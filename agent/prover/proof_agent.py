"""Single-session prover — the live core of Stage 4.

Replaces the legacy ``_partial_solver`` / ``_compile_loop`` / ``_targeted_fix*``
machinery with ONE multi-turn LLM session that owns the proof and uses the
Lean compiler as a ground-truth MCP tool.

Contract (matches the user's hard rule):
    * ``polib/Inventory.lean`` is the closed axiom base.  Lemmas inside it
      are accepted as true even when they contain ``sorry``.
    * Any NEW lemma the prover writes (i.e. anything outside Inventory)
      MUST be sorry-free.  A response with a remaining sorry is rejected.

The LLM workflow:
    1. Reads the locked signature from the user prompt.
    2. Already sees every Inventory + proven-dep API surface in the prompt
       — no Grep needed for basic facts.
    3. Drafts a Lean file.
    4. Calls ``lean_compile(code)`` — the ground-truth compiler.
    5. Iterates compile→error→fix→compile until clean.
    6. Emits the final file inside ``<final>```lean ... ```</final>``.

The Python layer only wires the MCP tool, runs the SDK conversation, and
re-compiles the final block as a soundness check (the emitted file could
differ from the last one passed to the tool).
"""
from __future__ import annotations

import asyncio
import os
import re
import time
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING

from claude_agent_sdk import (
    AssistantMessage,
    ClaudeAgentOptions,
    ResultMessage,
    TextBlock,
    ToolUseBlock,
    create_sdk_mcp_server,
    query,
    tool,
)

if TYPE_CHECKING:
    from agent.prover.tools.blueprint import BlueprintNode
    from agent.prover.tools.goal_lock import LockedGoal
    from agent.prover.tools.lean_compiler import LeanCompiler


# ---------------------------------------------------------------------------
# Regexes
# ---------------------------------------------------------------------------

_FINAL_FENCE_RE = re.compile(
    r"<final>\s*```lean\s*(.*?)```\s*</final>", re.DOTALL | re.IGNORECASE,
)
_FINAL_BARE_RE = re.compile(
    r"<final>\s*(.*?)\s*</final>", re.DOTALL | re.IGNORECASE,
)
_SORRY_RE = re.compile(r"(?<!\w)sorry(?!\w)")
_THEOREM_OR_LEMMA_RE = re.compile(r"\b(theorem|lemma)\b")

_INV_DECL_RE = re.compile(
    r"^(?:private\s+|noncomputable\s+)*(structure|opaque|theorem|lemma|def|axiom)\s+(\w+)",
)
_NAMESPACE_OPEN_RE = re.compile(r"^\s*namespace\s+(\S+)\s*$")
_NAMESPACE_CLOSE_RE = re.compile(r"^\s*end\s+(\S+)\s*$")


def _has_sorry(code: str) -> bool:
    """True iff *code* contains a non-comment ``sorry``."""
    for line in code.splitlines():
        if line.lstrip().startswith("--"):
            continue
        if _SORRY_RE.search(line):
            return True
    return False


# ---------------------------------------------------------------------------
# Inventory API surface — pre-extracted so the LLM doesn't waste turns grepping
# ---------------------------------------------------------------------------

def _extract_inventory_signatures(inventory_path: Path) -> str:
    """Read Inventory.lean and return a compact block of its declarations,
    namespace-aware so the LLM sees method-style availability correctly.

    For each declaration line, capture the header up to (and including) the
    line that ends the type signature (``:= by``, ``:= sorry``, ``where``,
    bare ``:=``).  The line is then trimmed at ``:=`` so only the type
    remains.  When a declaration is inside a ``namespace`` block, the block
    boundaries are preserved in the output — without them, a ``def p_4
    (maps ...)`` looks like a top-level function and the LLM may invoke it
    as ``p_4 maps`` instead of ``maps.p_4``.
    """
    try:
        text = inventory_path.read_text(encoding="utf-8")
    except OSError:
        return "(could not read Inventory.lean)"
    lines = text.splitlines()

    out: list[str] = []
    namespace_stack: list[str] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        ns_open = _NAMESPACE_OPEN_RE.match(line)
        if ns_open:
            namespace_stack.append(ns_open.group(1))
            out.append(line.rstrip())
            i += 1
            continue
        ns_close = _NAMESPACE_CLOSE_RE.match(line)
        if ns_close and namespace_stack and namespace_stack[-1] == ns_close.group(1):
            namespace_stack.pop()
            out.append(line.rstrip())
            i += 1
            continue
        m = _INV_DECL_RE.match(line)
        if not m:
            i += 1
            continue
        # Collect the header lines up to the body marker.  Cap at 12 lines
        # to handle multi-line binder groups; if no body marker found, take
        # those 12 lines verbatim (rare but safe).
        block: list[str] = []
        end_i = i
        body_found = False
        for j in range(i, min(i + 12, len(lines))):
            block.append(lines[j])
            if (re.search(r":=\s*by\b", lines[j])
                    or re.search(r":=\s*sorry\b", lines[j])
                    or re.search(r"\swhere\s*$", lines[j])
                    or re.search(r":=\s*(?:\S|$)", lines[j])):
                end_i = j
                body_found = True
                break
        if not body_found:
            end_i = min(i + 11, len(lines) - 1)
        # Trim the last line's body (`:= ...` onward) so only the type remains.
        last = block[-1]
        last = re.sub(r"\s*:=.*$", "", last)
        last = re.sub(r"\s*where\s*$", "", last)
        block[-1] = last.rstrip()
        out.append("\n".join(block).rstrip())
        i = end_i + 1

    return "\n\n".join(out)


# ---------------------------------------------------------------------------
# Proven-dependency signatures — pulled from Polib.lean so the LLM sees
# every sub-lemma's exact API and doesn't have to grep for it.
# ---------------------------------------------------------------------------

def _extract_dep_signatures(polib_lean: Path, dep_ids: list[str]) -> list[tuple[str, str]]:
    """For each id in *dep_ids* present in Polib.lean, return
    ``(id, header_text)``.  Header is the declaration line(s) up to ``:= by``.
    """
    if not dep_ids:
        return []
    try:
        text = polib_lean.read_text(encoding="utf-8")
    except OSError:
        return []
    lines = text.splitlines()
    name_to_block: dict[str, str] = {}
    for i, line in enumerate(lines):
        m = _INV_DECL_RE.match(line)
        if not m:
            continue
        name = m.group(2)
        if name not in dep_ids or name in name_to_block:
            continue
        block: list[str] = []
        for j in range(i, min(i + 12, len(lines))):
            block.append(lines[j])
            if (re.search(r":=\s*by\b", lines[j])
                    or re.search(r":=\s*(?:\S|$)", lines[j])):
                break
        # Trim body off the last line.
        last = block[-1]
        last = re.sub(r"\s*:=.*$", "", last)
        block[-1] = last.rstrip()
        name_to_block[name] = "\n".join(block).rstrip()
    # Preserve caller's dep order in output.
    return [(d, name_to_block[d]) for d in dep_ids if d in name_to_block]


# ---------------------------------------------------------------------------
# Prompts
# ---------------------------------------------------------------------------

SYSTEM_PROMPT = """\
You are a Lean 4 expert proving a polytope-combinatorics theorem.

You have a hard time budget. **Every second you spend exploring without
calling `lean_compile` is wasted** — the compiler's error messages are
strictly more informative than more file reading. Move fast.

## Inventory contract — read carefully
`polib/Inventory.lean` is the project's CLOSED axiom base. Every lemma it
declares is accepted as true. Some lemmas inside Inventory contain `sorry`
— that is intentional and authorised by the project owners. You may
invoke ANY Inventory lemma freely. You may NOT modify Inventory.

The conjecture you are proving lives OUTSIDE Inventory. It must compile
with ZERO new `sorry`. A file containing any new sorry is REJECTED.

## Tools
  - `Read`, `Grep`, `Glob`  — read-only exploration.
      • `polib/Inventory.lean`                  — accepted axiom base
                                                  (sorries here are pre-approved).
      • `polib/Polib.lean`                      — previously-proved conjectures.
                                                  ⚠ May still contain sections
                                                  marked `-- === X (partial) ===`
                                                  from earlier policy regimes —
                                                  those bodies contain `sorry`
                                                  and MUST NOT be invoked from a
                                                  new proof (would transitively
                                                  pull sorry into our dependency
                                                  closure).  Only call sections
                                                  marked `(proved)`.
      • `polib/.lake/packages/mathlib/Mathlib/` — full Mathlib source.
  - `mcp__prover_tools__lean_compile(code)`   — compile a Lean 4 file.
      Returns `COMPILED SUCCESSFULLY (no sorry)` on success, or the
      compiler errors. THIS IS YOUR GROUND TRUTH.

## Required workflow (in this order — do NOT spend extra time on step 1)
1. **At most ONE quick Grep / Read on Inventory.lean** to verify a specific
   lemma signature *only if* the headers already shown in the user prompt
   are insufficient. Spend < 60 seconds on this.
2. **Immediately draft a first proof attempt and call `lean_compile`** —
   even if you think it might be wrong, even if it is just a one-line
   `linarith` call. The first compile is a probe: its error messages
   will tell you what the goal really expects.
3. **Iterate: compile → read error → refine → compile**. Each round
   takes ~30-60s of compile time. Plan to make 5-15 such rounds. Do not
   over-think between rounds — small surgical edits driven by the error.
4. When `lean_compile` returns success WITH no sorry remaining, emit:

       <final>
       ```lean
       <complete contents of the compiling file>
       ```
       </final>

   Anything outside `<final>...</final>` is ignored. Exactly one block,
   and the ```lean fence is MANDATORY — bare `<final>prose</final>` is
   rejected.

## Hard rules (the python layer enforces these)
- Locked signature is IMMUTABLE: same name, same bound variables, same
  hypotheses, same conclusion. Verbatim.
- No new `sorry`. No `axiom` declarations.
- No struct construction of `SimplyCon3ConnectedMap` (the `IsMap` token
  is opaque; you cannot fabricate it). The only sources of `IsMap` are
  the theorem's `hM` and the witnesses of `equality_family`.
- Helper definitions must be `private` and prefixed with the node id.
- Imports: exactly `import Mathlib`, `import Inventory`, and (only if
  you reference proved conjectures) `import Polib`. Never a specific
  Mathlib submodule.

## Naming convention
Both Inventory lemmas and your conjecture use the same parameter names —
`(maps : SimplyCon3ConnectedMap g) (hM : IsMap maps)`. Call Inventory
lemmas positionally: `euler_formula maps hM`, `handshake maps hM`, etc.

Note: definitions inside the `namespace SimplyCon3ConnectedMap` block
(e.g. `p_4`, `total_faces`) are method-style — write `maps.p_4`, not
`p_4 maps`. The Inventory API surface in the user prompt preserves
namespace boundaries so you can see which is which.
"""


def _build_user_message(
    node: "BlueprintNode",
    locked_goal: "LockedGoal",
    inventory_signatures: str,
    dep_signatures: list[tuple[str, str]],
    project_root: Path,
) -> str:
    desc = (node.description or "").strip()
    polib_dir = project_root / "polib"
    parts: list[str] = [
        "# Prove this Lean 4 theorem",
        "",
        f"**Node id**: `{node.node_id}`",
        f"**Type**: {node.node_type}",
    ]
    if desc:
        parts.append(f"**Description**: {desc}")
    parts.extend([
        "",
        "## Working directory",
        f"Your `cwd` is **`{project_root}`** (relative paths resolve from here).",
        "Files you may need to Grep/Read — use these EXACT paths, do NOT guess",
        "or substitute hyphens for underscores in the project name:",
        "",
        f"  • Inventory.lean  →  `{polib_dir / 'Inventory.lean'}`",
        f"  • Polib.lean      →  `{polib_dir / 'Polib.lean'}`",
        f"  • Mathlib root    →  `{polib_dir / '.lake' / 'packages' / 'mathlib' / 'Mathlib'}`",
        "",
        "Note: the full Inventory API surface is ALREADY printed below — you",
        "should NOT need to Read or Grep Inventory.lean for basic facts.",
        "",
        "## Locked Lean signature (prove this EXACTLY as written)",
        "```lean",
        locked_goal.lean_signature,
        "```",
        "",
        "## Inventory API surface (already imported via `import Inventory`)",
        "These are EVERY type and lemma you may invoke from Inventory.lean.",
        "Headers shown verbatim, namespace blocks preserved — items inside",
        "`namespace SimplyCon3ConnectedMap ... end SimplyCon3ConnectedMap`",
        "are method-style (`maps.p_4`), items outside it are positional.",
        "",
        "```lean",
        inventory_signatures,
        "```",
        "",
    ])
    if dep_signatures:
        parts.extend([
            "## Already-proved sub-lemmas in this blueprint (in `Polib.lean`)",
            "Call any of these by name — they are imported by `import Polib`.",
            "",
            "```lean",
            "\n\n".join(sig for _, sig in dep_signatures),
            "```",
            "",
        ])
    parts.extend([
        "## Your task",
        "1. Pick the Inventory / proven-dep lemma(s) that look like they apply.",
        "2. Draft a proof — even a one-line `linarith [Foo maps hM, Bar maps hM]`",
        "   is a valid first probe.",
        "3. Call `lean_compile` with that draft. Read the errors.",
        "4. Iterate compile→fix→compile. Do NOT detour back into Grep unless a",
        "   specific error message requires it.",
        "5. When `lean_compile` returns success, emit `<final>```lean ... ```</final>`.",
    ])
    return "\n".join(parts)


def _extract_final_code(text: str) -> str | None:
    """Pull the Lean code out of the LLM's ``<final>`` block.

    Strict path: ``<final>```lean ... ```</final>`` — return the fenced body.
    Bare fallback: ``<final>...</final>`` — accept ONLY if it looks like a
    Lean file (contains ``theorem`` or ``lemma``).  Bare prose is rejected
    so we don't waste a final-verify compile on the LLM's prose.
    """
    m = _FINAL_FENCE_RE.search(text)
    if m:
        return m.group(1).strip()
    m = _FINAL_BARE_RE.search(text)
    if m:
        body = m.group(1).strip()
        if body.startswith("```lean"):
            body = body[len("```lean"):].lstrip("\n")
        if body.endswith("```"):
            body = body[:-3].rstrip()
        body = body.strip()
        if _THEOREM_OR_LEMMA_RE.search(body):
            return body
    return None


# ---------------------------------------------------------------------------
# MCP tool — wrap LeanCompiler so the LLM can call it directly
# ---------------------------------------------------------------------------

def _make_lean_compile_tool(compiler: "LeanCompiler", node_id: str, log_fn):
    call_count = {"n": 0}

    @tool(
        "lean_compile",
        (
            "Compile a Lean 4 file in this project's lake environment. "
            "Returns success or a list of compiler errors. Call this iteratively "
            "while developing the proof — do not guess whether code compiles, "
            "ask the compiler. The file must include the standard imports "
            "(`import Mathlib`, `import Inventory`, optionally `import Polib`)."
        ),
        {"code": str},
    )
    async def lean_compile(args):
        call_count["n"] += 1
        n = call_count["n"]
        code = args.get("code", "")
        if not code.strip():
            return {"content": [{"type": "text", "text": "ERROR: empty code passed to lean_compile."}]}
        try:
            result = compiler.compile(code, f"{node_id}_session_{n}")
        except Exception as exc:
            log_fn(f"    [lean_compile #{n}] internal error: {exc}")
            return {"content": [{"type": "text", "text": f"INTERNAL ERROR: {exc}"}]}

        if result.success:
            if _has_sorry(code):
                return {"content": [{"type": "text", "text":
                    "COMPILED, BUT THE FILE STILL CONTAINS sorry. "
                    "The final answer will be rejected unless every sorry is removed."
                }]}
            return {"content": [{"type": "text", "text": "COMPILED SUCCESSFULLY (no sorry)."}]}

        # Cap to first 6 errors so the context doesn't bloat.
        err_lines: list[str] = []
        for k, err in enumerate(result.errors[:6], 1):
            msg = (err.raw_message or "").strip()
            if len(msg) > 600:
                msg = msg[:600] + " …"
            err_lines.append(f"[{k}] line {getattr(err, 'line', '?')}: {msg}")
        more = (f"\n... and {len(result.errors) - 6} more error(s)."
                if len(result.errors) > 6 else "")
        body = f"FAILED ({len(result.errors)} error(s)):\n" + "\n".join(err_lines) + more
        return {"content": [{"type": "text", "text": body}]}

    return lean_compile, call_count


# ---------------------------------------------------------------------------
# Public entry
# ---------------------------------------------------------------------------

@dataclass
class ProofAttempt:
    """Outcome of one ``prove_node`` call."""
    success: bool
    code: str
    reason: str
    tool_calls: int
    elapsed_seconds: float


def prove_node(
    node: "BlueprintNode",
    locked_goal: "LockedGoal",
    compiler: "LeanCompiler",
    project_root: Path,
    proven_dep_ids: list[str] | None = None,
    model: str = "claude-opus-4-7",
    effort: str = "high",
    max_turns: int = 80,
    timeout_seconds: int = 1500,
    log_fn=print,
) -> ProofAttempt:
    """Prove ``node`` in one LLM session.

    ``success=True`` ONLY when the LLM emitted a ``<final>`` block AND that
    block re-compiles cleanly AND contains no new sorry.  Anything else is
    a failure (the ``reason`` field carries the precise cause).
    """
    started_at = time.monotonic()
    polib_dir = project_root / "polib"
    inventory_path = polib_dir / "Inventory.lean"
    polib_lean_path = polib_dir / "Polib.lean"

    inventory_sigs = _extract_inventory_signatures(inventory_path)
    dep_sigs = _extract_dep_signatures(polib_lean_path, list(proven_dep_ids or []))
    user_msg = _build_user_message(node, locked_goal, inventory_sigs, dep_sigs, project_root)

    lean_tool, call_count = _make_lean_compile_tool(compiler, node.node_id, log_fn)
    mcp_server = create_sdk_mcp_server(
        name="prover_tools", version="1.0.0", tools=[lean_tool],
    )

    # Same env scrubbing as ClaudeSDKClient — blanks the session-attach markers
    # that otherwise make the bundled CLI try to re-join a dead VSCode session.
    env_overrides = {
        **os.environ,
        "CLAUDE_EFFORT": "", "CLAUDECODE": "",
        "CLAUDE_CODE_SESSION_ID": "", "CLAUDE_CODE_EXECPATH": "",
        "CLAUDE_CODE_ENABLE_SDK_FILE_CHECKPOINTING": "",
        "CLAUDE_CODE_SSE_PORT": "", "AI_AGENT": "",
    }
    options = ClaudeAgentOptions(
        model=model,
        max_turns=max_turns,
        allowed_tools=["Read", "Grep", "Glob", "mcp__prover_tools__lean_compile"],
        permission_mode="bypassPermissions",
        mcp_servers={"prover_tools": mcp_server},
        system_prompt=SYSTEM_PROMPT,
        cwd=str(project_root),
        effort=effort,
        env=env_overrides,
    )

    text_chunks: list[str] = []
    tool_uses: list[str] = []
    result_msg: ResultMessage | None = None

    async def _run() -> None:
        nonlocal result_msg
        gen = query(prompt=user_msg, options=options)
        try:
            async for msg in gen:
                if isinstance(msg, AssistantMessage):
                    for block in msg.content:
                        if isinstance(block, TextBlock):
                            text_chunks.append(block.text)
                        elif isinstance(block, ToolUseBlock):
                            tool_uses.append(block.name)
                elif isinstance(msg, ResultMessage):
                    result_msg = msg
        finally:
            try:
                await gen.aclose()
            except Exception:
                pass

    try:
        asyncio.run(asyncio.wait_for(_run(), timeout=timeout_seconds))
    except asyncio.TimeoutError:
        elapsed = time.monotonic() - started_at
        log_fn(f"  [proof-agent] {node.node_id}: session timed out after "
               f"{elapsed:.0f}s ({call_count['n']} lean_compile calls)")
        return ProofAttempt(False, "", f"session timed out after {timeout_seconds}s",
                            call_count["n"], elapsed)
    except Exception as exc:
        elapsed = time.monotonic() - started_at
        log_fn(f"  [proof-agent] {node.node_id}: session crashed: {exc}")
        return ProofAttempt(False, "", f"session crashed: {type(exc).__name__}: {exc}",
                            call_count["n"], elapsed)

    elapsed = time.monotonic() - started_at
    n_tool = call_count["n"]
    log_fn(
        f"  [proof-agent] {node.node_id}: session finished in {elapsed:.0f}s, "
        f"{n_tool} lean_compile call(s), "
        f"{sum(1 for t in tool_uses if 'Grep' in t)} grep, "
        f"{sum(1 for t in tool_uses if 'Read' in t)} read"
    )

    if result_msg is not None and result_msg.is_error:
        return ProofAttempt(False, "", f"SDK reported error: subtype={result_msg.subtype}",
                            n_tool, elapsed)

    code = _extract_final_code("".join(text_chunks))
    if code is None:
        log_fn(f"  [proof-agent] {node.node_id}: no usable <final> block in response")
        return ProofAttempt(False, "", "no usable <final>...</final> block in final response",
                            n_tool, elapsed)

    # Soundness re-check: compile what the LLM actually emitted (the emitted
    # file could differ from the last one passed to the tool).
    verify = compiler.compile(code, f"{node.node_id}_final_verify")
    if not verify.success:
        err = verify.errors[0].raw_message[:200] if verify.errors else "build failed"
        log_fn(f"  [proof-agent] {node.node_id}: final block did not re-compile: {err}")
        return ProofAttempt(False, code, f"final block does not compile: {err}",
                            n_tool, elapsed)

    if _has_sorry(code):
        log_fn(f"  [proof-agent] {node.node_id}: final block contains sorry (rejected)")
        return ProofAttempt(False, code, "final block contains new sorry",
                            n_tool, elapsed)

    log_fn(f"  [proof-agent] {node.node_id}: proved (sorry-free, compiles)")
    return ProofAttempt(True, code, "ok", n_tool, elapsed)
