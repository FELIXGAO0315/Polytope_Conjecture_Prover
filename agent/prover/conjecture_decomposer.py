"""Discovery-mode blueprint decomposer for conjecture proving.

Drives the planner LLM with a prompt tuned for \"there's no known proof yet —
please find one\".  Reads Polib for proved lemmas to advertise, ranks the most
relevant for the planner prompt, and embeds the conjecture as structured JSON
so the planner can't accidentally swap coefficients.

Public API:
  * ``ConjectureDecomposer.decompose(parsed, locked, proved_lemmas, log=...)``

The retry loop runs up to 3 attempts.  Each attempt:
  1. Send the prompt (always single-turn — we recompute the correction
     hint each round rather than carrying conversation history).
  2. Parse JSON → schema check → plantri-pool refutation check.
  3. If all pass → topo-sort and return the Blueprint.
  4. Otherwise → format the rejection as a correction message for the next
     attempt's prompt.
"""
from __future__ import annotations

import json
import re
import time
from pathlib import Path
from typing import Callable, TYPE_CHECKING

from agent.exceptions import BlueprintError
from agent.prover.tools.blueprint import (
    Blueprint,
    BlueprintNode,
    _parse_blueprint_json,
    _topological_sort,
    _validate_blueprint_nodes,
)
from agent.prover.tools.blueprint_validator import BlueprintValidator

if TYPE_CHECKING:
    from agent.prover.tools.goal_lock import LockedGoal
    from agent.prover.tools.parsed_theorem import ParsedTheorem


# ---------------------------------------------------------------------------
# Planner prompt
# ---------------------------------------------------------------------------

DISCOVERY_BLUEPRINT_PROMPT = """\
You are a Lean 4 proof discovery expert working in the domain of combinatorial
polytope theory. Your task is to devise a proof strategy for the following
UNPROVEN conjecture and express it as a directed acyclic graph (DAG) of
blueprint nodes. There is no known proof — you must figure out how to prove
it from first principles using Lean 4 / Mathlib tactics and the Inventory lemmas
listed below.

Conjecture name: {theorem_name}

## Conjecture statement (structured JSON — AUTHORITATIVE)
The block below is the canonical machine-parsed form of the conjecture.
**Trust `lean_signature` over every other representation.** The `raw_formula`
and `conclusion.coefficients` are provided as redundant cross-checks; if you
ever derive an algebraic claim, verify it against `lean_signature` by direct
substitution. NEVER swap, scale, or "simplify" the coefficients — copy them
exactly into any `latex_fragment` you emit.

```json
{conjecture_json}
```

## Domain context (simple 3-polytopes / maps on surfaces)
- Euler's formula for the sphere: v - e + f = 2
- Handshaking: 2e = sum_k k*p_k   (each face has k edges)
- Vertex-degree for simple polytopes: 2e = 3v
- p-vector constraint: sum_k p_k = f_2  (total face count)
- Dehn–Sommerville: sum_k (6-k)*p_k = 12  (for genus-0 simple maps)
- All p_k >= 0; only finitely many p_k are nonzero (captured by maps.m)
- The Lean structure is SimplyCon3ConnectedMap 0 (genus 0 = sphere for ALL IRIS
  conjectures). Fields: maps.p_i k (face counts), maps.v, maps.e, maps.m.
  NEVER use maps.f2 or maps.f_2 — those fields do not exist.
  f_2 (total face count) = ∑ k in Finset.Ico 3 (maps.m + 1), maps.p_i k.
  Do NOT add IsSimple, maps.simple, or any simplicity hypothesis — it is not defined.

## Polib lemmas (available via `import Inventory` / `import Polib`)
The block below lists already-proved (or partially-proved) lemmas you MAY
choose to reuse. Treat it as a reference catalogue: invoke a lemma only when
its conclusion clearly applies; otherwise plan a fresh sub-proof.
{available_lemmas}

For any node whose proof can call one of these lemmas directly, mention the
lemma by name in the `description` so the per-node prompt knows to surface
its signature.

## Node structure
- Each auxiliary definition or lemma needed before the main result gets its own node.
- **Parallelism**: only add a dependency edge A → B when B's proof body will
  DIRECTLY call or apply A by name. Avoid speculative edges — unnecessary
  dependencies force sequential execution.
- **Independence**: if two sub-lemmas don't use each other's results, leave
  them unconnected so they can run in parallel.
- Node types: "def" | "lemma" | "theorem".
- Exactly ONE node must have "is_main_target": true.
- "latex_fragment": a brief mathematical description of what this node states.
- "lean_signature": **MANDATORY for every non-main-target node**.  Provide the
  EXACT Lean 4 header the prover should prove, including the declaration keyword
  (`theorem` / `lemma` / `private lemma` / `def`), the node id as the
  declaration name, all binders (typically `(maps : SimplyCon3ConnectedMap 0)
  (hM : IsMap maps)` plus any hypothesis binders), the return type, and the
  terminating ` := by` token.  The declared name MUST be the node's `node_id`.
  Use the SAME genus as the parent theorem (`SimplyCon3ConnectedMap 0`) and
  reuse the parent's hypothesis variable names (`maps`, `hM`, `h_p4`, `h_p5`,
  `h_f2`, …).

  ⚠ **CRITICAL — Lean 4 SUM notation**: use the Unicode `∈` (element-of),
  NEVER the keyword `in`.  Lean 4 with current Mathlib rejects `∑ k in ...`
  with `unexpected token 'in'; expected ','`.  The correct form is:

     ✅ CORRECT:  `∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k`
     ❌ WRONG:    `∑ k in Finset.Ico 3 (maps.m + 1), maps.p_i k`

  Same rule for `∏`, `⋃`, `⋂`, and any other Mathlib big-operator binder.

  Correct example (note `∈` in both sum expressions):

      "lean_signature": "private lemma C104_FaceCountEquation (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h_f2 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 7) : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k = maps.v - maps.e + 2 := by"

  • For the main-target node ONLY, leave "lean_signature" as null / omit it —
    the system uses the conjecture's locked goal signature directly.

## CRITICAL — Node naming
All nodes live in a shared Inventory namespace. You MUST prefix every new node
you define with the exact conjecture identifier: `{theorem_name}`.

  REQUIRED prefix: `{theorem_name}`
  BAD:   "InequalityBound"        ← no prefix, will collide
  BAD:   "P6InequalityBound"      ← wrong conjecture prefix
  GOOD:  "{theorem_name}InequalityBound"  ← correct

Exception: nodes that intentionally REUSE an existing Inventory lemma listed above
must use that lemma's exact name unchanged.

## CRITICAL — Dependency rules
Add A as a dependency of B ONLY IF B's proof directly calls/applies A's result
or B's type mentions a type defined in A. When in doubt, omit the dependency.

## CRITICAL — Cross-theorem dependencies are FORBIDDEN
Dependencies must only reference node_ids defined WITHIN THIS blueprint.
Do NOT list a node_id from another theorem's blueprint (e.g. "C2_DehnSommerville"
for a C4 blueprint) — those lemmas are already available via `import Inventory` and
must NOT appear as dependency entries. If you need a proved Inventory lemma, just
reference it by name in the `description` field; leave `dependencies` empty for that edge.

Respond with ONLY valid JSON — no prose, no markdown fences.

{{
  "nodes": [
    {{
      "node_id": "CamelCaseUniqueId",
      "node_type": "def" | "lemma" | "theorem",
      "description": "One sentence: what this node proves or defines.",
      "latex_fragment": "Brief mathematical description of the sub-goal.",
      "lean_signature": "private lemma CamelCaseUniqueId (maps : SimplyCon3ConnectedMap 0) ... : ... := by",
      "dependencies": ["only_direct_deps_here"],
      "is_main_target": false
    }}
  ]
}}
"""


# ---------------------------------------------------------------------------
# Lemma ranking + Polib signature scrape (formerly in _helpers.py)
# ---------------------------------------------------------------------------

# Stop-word set used to filter low-signal tokens out of the keyword overlap
# score in _rank_lemmas.
_RANK_STOP = frozenset(
    {"maps", "the", "a", "an", "and", "or", "in", "of", "for", "is", "to",
     "with", "all", "let", "if", "then", "be", "by", "on", "at", "from"}
)

_SIG_DECL_START = re.compile(
    r"^(?:private\s+)?(?:lemma|theorem|def|abbrev)\s+(\w+)",
    re.MULTILINE,
)


def _extract_lean_signatures(polib_lean: Path) -> dict[str, str]:
    """Return ``{node_id: signature_text}`` by scanning Polib.lean.

    Extracts only the type signature (the part before ``:= by`` or ``:=``),
    capped at 200 chars so the prompt stays readable.
    """
    try:
        text = polib_lean.read_text(encoding="utf-8")
    except OSError:
        return {}
    sigs: dict[str, str] = {}
    lines = text.splitlines()
    for i in range(len(lines)):
        m = _SIG_DECL_START.match(lines[i])
        if not m:
            continue
        name = m.group(1)
        collected: list[str] = []
        for j in range(i, min(i + 6, len(lines))):
            line = lines[j]
            if ":= by" in line:
                collected.append(line.split(":= by")[0])
                break
            if re.search(r":=\s*\S", line):
                collected.append(re.split(r":=\s*\S", line)[0] + ":=")
                break
            collected.append(line)
            if re.search(r":=\s*$", line):
                break
        sigs[name] = " ".join(collected).strip()[:200]
    return sigs


def _camel_tokens(s: str) -> set[str]:
    """Split a CamelCase/underscore identifier into lowercase word tokens."""
    return {w.lower() for w in re.findall(r"[A-Z][a-z]+|[a-z]+|[0-9]+", s)}


def _rank_lemmas(
    proved_lemmas: list[dict],
    theorem_name: str,
    hypotheses: list[str],
    conclusion: str,
    top_k: int = 12,
) -> tuple[list[dict], list[dict]]:
    """Return (top_k_relevant, rest) sorted by token overlap with the conjecture."""
    if not proved_lemmas:
        return [], []
    context_tokens = (
        _camel_tokens(theorem_name)
        | {w for w in re.findall(r"\w+", " ".join(hypotheses).lower())}
        | {w for w in re.findall(r"\w+", conclusion.lower())}
    ) - _RANK_STOP

    def _score(e: dict) -> int:
        text = f"{e.get('node_id', '')} {e.get('description', '')}"
        tokens = _camel_tokens(text) | {w for w in re.findall(r"\w+", text.lower())}
        return len(tokens & context_tokens)

    ranked = sorted(proved_lemmas, key=_score, reverse=True)
    return ranked[:top_k], ranked[top_k:]


def _build_conjecture_json(parsed: "ParsedTheorem", lean_signature: str) -> str:
    """Render a structured JSON view of the conjecture for the planner prompt.

    Sources, in priority order:
      1. ``lean_signature`` — authoritative, parser-validated.
      2. ``coefficients`` — extracted by AdvancedConjectureParser; lets the LLM
         cross-check arithmetic without re-deriving from raw text.
      3. ``raw_formula`` — verbatim DSL string, for context only.

    Why this exists: when only `Hypotheses: …\\nConclusion: …` was passed as
    free-form text alongside the lean_signature, the planner sometimes synthesised
    a `latex_fragment` with swapped coefficients (e.g. `p_6 + 2·Σ ≥ 4` instead
    of `Σ + 2·p_6 ≥ 4`) and decomposed a mathematically false sub-lemma.
    Funnelling everything through one JSON block with an explicit "trust
    lean_signature" instruction removes that ambiguity.
    """
    payload: dict = {
        "lean_signature": lean_signature,
        "hypotheses": list(parsed.hypotheses),
        "conclusion_raw": parsed.conclusion,
    }
    try:
        from agent.conjectures import AdvancedConjectureParser
        formula = f"if ({' and '.join(parsed.hypotheses)}), then {parsed.conclusion}"
        cf = AdvancedConjectureParser().parse_formula_with_coefficients(formula)
        payload["raw_formula"] = cf.raw_formula
        payload["conclusion"] = {
            "lhs": "p_6",
            "relation": cf.relation,
            "rhs_constant": float(cf.coefficients.get("const", 0.0)),
            "rhs_coefficients": {
                k: float(v) for k, v in cf.coefficients.items() if k != "const"
            },
        }
    except Exception:
        # Non-IRIS conjecture or unparseable RHS — drop the structured block;
        # lean_signature + raw conclusion are still present in payload.
        pass
    return json.dumps(payload, indent=2, ensure_ascii=False)


# ---------------------------------------------------------------------------
# ConjectureDecomposer
# ---------------------------------------------------------------------------

class ConjectureDecomposer:
    """Discovery-mode blueprint decomposer for unproven JSON conjectures.

    Wraps the LLM call in a 3-attempt retry-with-correction loop guarded by
    `BlueprintValidator`: when an intermediate node's `latex_fragment` is
    refuted by a realizable plantri-pool polytope satisfying the conjecture's
    hypotheses, the concrete counter-example is fed back to the planner and
    it is asked to re-decompose. Catches the false-sub-lemma class of bugs
    (e.g. C104_P6HigherFacesBound: p_6 + 5·Σ ≥ 10 was refuted by the
    truncated tetrahedron) BEFORE downstream proof attempts waste budget.
    """

    # Default plantri pool used by the post-decompose sanity check.
    # If the path doesn't exist (running tests without harvest output), the
    # validator silently no-ops — pure safety net, never blocks pipeline.
    _DEFAULT_PLANTRI_POOL = (
        Path(__file__).resolve().parents[2]
        / "output" / "conjecture_generator" / "plantri_pool.json"
    )

    def __init__(
        self,
        client,
        model: str,
        polib_lean: Path | None = None,
        plantri_pool_path: Path | None = None,
    ) -> None:
        self._client = client
        self._model = model
        self._polib_lean = polib_lean
        self._validator = BlueprintValidator(
            plantri_pool_path or self._DEFAULT_PLANTRI_POOL
        )

    def decompose(
        self,
        parsed: "ParsedTheorem",
        locked: "LockedGoal",
        proved_lemmas: list[dict] | None = None,
        max_attempts: int = 3,
        log: Callable[[str], None] | None = None,
    ) -> Blueprint:
        _log = log or (lambda _msg: None)

        available_block = self._render_available_lemmas(
            proved_lemmas or [], parsed,
        )
        conjecture_json = _build_conjecture_json(parsed, locked.lean_signature)
        base_prompt = DISCOVERY_BLUEPRINT_PROMPT.format(
            theorem_name=parsed.name,
            conjecture_json=conjecture_json,
            available_lemmas=available_block,
        )

        correction = ""   # appended to the next attempt's prompt
        last_exc: BlueprintError | None = None
        for attempt in range(1, max_attempts + 1):
            response = self._client.messages.create(
                model=self._model,
                # 1024 is enough for a 5-10-node blueprint (~150 chars/node
                # in the JSON schema).  2048 doubled the worst-case streaming
                # latency over VPN without any quality benefit observed.
                max_tokens=1024,
                messages=[{"role": "user", "content": base_prompt + correction}],
                # JSON-schema task — no need for extended thinking.  `low`
                # cuts wallclock 3-5x vs the schedule default of "medium".
                effort="low",
                # No tools — the prompt already embeds the full Inventory
                # API surface and the conjecture JSON.  Letting the LLM
                # grep/read tempts 30-120s detours (especially over WSL+VPN).
                allowed_tools=[],
            )
            text = response.content[0].text.strip()
            try:
                nodes = _parse_blueprint_json(text)
                _validate_blueprint_nodes(nodes)
                refutation = self._validator.check(nodes, parsed.hypotheses)
                if refutation is not None:
                    raise BlueprintError(refutation.message())
            except BlueprintError as exc:
                last_exc = exc
                err_class = _classify_blueprint_error(str(exc))
                _log(f"      [planner-attempt] REJECTED ({err_class}): {str(exc)[:200]}")
                correction = _format_correction(exc)
                continue
            return Blueprint(nodes=nodes, topo_order=_topological_sort(nodes))

        _log(f"      [planner] all {max_attempts} attempts failed — "
             f"last error: {str(last_exc)[:200]}")
        assert last_exc is not None  # loop ran at least once
        raise last_exc

    # ------------------------------------------------------------------
    # Available-lemmas block rendering
    # ------------------------------------------------------------------

    def _render_available_lemmas(
        self, proved_lemmas: list[dict], parsed: "ParsedTheorem",
    ) -> str:
        if not proved_lemmas:
            return "  (none yet)"
        sigs: dict[str, str] = (
            _extract_lean_signatures(self._polib_lean)
            if self._polib_lean is not None else {}
        )
        top, rest = _rank_lemmas(
            proved_lemmas,
            theorem_name=parsed.name,
            hypotheses=list(parsed.hypotheses),
            conclusion=parsed.conclusion,
        )
        lines: list[str] = []
        for e in top:
            line = f"  - `{e['node_id']}`"
            if e.get("description"):
                line += f": {e['description']}"
            sig = sigs.get(e["node_id"], "")
            if sig:
                line += f"\n    Lean: `{sig}`"
            lines.append(line)
        if rest:
            rest_ids = ", ".join(f"`{e['node_id']}`" for e in rest)
            lines.append(f"  Also available (name only): {rest_ids}")
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# Correction-message helpers
# ---------------------------------------------------------------------------

def _classify_blueprint_error(err_msg: str) -> str:
    if "REFUTED" in err_msg:
        return "REFUTED"
    if "JSON" in err_msg:
        return "INVALID_JSON"
    return "SCHEMA"


def _format_correction(exc: BlueprintError) -> str:
    err_msg = str(exc)
    if "REFUTED" in err_msg:
        return (
            "\n\n" + err_msg + "\n\n"
            "Re-emit the blueprint with a corrected decomposition. "
            "The refuted intermediate is mathematically false and must be "
            "replaced — do not keep it. Output ONLY the JSON object."
        )
    return (
        "\n\nYour previous response was not valid JSON matching the required "
        "schema. Respond with ONLY the JSON object — no prose, no markdown, "
        "no comments. Start your response with '{' and end with '}'."
    )
