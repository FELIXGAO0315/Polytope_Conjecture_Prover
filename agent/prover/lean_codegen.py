"""Pure Lean-source utility functions.

Extracted from FormalizerAgent's @staticmethods so they can be tested in
isolation and so agent.py shrinks.  Nothing here touches ``self``; if you
need agent state, this is the wrong module.
"""
from __future__ import annotations

import hashlib
import re

from agent.prover.prompts.lean_generation import LEAN_PREAMBLE


# ---------------------------------------------------------------------------
# Declaration manipulation
# ---------------------------------------------------------------------------

_LAST_DECL_RE = re.compile(
    r"^(?:private\s+)?(?:lemma|theorem|def|abbrev)\s+(\w+)",
    re.MULTILINE,
)


def rename_last_decl(code: str, expected_name: str) -> str:
    """If the last top-level declaration in *code* is not named *expected_name*,
    rename it. Also marks the declaration ``private`` to avoid polluting the
    global namespace.

    Only the declaration identifier itself is renamed; any docstring, helper
    lemmas, or references inside the proof body are left untouched (renaming
    references would require full parsing and is out of scope — the
    declaration name is what Lean exports).
    """
    matches = list(_LAST_DECL_RE.finditer(code))
    if not matches:
        return code
    last = matches[-1]
    actual_name = last.group(1)
    if actual_name == expected_name:
        return code
    start, end = last.span(1)
    new_code = code[:start] + expected_name + code[end:]
    full_span_start, full_span_end = last.span(0)
    full_decl = code[full_span_start:full_span_end]
    if not full_decl.strip().startswith("private"):
        new_code = new_code[:full_span_start] + "private " + new_code[full_span_start:]
    return new_code


def strip_named_declaration(code: str, name: str) -> str:
    """Remove the definition of ``name`` from ``code``.

    Handles lemma/theorem/def/abbrev declarations spanning multiple lines by
    finding the next top-level declaration after ``name``'s header and
    deleting everything in between. Preserves all other content unchanged.
    """
    lines = code.splitlines()
    start_re = re.compile(
        r"^(?:private\s+)?(?:lemma|theorem|def|abbrev)\s+" + re.escape(name) + r"\b"
    )
    next_decl_re = re.compile(
        r"^(?:private\s+)?(?:lemma|theorem|def|abbrev|structure|namespace|end|section|#)\s"
    )
    start_line = None
    for i, line in enumerate(lines):
        if start_re.match(line.strip()):
            start_line = i
            break
    if start_line is None:
        return code

    end_line = len(lines)
    for i in range(start_line + 1, len(lines)):
        stripped = lines[i].strip()
        if stripped and next_decl_re.match(stripped):
            end_line = i
            break

    doc_start = start_line
    for i in range(start_line - 1, -1, -1):
        stripped = lines[i].strip()
        if stripped.startswith("/--") or stripped.startswith("--") or not stripped:
            doc_start = i
        else:
            break

    kept = lines[:doc_start] + lines[end_line:]
    return "\n".join(kept)


# ---------------------------------------------------------------------------
# LLM response cleanup
# ---------------------------------------------------------------------------

def strip_markdown(text: str) -> str:
    """Extract Lean code from LLM response, stripping markdown fences and prose."""
    for pattern in (r"```lean\s*\n(.*?)```", r"```\s*\n(.*?)```"):
        m = re.search(pattern, text, re.DOTALL)
        if m:
            return m.group(1).strip()
    stripped = text.strip()
    if stripped.startswith("import Mathlib"):
        return stripped
    return ""


def strip_inline_shared_struct(code: str) -> str:
    """Remove any inlined SimplyCon3ConnectedMap structure definition.

    Uses line-by-line scanning to correctly handle the case where a comment
    contains 'end SimplyCon3ConnectedMap'.
    """
    lines = code.splitlines()
    result: list[str] = []
    depth = 0
    inside = False

    for line in lines:
        stripped = line.strip()
        if not inside:
            if (stripped.startswith("structure SimplyCon3ConnectedMap") or
                    stripped.startswith("namespace SimplyCon3ConnectedMap")):
                inside = True
                depth = 1
                continue
            result.append(line)
        else:
            if not stripped.startswith("--"):
                if stripped == "end SimplyCon3ConnectedMap":
                    depth -= 1
                    if depth == 0:
                        inside = False
                    continue
            result.append(line)

    return "\n".join(result)


def normalize_lean(code: str) -> str:
    """Post-process LLM-generated Lean code to fix common version-dependent
    issues:

    1. Collapse ``import Mathlib.X.Y`` → ``import Mathlib`` (umbrella only).
    2. Fix ``∑ x in s`` → ``∑ x ∈ s`` (Lean 4 Mathlib requires ∈).
    3. Remove ``axiom`` declarations (not allowed in polib).
    4. Remove any inlined SimplyCon3ConnectedMap definition.
    """
    code = re.sub(r"^import Mathlib\.\S+", "import Mathlib", code, flags=re.MULTILINE)
    lines = code.splitlines()
    seen_mathlib = False
    result = []
    for line in lines:
        if line.strip() == "import Mathlib":
            if not seen_mathlib:
                result.append(line)
                seen_mathlib = True
        else:
            result.append(line)
    code = "\n".join(result)
    code = re.sub(r"(∑[^∈\n,]*?)\s+\bin\b\s+", r"\1 ∈ ", code)
    code = re.sub(r"^axiom\s+[^\n]*\n?", "", code, flags=re.MULTILINE)
    code = strip_inline_shared_struct(code)
    return code


def ensure_preamble(code: str) -> str:
    """Guarantee that ``import Mathlib`` + ``import Inventory.Shared`` are at the top.

    Empty input returns the default preamble.  Otherwise stale import lines
    are stripped and the canonical two-line header is prepended.  Also strips
    any inline SimplyCon3ConnectedMap definition (which lives in Shared now).
    """
    if not code.strip():
        return LEAN_PREAMBLE
    code = strip_inline_shared_struct(code)
    if "import Inventory.Shared" in code:
        return code
    code = re.sub(r"^import Mathlib[^\n]*\n?", "", code, flags=re.MULTILINE)
    code = re.sub(r"^import Inventory\.Basic[^\n]*\n?", "", code, flags=re.MULTILINE)
    return LEAN_PREAMBLE + "\n" + code.lstrip()


# ---------------------------------------------------------------------------
# Sorry detection
# ---------------------------------------------------------------------------

_SORRY_RE = re.compile(r"\bsorry\b")


def has_sorry(code: str) -> bool:
    """Return True if code contains any sorry tactic (not in comments)."""
    for line in code.splitlines():
        if line.strip().startswith("--"):
            continue
        if _SORRY_RE.search(line):
            return True
    return False


def find_sorry_blocks(code: str) -> list[dict]:
    """Return a list of sorry blocks, each as ``{start, end, desc}``.

    Detects both ``exact sorry`` and bare ``sorry`` tactic lines.  Skips
    comment lines.  Each block includes preceding ``-- [SORRY]`` annotations.
    """
    lines = code.splitlines()
    blocks: list[dict] = []
    for i, line in enumerate(lines):
        if line.strip().startswith("--"):
            continue
        if not _SORRY_RE.search(line):
            continue
        start = i
        j = i - 1
        while j >= 0 and lines[j].strip().startswith("-- [SORRY]"):
            start = j
            j -= 1
        blocks.append({
            "start": start,
            "end": i,
            "desc": "\n".join(lines[start: i + 1]),
        })
    return blocks


def substitute_tactic_at_line(
    lean_code: str, line_num: int, tactic_pattern: str, replacement: str,
) -> str | None:
    """Surgical replacement: find ``tactic_pattern`` (with optional ``[..]``
    args or ``only [..]``) on line ``line_num`` (1-indexed) and swap it for
    ``replacement``. Returns the new code or ``None`` if the pattern doesn't hit.

    Preserves indentation and any preceding ``by`` / ``· `` / ``;`` syntax.
    Only touches ONE occurrence on the target line — avoids breaking other
    uses of the same tactic elsewhere in the file.
    """
    lines = lean_code.splitlines(keepends=True)
    if not (1 <= line_num <= len(lines)):
        return None
    target = lines[line_num - 1]
    pattern = (
        rf"\b{re.escape(tactic_pattern)}\b"
        r"(\s+only)?"
        r"(\s*\[[^\]]*\])?"
    )
    new_target, n_sub = re.subn(pattern, replacement, target, count=1)
    if n_sub == 0 or new_target == target:
        return None
    lines[line_num - 1] = new_target
    return "".join(lines)


# ---------------------------------------------------------------------------
# Error formatting + hashing
# ---------------------------------------------------------------------------

def format_errors_for_prompt(errors: list, max_chars: int = 3000) -> str:
    """Format up to the first 2 structured LeanErrors for a fix prompt.

    Uses parsed fields (line, column, error_class, raw_message, lean_excerpt)
    instead of truncating raw stderr, which can bury the real error in build
    noise.
    """
    if not errors:
        return "build failed (no structured errors parsed)"
    parts = []
    for e in errors[:2]:
        header = f"Line {e.line}:{e.column} [class {e.error_class}]: {e.raw_message}"
        if e.lean_excerpt:
            parts.append(f"{header}\n  > {e.lean_excerpt}")
        else:
            parts.append(header)
    if len(errors) > 2:
        parts.append(f"... and {len(errors) - 2} more error(s)")
    return "\n".join(parts)[:max_chars]


def hash_primary_error(errors: list) -> str:
    """Return an 8-char MD5 of the primary error after normalising line/col
    numbers and quoted identifiers, so the same logical error hashes
    identically regardless of source position or which identifier the LLM
    hallucinated.
    """
    if not errors:
        return "no_error"
    e = errors[0]
    msg = e.raw_message
    msg = re.sub(r":\d+:\d+:", ":LINE:COL:", msg)
    msg = re.sub(r"[`']([^`']+)[`']", "IDENTIFIER", msg)
    return hashlib.md5(f"{e.error_class}:{msg}".encode()).hexdigest()[:8]


# ---------------------------------------------------------------------------
# Tokenisation for alias / hint ranking
# ---------------------------------------------------------------------------

def face_count_tokens(name: str) -> set[str]:
    """Extract face-count references like P3, P4, P5, P6 from a node_id.

    Used as a fuzzy-match discriminator: if planner's ``C104_P6HigherFacesBound``
    TF-IDF-matches ``C104_P3LowerBound`` (because the planner's description
    literally mentions the proved lemma name), the cosine score is high but
    they're SEMANTICALLY DIFFERENT — one bounds p_6, the other bounds p_3.
    Comparing the ``{P3, P4, ...}`` token sets catches this:
    ``{P6} ∩ {P3} = ∅`` → reject the false alias.  Returns empty set for
    structural names like "Equality" or "Combine" (no face-count tokens) —
    those cases skip this check.
    """
    tokens: set[str] = set()
    for piece in name.split("_"):
        m = re.match(r"P(\d{1,2})(?=[A-Z]|$)", piece)
        if m and 3 <= int(m.group(1)) <= 12:
            tokens.add(f"P{m.group(1)}")
    return tokens


def tokenize_for_hint_ranking(text: str) -> set[str]:
    """Split a Lean-y identifier-rich string into lowercase tokens for
    overlap-based similarity.  Handles CamelCase, snake_case, and dotted
    Mathlib names: ``Finset.sum_Ico_consecutive`` →
    ``{finset, sum, ico, consecutive}``.
    """
    chunks: list[str] = []
    for piece in re.split(r"[.\s_]+", text):
        if not piece:
            continue
        chunks.extend(re.findall(r"[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z]+|[A-Z]+|\d+", piece))
    return {c.lower() for c in chunks if len(c) > 1}
