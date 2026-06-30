"""Module-level helpers used by FormalizerAgent and ConjectureDecomposer.

* ``_extract_lean_signatures(polib_lean)`` — scan a Polib.lean file and
  return ``{node_id: signature_text}`` for every saved entry, capped at
  200 chars per signature.
* ``_camel_tokens(s)`` — split CamelCase/snake_case names into lowercase tokens.
* ``_rank_lemmas_for_discovery(...)`` — score Polib entries for inclusion in
  the conjecture-discovery planner prompt (proved > partial, name overlap
  with the conjecture\'s tokens).
* ``_build_conjecture_json(parsed, lean_signature)`` — render the structured
  JSON conjecture block embedded in the discovery prompt.
"""
from __future__ import annotations

import json
import re
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from agent.prover.tools.latex_parser import ParsedTheorem


_SIG_DECL_START = re.compile(
    r"^(?:private\s+)?(?:lemma|theorem|def|abbrev)\s+(\w+)",
    re.MULTILINE,
)


def _extract_lean_signatures(polib_lean: Path) -> dict[str, str]:
    """Return {node_id: signature_text} by scanning Polib.lean.

    Extracts only the type signature (the part before ':= by' or ':='),
    capped at 200 chars so the prompt stays readable.
    """
    try:
        text = polib_lean.read_text(encoding="utf-8")
    except OSError:
        return {}
    sigs: dict[str, str] = {}
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        m = _SIG_DECL_START.match(lines[i])
        if m:
            name = m.group(1)
            collected: list[str] = []
            done = False
            for j in range(i, min(i + 6, len(lines))):
                line = lines[j]
                # Check for ':= by' first (proof tactic block)
                if ":= by" in line:
                    collected.append(line.split(":= by")[0])
                    done = True
                    break
                # Check for ':=' with something after it on the same line (inline body)
                if re.search(r":=\s*\S", line):
                    collected.append(re.split(r":=\s*\S", line)[0] + ":=")
                    done = True
                    break
                collected.append(line)
                # ':=' at end of line means body is on the next line — stop here
                if re.search(r":=\s*$", line):
                    done = True
                    break
            sigs[name] = " ".join(collected).strip()[:200]
            _ = done  # just consumed
        i += 1
    return sigs

def _camel_tokens(s: str) -> set[str]:
    """Split a CamelCase/underscore identifier into lowercase word tokens."""
    return {w.lower() for w in re.findall(r"[A-Z][a-z]+|[a-z]+|[0-9]+", s)}

def _rank_lemmas_for_discovery(
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
      1. `lean_signature` — authoritative, parser-validated.
      2. `coefficients` — extracted by AdvancedConjectureParser; lets the LLM
         cross-check arithmetic without re-deriving from raw text.
      3. `raw_formula` — verbatim DSL string, for context only.

    Why this exists: the prior prompt fed `Hypotheses: …\nConclusion: …` as
    free-form text alongside the lean_signature. When the two views disagreed
    in shape (e.g. lean said `Σ + 2*p₆ ≥ 4`, conclusion said
    `p_6 ≥ -0.5*sum + 2`), the planner sometimes synthesised a `latex_fragment`
    with swapped coefficients (`p_6 + 2·Σ ≥ 4`) and proceeded to decompose a
    mathematically false sub-lemma. Funnelling everything through one JSON
    block with an explicit "trust lean_signature" instruction removes that
    ambiguity.
    """
    payload: dict = {
        "lean_signature": lean_signature,
        "hypotheses": list(parsed.hypotheses),
        "conclusion_raw": parsed.conclusion,
    }
    try:
        from agent.conjectures import AdvancedConjectureParser
        formula = (
            f"if ({' and '.join(parsed.hypotheses)}), then {parsed.conclusion}"
        )
        cf = AdvancedConjectureParser().parse_formula_with_coefficients(formula)
        rhs_const = float(cf.coefficients.get("const", 0.0))
        rhs_terms = {
            k: float(v) for k, v in cf.coefficients.items() if k != "const"
        }
        payload["raw_formula"] = cf.raw_formula
        payload["conclusion"] = {
            "lhs": "p_6",
            "relation": cf.relation,
            "rhs_constant": rhs_const,
            "rhs_coefficients": rhs_terms,
        }
    except Exception:
        # Non-IRIS conjecture or unparseable RHS — drop the structured block;
        # lean_signature + raw conclusion are still present in payload.
        pass
    return json.dumps(payload, indent=2, ensure_ascii=False)
