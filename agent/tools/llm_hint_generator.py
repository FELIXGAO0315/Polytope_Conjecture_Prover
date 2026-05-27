from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from agent.tools.blueprint import BlueprintNode


@dataclass
class FailureRecord:
    """One round of failed compilation in the compile-fix loop."""
    round_num: int
    strategy: str          # e.g. "targeted_fix_parallel", "targeted_fix_decompose"
    error_classes: list[str]
    primary_error: str     # raw_message of the first error, truncated
    lean_excerpt: str      # the failing code fragment (first error's lean_excerpt)
    banned_ids: list[str] = field(default_factory=list)


class LLMHintGenerator:
    """
    Meta-prompting hint generator that analyses the history of failed proof
    attempts and suggests a strategically different approach.

    Unlike CombinedHintGenerator (lemma-name lookup) and
    LLMProofReasoningHintGenerator (single-node proof sketch), this tool:
      1. Receives the full sequence of failure records from the compile loop.
      2. Identifies recurring error patterns and exhausted strategies.
      3. Asks the LLM to reason about *why* those strategies failed and what
         fundamentally different approach to try next.
      4. Returns a short list of strategic hint strings injected into the next
         fix prompt.

    Inspired by the meta-prompting layer in ScaleAutoResearch-Ramsey, where
    one LLM instance steers the search strategy for another.
    """

    _SYSTEM = (
        "You are an expert Lean 4 proof strategist. "
        "Given a history of failed proof attempts, you identify the root cause "
        "and recommend a concrete, different strategy. Be concise and specific."
    )

    _PROMPT = """\
A Lean 4 proof node has stagnated after multiple failed compile rounds.
Your task: analyse the failure patterns and recommend a genuinely different strategy.

## Node to prove
Node ID      : {node_id}
Node type    : {node_type}
Description  : {description}
LaTeX        : {latex_fragment}

## Goal signature (do NOT change names or types)
```lean
{goal_signature}
```

## Failure history ({num_rounds} rounds)
{failure_summary}

## Banned identifiers (Lean rejected these — never use them)
{banned_ids}

## Domain axioms available (call WITHOUT dot-notation)
- `euler_formula maps`      : (v:ℤ) - e + Σ p_i k = 2 - 2*g
- `handshake maps`          : 2*e = Σ k * p_i k
- `regularity maps`         : 3*v = 2*e
- `kgon_occupation_bound`   : occupied.card ≤ k/2
- `quad_occ_reduction`      : occupied.card ≤ r/2 - 1 (when p₄ > 0)

## Instructions
Think step by step:
1. What error class dominates the history? (type mismatch / unknown id / unsolved goal / …)
2. Which strategies have already been exhausted?
3. What is the most likely ROOT CAUSE of the stagnation?
4. What ONE concrete change in proof approach would bypass the root cause?

Then output 2-4 strategic hints, each on its own line, starting with "- ".
Each hint must be actionable and specific to this node — not generic advice.
Examples of good hints:
- "Replace `linarith` with `omega` after casting all terms to ℤ via `push_cast`"
- "Introduce `have h := handshake maps` first, then use `linarith [h, regularity maps]`"
- "Rewrite goal using `Finset.sum_Ico_consecutive` split at k=6 before applying `linarith`"

Do NOT output prose before the hints. Output ONLY the bullet list.
"""

    def __init__(self, client: object, model: str | None = None) -> None:
        self._client = client
        self._model = model

    def generate(
        self,
        node: "BlueprintNode",
        goal_signature: str,
        failure_history: list[FailureRecord],
    ) -> list[str]:
        """Analyse failure_history and return strategic hint strings.

        Returns an empty list if the LLM call fails or produces nothing useful.
        """
        if not failure_history:
            return []

        failure_summary = self._format_history(failure_history)
        all_banned: list[str] = []
        for rec in failure_history:
            all_banned.extend(rec.banned_ids)
        banned_str = ", ".join(f"`{x}`" for x in dict.fromkeys(all_banned)) or "(none)"

        prompt = self._PROMPT.format(
            node_id=node.node_id,
            node_type=node.node_type,
            description=node.description,
            latex_fragment=(node.latex_fragment or "")[:400],
            goal_signature=goal_signature or "(not available)",
            num_rounds=len(failure_history),
            failure_summary=failure_summary,
            banned_ids=banned_str,
        )

        try:
            raw = self._client._call(prompt, model=self._model, system=self._SYSTEM, timeout=60)
        except Exception:
            return []

        return self._parse_hints(raw)

    # ------------------------------------------------------------------
    # Helpers
    # ------------------------------------------------------------------

    @staticmethod
    def _format_history(history: list[FailureRecord]) -> str:
        lines: list[str] = []
        for rec in history:
            classes = ", ".join(rec.error_classes) or "unknown"
            excerpt = rec.lean_excerpt.replace("\n", " ").strip()[:120] if rec.lean_excerpt else ""
            line = (
                f"  Round {rec.round_num} [{rec.strategy}]: "
                f"error class(es)={classes} | {rec.primary_error[:120]}"
            )
            if excerpt:
                line += f"\n    failing code: {excerpt}"
            lines.append(line)
        return "\n".join(lines)

    @staticmethod
    def _parse_hints(raw: str) -> list[str]:
        hints: list[str] = []
        for line in raw.splitlines():
            stripped = line.strip()
            if stripped.startswith("- "):
                hint = stripped[2:].strip()
                if hint:
                    hints.append(f"[strategy] {hint}")
        return hints[:4]  # cap at 4 strategic hints
