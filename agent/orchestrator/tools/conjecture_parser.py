"""JSON-conjecture parser.

The prover pipeline only consumes conjectures from ``conjectures.json``.
``ParsedConjecture`` is the in-memory view of one such row; the canonical
input is its ``formula`` string, e.g.::

    if ((is_simple) and (p_4 = 0) and (p_5 <= 2) and (f_2>=_7)),
        then p6 >= (((-0.5 * sum_pk_after_p6) + 2))

``from_conjecture_spec`` splits this into ``(hypotheses, conclusion)`` and
forwards it to the prover, with two normalisations:

* Tokens that are no-ops in the Lean theory (``is_simple``, ``is_3_connected``)
  are dropped at parse time so they never reach the goal-extractor LLM.
* If the formula does not match the ``if ..., then ...`` shape, we fail
  fast — silent fallback used to mask malformed conjectures and let them
  flow into the LLM as garbage.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from agent.prover.tools.parsed_theorem import ParsedTheorem, _sha256

if TYPE_CHECKING:
    from agent.conjectures import ConjectureSpec


# Hypotheses that exist in the conjecture DSL but have no Lean counterpart.
# `SimplyCon3ConnectedMap` already encodes simplicity + 3-connectedness, so
# leaking them as separate hypotheses would force the goal extractor to spend
# a prompt rule on dropping them every time. Drop here instead.
_NOOP_HYPOTHESES = frozenset({"is_simple", "is_3_connected"})

# Non-greedy split at the FIRST ", then " so multi-paren cond expressions like
# `((a) and (b))` are captured whole.  Outer parens (one or many wrappers) are
# stripped afterwards by `_strip_outer_parens`.
_IF_THEN_RE = re.compile(
    r'^\s*if\s+(?P<cond>.+?)\s*,\s*then\s+(?P<concl>.+?)\s*$',
    re.IGNORECASE | re.DOTALL,
)


@dataclass
class ParsedConjecture:
    conjecture_id: str        # short form, e.g. "C104"
    statement_latex: str      # raw formula string (DSL, not LaTeX)
    hypotheses: list[str]
    conclusion: str
    # NOTE: never populated by ``from_conjecture_spec`` today — ConjectureSpec
    # has no IRIS fields.  Kept because orchestrator._sort_by_iris reads it;
    # see TODO in that method (currently a no-op sort).
    iris_scores: dict[str, float] = field(default_factory=dict)

    @property
    def short_id(self) -> str:
        """Display ID like 'C45' derived from the numeric suffix."""
        m = re.search(r'_(\d+)$', self.conjecture_id)
        return f"C{m.group(1)}" if m else self.conjecture_id

    def to_parsed_theorem(self) -> ParsedTheorem:
        """Build the prover-side view of this conjecture."""
        content = f"{self.conjecture_id}|{'|'.join(self.hypotheses)}|{self.conclusion}"
        return ParsedTheorem(
            name=self.conjecture_id,
            hypotheses=self.hypotheses,
            conclusion=self.conclusion,
            content_hash=_sha256(content),
        )

    @classmethod
    def from_conjecture_spec(cls, spec: ConjectureSpec) -> ParsedConjecture:
        """Build a ParsedConjecture from a JSON ConjectureSpec.

        Raises ``ValueError`` if ``spec.formula`` does not have the
        ``if ..., then ...`` shape — silent fallback would hand the raw
        formula to the goal extractor as the conclusion.
        """
        formula = spec.formula
        m = _IF_THEN_RE.match(formula)
        if not m:
            raise ValueError(
                f"ParsedConjecture: formula for {spec.name!r} does not match "
                f"'if ..., then ...':\n  {formula!r}"
            )
        cond_raw = _strip_outer_parens(m.group('cond'))
        conclusion = m.group('concl').strip()
        hypotheses = [
            c
            for c in _flatten_and_groups(cond_raw)
            if _normalize_token(c) not in _NOOP_HYPOTHESES
        ]
        cid_match = re.search(r'_(\d+)$', spec.name)
        cid = f"C{cid_match.group(1)}" if cid_match else spec.name
        return cls(
            conjecture_id=cid,
            statement_latex=formula,
            hypotheses=hypotheses,
            conclusion=conclusion,
        )


def _strip_outer_parens(s: str) -> str:
    """Strip one matching outer paren pair, depth-aware.

    `((a) and (b))` → `(a) and (b)`.
    `(a) and (b)`  → `(a) and (b)`  (leading ( closes before end → leave alone).
    """
    s = s.strip()
    if not (s.startswith('(') and s.endswith(')')):
        return s
    depth = 0
    for i, ch in enumerate(s):
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        if depth == 0 and i < len(s) - 1:
            return s  # outer ( closes before the last char → not a single wrapper
    return s[1:-1].strip()


def _flatten_and_groups(s: str) -> list[str]:
    """Split on `and` recursively so nested groups like
    ``((H1) and (H2)) and (H3)`` yield atomic hypotheses ``[H1, H2, H3]``.

    ``_split_top_level_and`` alone only peels one level; the compound left over
    (e.g. ``((is_simple) and (f_2>=_37))``) then hits ``_compile_hypothesis``'s
    fail-closed default and silently drops any p-vec that should satisfy it —
    which broke IRIS scoring and RL CE search on those conjectures.
    """
    parts = _split_top_level_and(s)
    if len(parts) == 1:
        atom = parts[0].strip()
        stripped = _strip_outer_parens(atom)
        if stripped == atom:
            return [atom] if atom else []
        return _flatten_and_groups(stripped)
    out: list[str] = []
    for p in parts:
        out.extend(_flatten_and_groups(p.strip()))
    return out


def _split_top_level_and(s: str) -> list[str]:
    """Split on ``\\s+and\\s+`` at paren depth 0 only."""
    out: list[str] = []
    depth = 0
    last = 0
    i = 0
    # Match ' and ' as a whole word at depth 0
    pattern = re.compile(r'\s+and\s+', re.IGNORECASE)
    while i < len(s):
        ch = s[i]
        if ch == '(':
            depth += 1
            i += 1
        elif ch == ')':
            depth -= 1
            i += 1
        elif depth == 0:
            m = pattern.match(s, i)
            if m:
                out.append(s[last:i])
                last = m.end()
                i = m.end()
            else:
                i += 1
        else:
            i += 1
    out.append(s[last:])
    return out


def _normalize_token(cond: str) -> str:
    """Strip surrounding parentheses + whitespace so '(is_simple)' matches."""
    return cond.strip().strip("()").strip().lower()
