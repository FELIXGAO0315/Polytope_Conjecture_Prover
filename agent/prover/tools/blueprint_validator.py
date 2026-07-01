"""Blueprint sanity check via plantri-pool counterexample search.

After the planner emits a blueprint, every non-main-target node makes a
mathematical claim (its `latex_fragment`). If that claim is REFUTED by a
realizable polytope in the plantri pool, the entire downstream proof chain
is doomed — no LLM can prove a false intermediate, no matter how many
rounds we throw at it.

This module catches such bad blueprints AT planning time by trying to
parse each intermediate's claim into a Python predicate, then evaluating
the predicate over a sample of plantri p-vectors that satisfy the
conjecture's hypotheses.

Design constraint (user red line, 2026-06-29):
  This is a SOUNDNESS check — it tells the planner "your claim is false,
  pick something else". It does NOT inject a specific proof strategy
  (which would violate `feedback_no_cheating`). The validator only ever
  says "your blueprint is bad" — it never says "use Barnette" or "do a
  case-split on Σ".

Parser is intentionally conservative — claims it can't parse are SKIPPED
(silently passed). False negatives are acceptable; false positives are not.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Callable


@dataclass
class Refutation:
    node_id: str
    claim_text: str
    p_vec_key: str
    p_vec: dict[str, int]
    lhs_value: float
    rhs_value: float
    comparator: str

    def message(self) -> str:
        return (
            f"Intermediate lemma `{self.node_id}` is REFUTED by realizable "
            f"polytope p-vec {{{self.p_vec_key}}}: claim `{self.claim_text}` "
            f"evaluates to LHS={self.lhs_value} {self.comparator} "
            f"RHS={self.rhs_value} which is FALSE. This means the blueprint "
            f"is wrong — the planner must pick a different decomposition. "
            f"Common fix: derive the intermediate from existing Inventory "
            f"lemmas directly rather than inventing a new bound."
        )


class BlueprintValidator:
    """Plantri-pool-backed refutation search for blueprint intermediates.

    Usage:
        v = BlueprintValidator(plantri_pool_path)
        refutation = v.check(blueprint_nodes, conjecture_hyps)
        if refutation:
            raise BlueprintError(refutation.message())
    """

    # Cap on how many p-vectors we evaluate per node — full pool (~25k) is
    # overkill; first-violation-wins so a small sample catches most bugs.
    _MAX_PVEC_SAMPLE = 500

    def __init__(self, plantri_pool_path: Path | str):
        path = Path(plantri_pool_path)
        if not path.exists():
            self._pool: list[dict] = []
            return
        try:
            data = json.loads(path.read_text())
            self._pool = data.get("p_vecs", [])
        except Exception:
            self._pool = []

    def is_ready(self) -> bool:
        return bool(self._pool)

    def check(
        self,
        nodes: list,  # list[BlueprintNode]
        conjecture_hyps: list[str],
    ) -> Refutation | None:
        """Scan all non-main-target intermediates; return first refutation."""
        if not self._pool:
            return None
        # Parse conjecture hypotheses into a filter predicate
        hyp_filter = self._compile_hyp_filter(conjecture_hyps)
        if hyp_filter is None:
            # Couldn't parse hypotheses — fall back to the full pool
            relevant = self._pool[: self._MAX_PVEC_SAMPLE]
        else:
            relevant = [
                pv for pv in self._pool if hyp_filter(pv.get("p_vec", {}))
            ][: self._MAX_PVEC_SAMPLE]
        if not relevant:
            return None  # no p-vectors match the hypothesis — can't refute

        for node in nodes:
            if getattr(node, "is_main_target", False):
                continue
            claim_text = (getattr(node, "latex_fragment", "") or "").strip()
            if not claim_text:
                continue
            parsed = self._parse_claim(claim_text)
            if parsed is None:
                continue  # un-parseable — skip silently
            lhs_fn, comp, rhs_fn = parsed
            for pv_entry in relevant:
                pv = pv_entry.get("p_vec", {})
                try:
                    lhs = lhs_fn(pv)
                    rhs = rhs_fn(pv)
                except Exception:
                    break  # evaluator broke — skip this claim entirely
                if not self._compare(lhs, comp, rhs):
                    return Refutation(
                        node_id=getattr(node, "node_id", "<unknown>"),
                        claim_text=claim_text,
                        p_vec_key=pv_entry.get("key", "?"),
                        p_vec={k: int(v) for k, v in pv.items()},
                        lhs_value=float(lhs),
                        rhs_value=float(rhs),
                        comparator=comp,
                    )
        return None

    # ── Claim parser ────────────────────────────────────────────────────

    def _parse_claim(
        self, latex: str
    ) -> tuple[Callable, str, Callable] | None:
        """Parse a LaTeX inequality into (lhs_fn, comparator, rhs_fn).

        Returns None if the claim is too complex / can't be parsed.
        Supported shapes (the ones we've seen blueprints produce):
          p_3, p_4, p_5, p_6 — direct face counts (default 0)
          \\sum_{k \\geq N} p_k — face count tail starting at N
          \\sum_{k \\geq N} (k - M) p_k — weighted tail with linear coefficient
          \\sum_{k \\geq N} (k - M) \\cdot p_k — same with \\cdot
          integer constants
          +, -, *, ()  and integer * factor (no \\cdot needed)
        """
        # Pre-process LaTeX to normalize whitespace and strip irrelevant pieces
        s = latex.strip().lstrip("$").rstrip("$")
        s = re.sub(r"\\text\{[^}]*\}", "", s)
        s = re.sub(r"\\quad|\\qquad", " ", s)
        s = re.sub(r"\s+", " ", s).strip()
        # Strip leading "if ..., then" — only check the consequent
        m_if = re.search(r"\\text\s*\{?\s*then\s*\}?\s*", s)
        if m_if:
            s = s[m_if.end():].strip()

        # Mask out content inside `\{...\}` (sum bounds, subscripts) BEFORE
        # searching for the outer comparator — otherwise `\geq` inside
        # `\sum_{k \geq 7}` is matched first and the wrong split happens.
        # We do the masking only for comparator-position discovery; the
        # original `s` is what _compile_expr will see for substitution.
        s_masked = re.sub(r"\\\{[^}]*\\?\}", lambda m: " " * len(m.group()), s)
        # Common LaTeX brace pairs without backslash: `{k \geq 7}` etc.
        s_masked = re.sub(r"\{[^{}]*\}", lambda m: " " * len(m.group()), s_masked)

        # Find the OUTER comparator (now safe from sum-bound interference)
        cmp_match = re.search(r"\\geq|\\ge\b|\\leq|\\le\b|\\neq|=|≥|≤|<|>", s_masked)
        if not cmp_match:
            return None
        lhs_text = s[: cmp_match.start()].strip()
        op_text = cmp_match.group()
        rhs_text = s[cmp_match.end():].strip()
        comp = {
            "\\geq": ">=", "\\ge": ">=", "≥": ">=",
            "\\leq": "<=", "\\le": "<=", "≤": "<=",
            "=": "==", "<": "<", ">": ">",
        }.get(op_text)
        if comp is None:
            return None

        lhs_fn = self._compile_expr(lhs_text)
        rhs_fn = self._compile_expr(rhs_text)
        if lhs_fn is None or rhs_fn is None:
            return None
        return lhs_fn, comp, rhs_fn

    def _compile_expr(self, expr_latex: str) -> Callable | None:
        """Convert a latex expression substring into a `lambda pv: value`.

        Returns None if any sub-expression can't be normalised — graceful
        skip is preferred over false positives.
        """
        s = expr_latex

        # \cdot → *
        s = s.replace("\\cdot", "*")
        # \,\, etc → space
        s = re.sub(r"\\[,;:!]", " ", s)
        # Strip braces around bare integers like {7}, {6}
        s = re.sub(r"\{(\d+)\}", r"\1", s)

        # Sums with linear coefficient: \sum_{k \geq N} (k - M) p_k
        def _sum_lin(m: re.Match) -> str:
            n = int(m.group(1))
            m_const = int(m.group(2))
            return (
                f"sum((__k - {m_const}) * pv.get(str(__k), 0) "
                f"for __k in range({n}, 30))"
            )
        s = re.sub(
            r"\\sum_\{\s*k\s*\\geq\s*(\d+)\s*\}\s*\(\s*k\s*-\s*(\d+)\s*\)\s*\*?\s*p_k",
            _sum_lin, s,
        )

        # Sums with M-k coefficient: \sum_{k \geq N} (M - k) p_k (less common)
        def _sum_lin2(m: re.Match) -> str:
            n = int(m.group(1))
            m_const = int(m.group(2))
            return (
                f"sum(({m_const} - __k) * pv.get(str(__k), 0) "
                f"for __k in range({n}, 30))"
            )
        s = re.sub(
            r"\\sum_\{\s*k\s*\\geq\s*(\d+)\s*\}\s*\(\s*(\d+)\s*-\s*k\s*\)\s*\*?\s*p_k",
            _sum_lin2, s,
        )

        # Sums of plain p_k: \sum_{k \geq N} p_k
        def _sum_plain(m: re.Match) -> str:
            n = int(m.group(1))
            return f"sum(pv.get(str(__k), 0) for __k in range({n}, 30))"
        s = re.sub(
            r"\\sum_\{\s*k\s*\\geq\s*(\d+)\s*\}\s*p_k",
            _sum_plain, s,
        )

        # If any \sum remains, we couldn't handle it — bail.
        if "\\sum" in s:
            return None

        # p_<digit> or p_{digit} → pv.get(str(digit), 0)
        s = re.sub(r"p_\{(\d+)\}", r'pv.get("\1", 0)', s)
        s = re.sub(r"p_(\d+)", r'pv.get("\1", 0)', s)

        # Insert implicit multiplication: LaTeX writes "5 \sum X" or "5 p_k"
        # meaning 5*X. After our substitutions these read "5 sum(...)" or
        # "5 pv.get(...)" — invalid Python. Insert `*` between digit and the
        # following identifier (sum, pv, p_…) when there's whitespace.
        s = re.sub(r"(\d+)\s+(sum\b|pv\b)", r"\1 * \2", s)
        # Also: ")(" or ") (" needs * — e.g. "(k - 6) p_k" became "(k - 6) pv.get(..."
        s = re.sub(r"(\))\s+(sum\b|pv\b)", r"\1 * \2", s)

        # Reject if anything LaTeX-y remains (control sequences, etc.)
        if re.search(r"\\[a-zA-Z]+", s):
            return None
        # Reject if anything alphabetic other than `pv` / `int` / `get` / `str` / `for`/`in`/`range`/`sum`/`__k`
        # (a safety guard against unintended code execution)
        for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_]*", s):
            if tok not in {"pv", "get", "str", "for", "in", "range", "sum", "__k", "int"}:
                return None

        try:
            code = compile(s, "<blueprint_claim>", "eval")
        except SyntaxError:
            return None

        def _eval(pv: dict[str, int]) -> float:
            # `pv` must be in GLOBALS — generator expressions inside eval'd
            # code can't see eval's locals dict due to Python scoping rules.
            return eval(
                code,
                {
                    "__builtins__": {},
                    "sum": sum, "range": range, "str": str, "int": int,
                    "pv": pv,
                },
                {},
            )

        return _eval

    @staticmethod
    def _compare(lhs: float, op: str, rhs: float) -> bool:
        return {
            ">=": lhs >= rhs,
            "<=": lhs <= rhs,
            "==": lhs == rhs,
            "<": lhs < rhs,
            ">": lhs > rhs,
        }[op]

    # ── Hypothesis filter ───────────────────────────────────────────────

    def _compile_hyp_filter(
        self, hyps: list[str]
    ) -> Callable[[dict[str, int]], bool] | None:
        """Compile conjecture hypotheses into a p-vector filter.

        Supports the same shapes the conjecture generator emits:
          (p_4 = 0)            → pv['4'] == 0
          (p_5 <= 2)           → pv['5'] <= 2
          (f_2 >= 7)           → sum(pv.values()) >= 7
          (f_2>=_7)            → same (compressed form)
          (is_simple)          → always True (plantri pool IS simple polytopes)
        Unparseable hypotheses are SKIPPED — the filter passes everything
        they don't explicitly constrain.
        """
        preds: list[Callable] = []
        for h in hyps:
            h = h.strip().lstrip("(").rstrip(")")
            if "is_simple" in h:
                continue  # plantri pool is all simple — always satisfied
            # p_K = V
            m = re.match(r"p_(\d+)\s*=\s*(\d+)$", h)
            if m:
                k, v = m.group(1), int(m.group(2))
                preds.append(lambda pv, k=k, v=v: pv.get(k, 0) == v)
                continue
            # p_K <= V
            m = re.match(r"p_(\d+)\s*<=\s*(\d+)$", h)
            if m:
                k, v = m.group(1), int(m.group(2))
                preds.append(lambda pv, k=k, v=v: pv.get(k, 0) <= v)
                continue
            # p_K >= V
            m = re.match(r"p_(\d+)\s*>=\s*(\d+)$", h)
            if m:
                k, v = m.group(1), int(m.group(2))
                preds.append(lambda pv, k=k, v=v: pv.get(k, 0) >= v)
                continue
            # f_2 >= V (also tolerates f_2>=_V from generator)
            m = re.match(r"f_2\s*>=_?\s*(\d+)$", h)
            if m:
                v = int(m.group(1))
                preds.append(lambda pv, v=v: sum(pv.values()) >= v)
                continue
            m = re.match(r"f_2\s*<=_?\s*(\d+)$", h)
            if m:
                v = int(m.group(1))
                preds.append(lambda pv, v=v: sum(pv.values()) <= v)
                continue
            # Unrecognised — skip this constraint
        if not preds:
            return None
        return lambda pv: all(p(pv) for p in preds)
