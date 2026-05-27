#!/usr/bin/env python3
"""
agent/orchestrator.py — Main pipeline orchestrator.

Given a conjecture ID, runs two parallel counterexample-finding tracks:
  1. LLM track  — Claude reasons about p-vectors across multiple rounds
  2. RL track   — counterexample_finding_agent (PPO) runs 600+ episodes

If either track finds a CE that passes validation:
  → output/conjecture_with_ce/{id}.json   (status=failed)

If neither finds one after both tracks exhaust:
  → ProverAgent formalizes the conjecture
  → output/conjecture_without_ce/{id}.lean

Usage:
    python -m agent.orchestrator --id C2
    python -m agent.orchestrator --id C2 --rl-episodes 600 --llm-rounds 30
    python -m agent.orchestrator --id C2 --tex conjectures/individual/C2.tex
"""
from __future__ import annotations

import argparse
import json
import re
import threading
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

from agent.config import Config
from agent.claude_sdk import ClaudeSDKClient
from agent.tools.conjecture_parser import ConjectureParser, ParsedConjecture
from agent.tools.check_pvector import PVectorCheckAgent

try:
    from agent.counterexample_finding_agent import train_on_conjecture
    _RL_AVAILABLE = True
    _RL_IMPORT_ERR = ""
except Exception as _e:
    _RL_AVAILABLE = False
    _RL_IMPORT_ERR = str(_e)

_PROJECT_ROOT = Path(__file__).resolve().parent.parent


# ══════════════════════════════════════════════════════════════════════════════
# Polytope math helpers
# ══════════════════════════════════════════════════════════════════════════════

def _dehn_sommerville(p_vec: dict[int, int]) -> int:
    """Return sum((6-k)*p_k) — must equal 12 for a valid simple 3-polytope."""
    return sum((6 - k) * v for k, v in p_vec.items() if v > 0)


def is_valid_simple_polytope(p_vec: dict[int, int]) -> tuple[bool, str]:
    """Check Dehn-Sommerville + non-negativity + minimum size."""
    if not p_vec or all(v <= 0 for v in p_vec.values()):
        return False, "empty p-vector"
    if any(v < 0 for v in p_vec.values()):
        neg = {k: v for k, v in p_vec.items() if v < 0}
        return False, f"negative face counts: {neg}"
    ds = _dehn_sommerville(p_vec)
    if ds != 12:
        return False, f"Dehn-Sommerville fails: sum((6-k)·p_k) = {ds} ≠ 12"
    f2 = sum(p_vec.values())
    if f2 < 4:
        return False, f"f2 = {f2} < 4 (tetrahedron is the smallest)"
    return True, ""


def p_vec_props(p_vec: dict[int, int]) -> dict:
    """Compute derived properties for a p-vector dict."""
    f2 = sum(p_vec.values())
    two_e = sum(k * v for k, v in p_vec.items())
    e = two_e // 2
    v_count = two_e // 3  # 2e = 3v for simple polytopes
    kmax = max(p_vec.keys(), default=6)
    return {
        "p3": p_vec.get(3, 0),
        "p4": p_vec.get(4, 0),
        "p5": p_vec.get(5, 0),
        "p6": p_vec.get(6, 0),
        "sum_pk_after_p6": sum(v for k, v in p_vec.items() if k > 6),
        "f2": f2,
        "num_vertices": v_count,
        "num_edges": e,
        "p_vector": [p_vec.get(k, 0) for k in range(3, kmax + 1)],
    }


# ══════════════════════════════════════════════════════════════════════════════
# LaTeX expression evaluator for IRIS conjecture formulas
# ══════════════════════════════════════════════════════════════════════════════

def _clean_latex_ws(s: str) -> str:
    """Remove LaTeX whitespace commands and collapse spaces."""
    s = re.sub(r'\\[;,!:]', ' ', s)
    s = re.sub(r'\\quad|\\qquad', ' ', s)
    s = s.replace(r'\ ', ' ')
    return re.sub(r'\s+', ' ', s).strip()


def _eval_rhs_expr(expr: str, p_vec: dict[int, int]) -> Optional[float]:
    """Evaluate a RHS expression from an IRIS LaTeX conjecture given p_vec."""
    s = expr

    # Expand fractions, then resolve implicit multiplication.
    s = _expand_fractions(s)
    s = _implicit_mul_to_explicit(s)

    s = _clean_latex_ws(s)

    # \sum_{k \geq N} p_k  →  numeric value
    def _replace_sum(m: re.Match) -> str:
        k_min = int(m.group(1))
        return str(sum(v for k, v in p_vec.items() if k >= k_min))

    s = re.sub(r'\\sum_\{k\s*(?:\\geq|\\ge|>=)\s*(\d+)\}\s*p_k', _replace_sum, s)

    # p_{N} or p_N  →  value
    s = re.sub(r'p_\{(\d+)\}', lambda m: str(p_vec.get(int(m.group(1)), 0)), s)
    s = re.sub(r'p_(\d+)', lambda m: str(p_vec.get(int(m.group(1)), 0)), s)

    # f_2 or f_{2}  →  total face count
    f2 = sum(p_vec.values())
    s = re.sub(r'f_\{2\}|f_2', str(f2), s)

    # Remove remaining LaTeX commands and braces before the final mul pass
    s = re.sub(r'\\[a-zA-Z]+', '', s)
    s = s.replace('{', '(').replace('}', ')')

    # After all substitutions, implicit multiplication may appear as
    # "digit space digit" or "') space digit" — insert * to make Python-valid.
    s = re.sub(r'(\))\s+(\d)', r'\1*\2', s)
    s = re.sub(r'(\d)\s+(\d)', r'\1*\2', s)
    s = re.sub(r'\s+', ' ', s).strip()

    try:
        return float(eval(s, {"__builtins__": {}}, {}))
    except Exception:
        return None


def _eval_hypothesis(hyp: str, p_vec: dict[int, int]) -> bool:
    """Return True if the hypothesis is satisfied by p_vec."""
    s = hyp.strip()

    # \text{...} — always true (simplicity is a structural assumption)
    if re.fullmatch(r'\\text\{[^}]*\}', s):
        return True

    # f_2 \geq N
    m = re.match(r'f_(?:\{2\}|2)\s*(?:\\geq|>=)\s*(\d+)', s)
    if m:
        return sum(p_vec.values()) >= int(m.group(1))

    # f_2 \leq N
    m = re.match(r'f_(?:\{2\}|2)\s*(?:\\leq|<=)\s*(\d+)', s)
    if m:
        return sum(p_vec.values()) <= int(m.group(1))

    # p_k \geq N
    m = re.match(r'p_\{?(\d+)\}?\s*(?:\\geq|>=)\s*(\d+)', s)
    if m:
        return p_vec.get(int(m.group(1)), 0) >= int(m.group(2))

    # p_k \leq N
    m = re.match(r'p_\{?(\d+)\}?\s*(?:\\leq|<=)\s*(\d+)', s)
    if m:
        return p_vec.get(int(m.group(1)), 0) <= int(m.group(2))

    # p_k = N
    m = re.match(r'p_\{?(\d+)\}?\s*=\s*(\d+)', s)
    if m:
        return p_vec.get(int(m.group(1)), 0) == int(m.group(2))

    # Unknown hypothesis — assume satisfied (conservative)
    return True


def _eval_conclusion_violated(conc: str, p_vec: dict[int, int]) -> tuple[bool, str]:
    """Return (is_violated, detail). Violated → p_vec is a counterexample."""
    s = _clean_latex_ws(conc.strip())

    # p_6 \geq EXPR — violated when p_6 < EXPR
    m = re.match(r'p_\{?6\}?\s*(?:\\geq|>=)\s*(.+)', s, re.DOTALL)
    if m:
        rhs = _eval_rhs_expr(m.group(1).strip(), p_vec)
        if rhs is None:
            return False, "could not evaluate RHS"
        p6 = float(p_vec.get(6, 0))
        if p6 < rhs:
            return True, f"p6={p6} < RHS={rhs:.4f} (violation)"
        return False, f"p6={p6} >= RHS={rhs:.4f} (holds)"

    # p_6 \leq EXPR — violated when p_6 > EXPR
    m = re.match(r'p_\{?6\}?\s*(?:\\leq|<=)\s*(.+)', s, re.DOTALL)
    if m:
        rhs = _eval_rhs_expr(m.group(1).strip(), p_vec)
        if rhs is None:
            return False, "could not evaluate RHS"
        p6 = float(p_vec.get(6, 0))
        if p6 > rhs:
            return True, f"p6={p6} > RHS={rhs:.4f} (violation)"
        return False, f"p6={p6} <= RHS={rhs:.4f} (holds)"

    return False, f"unrecognised conclusion form: {conc[:80]}"


def is_counterexample(
    p_vec: dict[int, int], conjecture: ParsedConjecture
) -> tuple[bool, str]:
    """Full CE check: polytope validity + hypotheses + conclusion violation."""
    ok, reason = is_valid_simple_polytope(p_vec)
    if not ok:
        return False, f"invalid polytope: {reason}"

    for hyp in conjecture.hypotheses:
        if not _eval_hypothesis(hyp, p_vec):
            return False, f"hypothesis not satisfied: {hyp[:60]}"

    violated, detail = _eval_conclusion_violated(conjecture.conclusion, p_vec)
    if not violated:
        return False, detail

    return True, detail


# ══════════════════════════════════════════════════════════════════════════════
# Formula string converter (LaTeX → CE agent format)
# ══════════════════════════════════════════════════════════════════════════════

def _expand_fractions(s: str) -> str:
    r"""Replace \frac{A}{B} and \tfrac{A}{B} with (A/B)."""
    s = re.sub(r'\\[tds]?frac\{([^}]+)\}\{([^}]+)\}', r'(\1/\2)', s)
    return s


def _implicit_mul_to_explicit(s: str) -> str:
    r"""Replace LaTeX thin-space implicit multiplication with explicit *.

    In IRIS LaTeX, patterns like  5\,\sum  or  2\,p_k  mean multiplication.
    This must be applied BEFORE stripping \, as whitespace.
    """
    # digit \, (\sum or letter) → digit * \sum
    s = re.sub(r'(\d)\s*\\,\s*(\\[a-zA-Z]|[a-z_])', r'\1*\2', s)
    # fraction-result \, ... → (fraction)*...
    s = re.sub(r'(\))\s*\\,\s*(\\[a-zA-Z]|[a-z_])', r'\1*\2', s)
    return s


def _latex_to_formula_expr(expr: str) -> str:
    """Convert a single LaTeX math expression to CE agent formula format."""
    s = expr.strip()

    # Expand fractions, then resolve implicit multiplication.
    s = _expand_fractions(s)
    s = _implicit_mul_to_explicit(s)

    s = _clean_latex_ws(s)

    # \sum_{k \geq N} p_k → sum_pk_k>=N
    s = re.sub(
        r'\\sum_\{k\s*(?:\\geq|\\ge|>=)\s*(\d+)\}\s*p_k',
        r'sum_pk_k>=\1', s
    )

    # p_{N} or p_N → pN
    s = re.sub(r'p_\{(\d+)\}', r'p\1', s)
    s = re.sub(r'p_(\d+)', r'p\1', s)

    # f_2 or f_{2} → f2
    s = re.sub(r'f_\{2\}|f_2', 'f2', s)

    # \geq → >=, \leq → <=
    s = s.replace(r'\geq', '>=').replace(r'\leq', '<=')

    # Remove remaining LaTeX
    s = re.sub(r'\\[a-zA-Z]+', '', s)
    s = s.replace('{', '(').replace('}', ')')
    s = re.sub(r'\s+', ' ', s).strip()

    return s


def conjecture_to_formula_string(conjecture: ParsedConjecture) -> Optional[str]:
    """Convert a ParsedConjecture to the formula string that train_on_conjecture expects.

    Example output: "if (f2 >= 22), then p6 >= -5*sum_pk_k>=7 + 10"
    """
    cond_parts: list[str] = []
    for hyp in conjecture.hypotheses:
        s = hyp.strip()
        # \text{simple} and similar — skip (assumed by the environment)
        if re.fullmatch(r'\\text\{[^}]*\}', s):
            continue
        cond_parts.append(_latex_to_formula_expr(s))

    conc = _latex_to_formula_expr(conjecture.conclusion)

    if cond_parts:
        cond_str = " and ".join(f"({c})" for c in cond_parts)
        return f"if ({cond_str}), then {conc}"
    return f"then {conc}"


# ══════════════════════════════════════════════════════════════════════════════
# LLM counterexample finder
# ══════════════════════════════════════════════════════════════════════════════

_LLM_SYSTEM = """\
You are an expert in combinatorial geometry specialising in simple convex 3-polytopes.
A simple 3-polytope is described by its p-vector where p_k = number of k-gonal faces.

Mandatory constraints every valid p-vector must satisfy:
  1. All p_k ≥ 0
  2. Dehn–Sommerville: 3·p3 + 2·p4 + p5 - p7 - 2·p8 - 3·p9 - ... = 12
     (i.e. sum over k of (6-k)·p_k = 12)
  3. Total faces f2 = sum p_k ≥ 4 (tetrahedron is the smallest)
  4. Only finitely many p_k are nonzero

Reference examples (all satisfy Dehn–Sommerville):
  - Tetrahedron:         p3=4
  - Cube:                p4=6
  - Dodecahedron:        p5=12
  - Truncated tetrahedron: p3=4, p6=4
  - n-prism:             p4=n, pn=2
  - Fullerene C20:       p5=12, p6=0

Your goal: find p-vectors that satisfy the polytope constraints + conjecture hypotheses
but VIOLATE the conjecture conclusion.
"""

_LLM_ROUND_PROMPT = """\
Conjecture {cid}: {statement}

Hypotheses (ALL must hold):
{hyp_block}

Conclusion (must be VIOLATED — i.e. the inequality must FAIL):
  {conclusion}

{prev_block}\
Think step by step:
1. What values of p3, p4, p5, p6, p7, ... would push the conclusion to fail?
2. Does your candidate satisfy Dehn–Sommerville?
3. Does it satisfy every hypothesis?

Respond ONLY with valid JSON (no prose outside the JSON):
{{
  "reasoning": "your mathematical analysis",
  "candidates": [
    {{"p3": 0, "p4": 0, "p5": 0, "p6": 0, "p7": 0}},
    ...
  ]
}}

Provide 3–5 distinct candidates. Include only integer values ≥ 0.
"""


def _extract_json_from_text(text: str) -> Optional[dict]:
    """Extract the first valid JSON object from an LLM response."""
    # Prefer ```json ... ``` fences
    m = re.search(r'```(?:json)?\s*(\{[\s\S]*?\})\s*```', text)
    if m:
        try:
            return json.loads(m.group(1))
        except json.JSONDecodeError:
            pass

    # Walk the string to find the outermost {…} block
    start = text.find('{')
    if start == -1:
        return None
    depth = 0
    for i in range(start, len(text)):
        if text[i] == '{':
            depth += 1
        elif text[i] == '}':
            depth -= 1
            if depth == 0:
                try:
                    return json.loads(text[start:i + 1])
                except json.JSONDecodeError:
                    break
    return None


class LLMCEFinder:
    """Asks Claude to find counterexample p-vectors over multiple rounds."""

    def __init__(
        self,
        conjecture: ParsedConjecture,
        client: ClaudeSDKClient,
        num_rounds: int = 30,
        stop_event: threading.Event | None = None,
        check_agent=None,
    ) -> None:
        self.conjecture = conjecture
        self.client = client
        self.num_rounds = num_rounds
        self.stop_event = stop_event or threading.Event()
        self.check_agent = check_agent  # PVectorCheckAgent, injected by orchestrator

    def run(self) -> Optional[dict]:
        """Search for a CE. Returns CE info dict or None if exhausted."""
        from agent.tools.check_pvector import PVectorCheckAgent
        checker = self.check_agent or PVectorCheckAgent(client=self.client)
        failed: list[dict] = []

        for rnd in range(1, self.num_rounds + 1):
            if self.stop_event.is_set():
                print(f"[LLM] Round {rnd}: stop signal — halting.")
                return None

            print(f"[LLM] Round {rnd}/{self.num_rounds} …")
            try:
                prompt = self._build_prompt(rnd, failed)
                resp = self.client.messages.create(
                    model=self.client.model,
                    max_tokens=2048,
                    messages=[{"role": "user", "content": prompt}],
                    system=_LLM_SYSTEM,
                )
                text = resp.content[0].text.strip()
            except Exception as exc:
                print(f"[LLM] Round {rnd} API error: {exc}")
                time.sleep(5)
                continue

            candidates = self._parse_candidates(text)
            print(f"[LLM] Round {rnd}: {len(candidates)} candidate(s)")

            for idx, cand in enumerate(candidates):
                # Quick basic check first (polytope validity + violation)
                ok, detail = is_counterexample(cand, self.conjecture)
                if not ok:
                    failed.append({"p_vec": cand, "reason": detail})
                    continue

                # Full 5-check validation
                print(f"[LLM] ✓ CE candidate at round {rnd}: {cand} — {detail}")
                report = checker.run_silent(cand, self.conjecture)
                report.print()

                if report.all_passed:
                    other_candidates = candidates[idx + 1:]  # remaining unchecked
                    return {
                        "p_vector": cand,
                        "found_by": "llm_finder",
                        "found_at_round": rnd,
                        "violation_detail": detail,
                        "other_candidates_not_checked": other_candidates,
                        "found_at": datetime.now(timezone.utc).isoformat(),
                    }

                # Check failed — tell LLM why in next round
                print(f"[LLM] ✗ Candidate failed 5-check: {report.failure_summary()}")
                failed.append({"p_vec": cand,
                               "reason": f"failed 5-check: {report.failure_summary()}"})

            failed = failed[-10:]

        print(f"[LLM] Exhausted {self.num_rounds} rounds without a CE.")
        return None

    # ── helpers ─────────────────────────────────────────────────────────────

    def _build_prompt(self, rnd: int, failed: list[dict]) -> str:
        hyp_block = "\n".join(
            f"  - {h}" for h in self.conjecture.hypotheses
        ) or "  (none)"

        prev_block = ""
        if failed:
            lines = ["Previously tried (did NOT violate the conclusion):"]
            for fa in failed[-5:]:
                lines.append(f"  {fa['p_vec']} → {fa['reason']}")
            prev_block = "\n".join(lines) + "\n\n"

        return _LLM_ROUND_PROMPT.format(
            cid=self.conjecture.conjecture_id,
            statement=self.conjecture.statement_latex,
            hyp_block=hyp_block,
            conclusion=self.conjecture.conclusion,
            prev_block=prev_block,
        )

    def _parse_candidates(self, text: str) -> list[dict[int, int]]:
        data = _extract_json_from_text(text)
        if not data:
            return []
        raw_cands = data.get("candidates", [])
        results: list[dict[int, int]] = []
        for c in raw_cands:
            if not isinstance(c, dict):
                continue
            p_vec: dict[int, int] = {}
            for key, val in c.items():
                m = re.match(r'p(\d+)', str(key))
                if m and isinstance(val, (int, float)) and val >= 0:
                    p_vec[int(m.group(1))] = int(val)
            if p_vec:
                results.append(p_vec)
        return results


# ══════════════════════════════════════════════════════════════════════════════
# P-vector lattice walk CE finder
# ══════════════════════════════════════════════════════════════════════════════

class PVectorCEFinder:
    """Fast CE search via direct random walk on the Dehn-Sommerville lattice.

    Works entirely on p-vectors (no graph construction), so it can instantly
    reach large-k faces (e.g. p11=1) that graph-based RL almost never finds.

    Valid moves preserve sum_{k>=3}(6-k)*p_k = 12:
      For k1 < 6 < k2:  p[k1] += (k2-6),  p[k2] += (6-k1)  — always non-negative
      Reverse:           p[k1] -= (k2-6),  p[k2] -= (6-k1)  — only when feasible
    """

    _PAIRS: list[tuple[int, int]] = [
        (k1, k2) for k1 in range(3, 6) for k2 in range(7, 16)
    ]  # 27 move types covering p7 … p15

    def __init__(
        self,
        conjecture: ParsedConjecture,
        num_steps: int = 200_000,
        num_restarts: int = 60,
        stop_event: threading.Event | None = None,
    ):
        self.conjecture = conjecture
        self.num_steps = num_steps
        self.num_restarts = num_restarts
        self.stop_event = stop_event or threading.Event()

    # ── lattice helpers ──────────────────────────────────────────────────────

    def _start(self) -> dict[int, int]:
        """Randomly perturbed dodecahedron (p5=12, DS-sum=12)."""
        import random
        p: dict[int, int] = {5: 12}
        for _ in range(random.randint(0, 12)):
            k1, k2 = random.choice(self._PAIRS)
            p[k1] = p.get(k1, 0) + (k2 - 6)
            p[k2] = p.get(k2, 0) + (6 - k1)
        return {k: v for k, v in p.items() if v > 0}

    def _neighbours(self, p: dict[int, int]) -> list[dict[int, int]]:
        """All valid one-step neighbours."""
        result: list[dict[int, int]] = []
        for k1, k2 in self._PAIRS:
            d1, d2 = k2 - 6, 6 - k1
            # Forward (always valid — both increments positive)
            p2 = dict(p)
            p2[k1] = p2.get(k1, 0) + d1
            p2[k2] = p2.get(k2, 0) + d2
            result.append({k: v for k, v in p2.items() if v > 0})
            # Reverse (valid only when subtraction stays non-negative)
            if p.get(k1, 0) >= d1 and p.get(k2, 0) >= d2:
                p3 = dict(p)
                p3[k1] = p3.get(k1, 0) - d1
                p3[k2] = p3.get(k2, 0) - d2
                result.append({k: v for k, v in p3.items() if v > 0})
        return result

    def _gap(self, p: dict[int, int]) -> float:
        """Signed violation gap (positive → p_vec is a CE candidate)."""
        for hyp in self.conjecture.hypotheses:
            if not _eval_hypothesis(hyp, p):
                return float('-inf')  # outside feasible region
        violated, detail = _eval_conclusion_violated(self.conjecture.conclusion, p)
        m = re.search(r'p6=([\d.]+).*?RHS=([\d.]+)', detail)
        if m:
            return float(m.group(2)) - float(m.group(1))
        return 1.0 if violated else -1.0

    # ── main search ──────────────────────────────────────────────────────────

    def run(self) -> Optional[dict]:
        """Return CE info dict {p_vector, found_by, found_at_round} or None."""
        import random
        steps_each = max(1, self.num_steps // self.num_restarts)

        for restart in range(self.num_restarts):
            if self.stop_event.is_set():
                return None

            print(f"[p-vector_random_walk] Round {restart + 1}/{self.num_restarts} …", flush=True)
            p = self._start()
            best_gap = self._gap(p)

            for step in range(steps_each):
                if self.stop_event.is_set():
                    return None

                neighbours = self._neighbours(p)
                # Sample up to 10 neighbours for efficiency
                sample = random.sample(neighbours, min(10, len(neighbours)))
                gaps = [self._gap(c) for c in sample]

                # Check for genuine CE
                for cand, g in zip(sample, gaps):
                    if g > 0:
                        ok, _ = is_valid_simple_polytope(cand)
                        if ok:
                            _, detail = _eval_conclusion_violated(
                                self.conjecture.conclusion, cand
                            )
                            return {
                                "p_vector": cand,
                                "found_by": "pvector_walk",
                                "found_at_round": restart * steps_each + step,
                            }

                # Greedy move with 30 % exploration
                best_idx = max(range(len(gaps)), key=lambda i: gaps[i])
                if gaps[best_idx] > best_gap or random.random() < 0.30:
                    p = sample[best_idx]
                    best_gap = gaps[best_idx]

        return None


# ══════════════════════════════════════════════════════════════════════════════
# RL counterexample finder (thread target)
# ══════════════════════════════════════════════════════════════════════════════

def _rl_finder_thread(
    formula: str,
    name: str,
    num_episodes: int,
    result_holder: list,
    lock: threading.Lock,
    ce_found_event: threading.Event,
    label: str = "",
    conjecture=None,
    check_agent=None,
) -> None:
    """Run train_on_conjecture, 5-check every CE found, report first passing one."""
    tag = f"[rl agent{':' + label if label else ''}]"
    if not _RL_AVAILABLE:
        print(f"{tag} disabled: {_RL_IMPORT_ERR}")
        return

    try:
        result = train_on_conjecture(
            formula=formula,
            name=name,
            num_episodes=num_episodes,
            exit_on_first_ce=False,   # collect all CEs; we'll pick first passing one
        )
    except Exception as exc:
        print(f"{tag} train_on_conjecture raised: {exc}")
        return

    ces = result.get("counterexamples", [])
    if not ces:
        print(f"{tag} No CE found in {num_episodes} episodes.")
        return

    print(f"{tag} {len(ces)} CE candidate(s) found — running 5-check on each …")

    from agent.tools.check_pvector import PVectorCheckAgent
    checker = check_agent or (PVectorCheckAgent(client=None) if conjecture else None)

    for idx, raw in enumerate(ces):
        if ce_found_event.is_set():
            return

        p_vec_list = raw.get("p_vector", [])
        p_vec: dict[int, int] = {
            k + 3: int(v)
            for k, v in enumerate(p_vec_list)
            if isinstance(v, (int, float)) and v > 0
        }

        detail = f"gap={raw.get('gap', 0):.4f}, margin={raw.get('margin', 0):.4f}"
        print(f"{tag} Checking CE #{idx + 1}: {p_vec} — {detail}")

        if checker and conjecture:
            report = checker.run_silent(p_vec, conjecture)
            report.print()
            if not report.all_passed:
                print(f"{tag} ✗ CE #{idx + 1} failed 5-check: {report.failure_summary()}")
                continue

        # This CE passed — record it, list remaining as other_candidates
        other_candidates = [
            {k + 3: int(v)
             for k, v in enumerate(r.get("p_vector", []))
             if isinstance(v, (int, float)) and v > 0}
            for r in ces[idx + 1:]
        ]
        with lock:
            if not ce_found_event.is_set():
                result_holder.append({
                    "p_vector": p_vec,
                    "found_by": "rl_agent",
                    "found_at_round": raw.get("episode", 0),
                    "violation_detail": detail,
                    "other_candidates_not_checked": other_candidates,
                    "found_at": raw.get("found_at", datetime.now(timezone.utc).isoformat()),
                })
                ce_found_event.set()
                print(f"{tag} ✓ CE confirmed at episode {raw.get('episode', '?')}")
        return

    print(f"{tag} All {len(ces)} CE candidate(s) failed 5-check.")


# ══════════════════════════════════════════════════════════════════════════════
# Output writers
# ══════════════════════════════════════════════════════════════════════════════

def _write_ce_json(
    conjecture: ParsedConjecture, ce_info: dict, out_dir: Path
) -> Path:
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / f"{conjecture.conjecture_id}.json"

    p_vec = ce_info.get("p_vector", {})
    props = p_vec_props(p_vec) if p_vec else {}
    kmax = max(p_vec.keys(), default=6)

    payload = {
        "conjecture_id": conjecture.conjecture_id,
        "conjecture_latex": conjecture.statement_latex,
        "hypotheses": conjecture.hypotheses,
        "conclusion": conjecture.conclusion,
        "status": "failed",
        "counterexample": {
            "p_vector": [p_vec.get(k, 0) for k in range(3, kmax + 1)],
            **{f"p{k}": p_vec.get(k, 0) for k in range(3, kmax + 1)},
            "f2": props.get("f2", 0),
            "num_vertices": props.get("num_vertices", 0),
            "num_edges": props.get("num_edges", 0),
        },
        "found_by": ce_info.get("found_by", "unknown"),
        "found_at_round": ce_info.get("found_at_round", -1),
        "violation_detail": ce_info.get("violation_detail", ""),
        "found_at": ce_info.get("found_at", datetime.now(timezone.utc).isoformat()),
        "other_candidates_not_checked": ce_info.get("other_candidates_not_checked", []),
    }
    out_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False))
    print(f"[Output] CE JSON → {out_path}")
    return out_path


def _resolve_lean_output(conjecture: ParsedConjecture, no_ce_dir: Path) -> Optional[Path]:
    """Find the Lean file written by ProverAgent and copy it to no_ce_dir."""
    # ProverAgent writes to output/conjecture_proof/{id}.lean by default
    prover_out = _PROJECT_ROOT / "output" / "conjecture_proof" / f"{conjecture.conjecture_id}.lean"
    if prover_out.exists():
        dst = no_ce_dir / f"{conjecture.conjecture_id}.lean"
        dst.write_text(prover_out.read_text())
        return dst
    return None


# ══════════════════════════════════════════════════════════════════════════════
# Orchestrator
# ══════════════════════════════════════════════════════════════════════════════

class Orchestrator:
    """Top-level pipeline: CE search → ProverAgent fallback."""

    def __init__(self, config: Config | None = None) -> None:
        self.config = config or Config.from_env()
        self.client = ClaudeSDKClient(model=self.config.model_main)
        self._ce_dir = _PROJECT_ROOT / "output" / "conjecture_with_ce"
        self._no_ce_dir = _PROJECT_ROOT / "output" / "conjecture_without_ce"

    # ── Public API ─────────────────────────────────────────────────────────────

    def run_from_id(
        self,
        conjecture_id: str,
        tex_path: str | None = None,
        rl_episodes: int = 600,
        llm_rounds: int = 30,
    ) -> None:
        """Single-conjecture entry point by ID."""
        conjecture = self._load_conjecture(conjecture_id, tex_path)
        self.run(conjecture, rl_episodes=rl_episodes, llm_rounds=llm_rounds)

    def run(
        self,
        conjecture: ParsedConjecture,
        rl_episodes: int = 600,
        llm_rounds: int = 30,
    ) -> None:
        """Single-conjecture pipeline: CE search → ProverAgent fallback."""
        _sep = "=" * 70
        print(f"\n{_sep}")
        print(f"Orchestrator  →  {conjecture.conjecture_id}")
        print(f"Statement : {conjecture.statement_latex}")
        print(f"Hypotheses: {conjecture.hypotheses}")
        print(f"Conclusion: {conjecture.conclusion}")
        print(_sep)

        ce_info = self._run_ce_search(conjecture, rl_episodes, llm_rounds)
        if ce_info:
            _write_ce_json(conjecture, ce_info, self._ce_dir)
        else:
            self._run_prover(conjecture)

    def run_batch(
        self,
        tex_path: str,
        rl_episodes: int = 600,
        llm_rounds: int = 30,
    ) -> None:
        """Batch pipeline: 7 parallel IRIS-sort workers compete to find CEs.

        Each worker iterates conjectures in a different sort order (T, R, L,
        TR, TL, RL, TRL). Workers atomically claim conjectures so no two
        workers duplicate work on the same conjecture. The first worker to
        find a CE for a conjecture marks it done; remaining workers skip it.

        After all workers finish, any conjecture without a CE goes to
        ProverAgent (sequentially, one per conjecture).
        """
        # ── Load and sort ──────────────────────────────────────────────────────
        conjectures = self._load_all_conjectures(tex_path)
        if not conjectures:
            print(f"[Batch] No conjectures found in {tex_path}")
            return

        print(f"\n[Batch] Loaded {len(conjectures)} conjecture(s) from {tex_path}")

        _SORTS = ["T", "R", "L", "TR", "TL", "RL", "TRL"]
        sorted_lists = {s: self._sort_by_iris(conjectures, s) for s in _SORTS}

        # ── Shared state ───────────────────────────────────────────────────────
        state_lock = threading.Lock()
        claimed: set[str] = set()    # being worked on right now
        completed: set[str] = set()  # CE found (written to disk)
        # conjectures without CE after all workers finish → ProverAgent
        no_ce: set[str] = set()

        # ── Launch 7 worker threads ────────────────────────────────────────────
        workers = []
        for sort_key in _SORTS:
            t = threading.Thread(
                target=self._batch_worker,
                args=(sort_key, sorted_lists[sort_key],
                      state_lock, claimed, completed, no_ce,
                      rl_episodes, llm_rounds),
                name=f"Worker-{sort_key}",
                daemon=True,
            )
            workers.append(t)

        print(f"[Batch] Launching {len(workers)} workers …\n")
        for t in workers:
            t.start()
        for t in workers:
            t.join()

        # ── ProverAgent for conjectures without CE ─────────────────────────────
        remaining = [c for c in conjectures if c.conjecture_id in no_ce]
        print(f"\n[Batch] CE search done. "
              f"{len(completed)} with CE, {len(remaining)} without → ProverAgent")

        for c in remaining:
            try:
                self._run_prover(c)
            except Exception as exc:
                print(f"[Batch] ProverAgent failed for {c.conjecture_id}: {exc}")

        print("\n[Batch] All done.")

    # ── CE search (shared by single + batch modes) ─────────────────────────────

    def _run_ce_search(
        self,
        conjecture: ParsedConjecture,
        rl_episodes: int,
        llm_rounds: int,
        label: str = "",
    ) -> Optional[dict]:
        """Run parallel LLM + RL CE search. Returns validated CE info or None."""
        tag = f"[{conjecture.conjecture_id}{':' + label if label else ''}]"

        ce_found_event = threading.Event()
        result_holder: list[dict] = []
        lock = threading.Lock()

        formula_str = conjecture_to_formula_string(conjecture)
        print(f"{tag} formula: {formula_str}")

        # ── Fast p-vector lattice walk (no API, no graph construction) ────────
        pvec_result = PVectorCEFinder(
            conjecture=conjecture,
            num_steps=200_000,
            num_restarts=60,
            stop_event=threading.Event(),
        ).run()
        if pvec_result:
            p_vec = pvec_result["p_vector"]
            rnd = pvec_result['found_at_round']
            _, detail = _eval_conclusion_violated(conjecture.conclusion, p_vec)
            p6_val = p_vec.get(6, 0)
            print(f"[p-vector_random_walk] ✓ CE found at round {rnd}: "
                  f"{p_vec} — p6={p6_val:.1f} < {detail.split('<')[1].strip()}")
            report = PVectorCheckAgent(client=self.client).run(p_vec, conjecture)
            if report.all_passed:
                pvec_result["violation_detail"] = detail
                print(f"[Conclusion] ✓ Validated CE from p-vector_random_walk "
                      f"at round {rnd}")
                return pvec_result
            print(f"[Conclusion] ✗ p-vector walk CE failed validation, continuing …")
        print(f"[p-vector_random_walk] P-vector walk exhausted, falling back to LLM + RL …")

        # ── Standard CE finding: LLM + RL in parallel ─────────────────────────
        print(f"[Standard ce finding process] RL episodes: {rl_episodes}  |  LLM rounds: {llm_rounds}")

        # Shared check_agent (LLM check uses the same client)
        check_agent = PVectorCheckAgent(client=self.client)

        # RL track (daemon thread) — passes conjecture + check_agent for inline validation
        rl_thread: threading.Thread | None = None
        if _RL_AVAILABLE and formula_str:
            rl_thread = threading.Thread(
                target=_rl_finder_thread,
                args=(formula_str, conjecture.conjecture_id, rl_episodes,
                      result_holder, lock, ce_found_event, label),
                kwargs={"conjecture": conjecture, "check_agent": check_agent},
                daemon=True,
                name=f"RL-{conjecture.conjecture_id}-{label}",
            )
            rl_thread.start()
        else:
            reason = _RL_IMPORT_ERR if not _RL_AVAILABLE else "formula conversion failed"
            print(f"[rl agent] disabled: {reason}")

        # LLM track (this thread) — 5-check happens inside LLMCEFinder per round
        llm_result = LLMCEFinder(
            conjecture=conjecture,
            client=self.client,
            num_rounds=llm_rounds,
            stop_event=ce_found_event,
            check_agent=check_agent,
        ).run()

        if llm_result:
            with lock:
                if not ce_found_event.is_set():
                    result_holder.append(llm_result)
                    ce_found_event.set()

        # If LLM exhausted but RL still running, wait for it
        if rl_thread and rl_thread.is_alive() and not ce_found_event.is_set():
            print(f"[Standard ce finding process] LLM exhausted, waiting for RL …")
            rl_thread.join()

        if not result_holder:
            print(f"[Standard ce finding process] No CE found.")
            return None

        # CE already passed 5-check inside the finder — just confirm and return
        ce_info = result_holder[0]
        print(f"[Conclusion] ✓ Validated CE from {ce_info['found_by']} "
              f"at round {ce_info['found_at_round']}")
        return ce_info

    # ── Batch worker ───────────────────────────────────────────────────────────

    def _batch_worker(
        self,
        sort_key: str,
        conjectures: list[ParsedConjecture],
        state_lock: threading.Lock,
        claimed: set[str],
        completed: set[str],
        no_ce: set[str],
        rl_episodes: int,
        llm_rounds: int,
    ) -> None:
        """One sort-strategy worker. Iterates its ordered list, claims each
        unclaimed conjecture, runs CE search, then marks it done."""
        tag = f"[Worker-{sort_key}]"
        print(f"{tag} started, {len(conjectures)} conjectures in order")

        for c in conjectures:
            cid = c.conjecture_id

            # Atomically claim the conjecture (skip if already taken)
            with state_lock:
                if cid in completed or cid in claimed:
                    continue
                claimed.add(cid)

            print(f"{tag} → claiming {cid}")
            try:
                ce_info = self._run_ce_search(c, rl_episodes, llm_rounds, label=sort_key)
            except Exception as exc:
                print(f"{tag} CE search error for {cid}: {exc}")
                ce_info = None

            with state_lock:
                claimed.discard(cid)
                completed.add(cid)
                if ce_info:
                    _write_ce_json(c, ce_info, self._ce_dir)
                else:
                    no_ce.add(cid)

        print(f"{tag} finished")

    # ── Private helpers ────────────────────────────────────────────────────────

    def _run_prover(self, conjecture: ParsedConjecture) -> None:
        from agent.prover_agent import ProverAgent

        print(f"\n[Orchestrator] ProverAgent starting for {conjecture.conjecture_id} …")
        agent = ProverAgent(self.config)
        # Route ProverAgent output directly into conjecture_without_ce/
        agent._proof_subdir = "conjecture_without_ce"

        try:
            result = agent.prove_conjecture(conjecture)
        except Exception as exc:
            print(f"[Orchestrator] ProverAgent raised: {exc}")
            raise

        # The Lean file is already written by ProverAgent; just confirm path.
        lean_path = (
            _PROJECT_ROOT / "output" / "conjecture_without_ce"
            / f"{conjecture.conjecture_id}.lean"
        )
        if lean_path.exists():
            print(f"[Output] Lean file → {lean_path}")
        else:
            # Fallback: check the default prover output directory
            fallback = _resolve_lean_output(conjecture, self._no_ce_dir)
            if fallback:
                print(f"[Output] Lean file (copied) → {fallback}")
            else:
                print(f"[Output] Warning: Lean file not found at expected path.")

        print(f"\n[Orchestrator] Done. Result: {result.status}")

    def _load_all_conjectures(self, tex_path: str) -> list[ParsedConjecture]:
        """Load every conjecture from a tex file.

        Supports two formats:
        - Combined longtable (conjectures.tex) — rows with IRIS scores
        - Directory of individual files — scans for C*.tex
        """
        parser = ConjectureParser()
        path = Path(tex_path)

        # 1. Try longtable format (has IRIS scores → enables sort)
        if path.is_file():
            conjectures = parser.parse_file(path.read_text())
            if conjectures:
                return conjectures
            # Might be a single-theorem file — still try it
            # (falls through to individual-file fallback below)

        # 2. Directory of individual C*.tex files (no IRIS scores)
        if path.is_dir():
            results: list[ParsedConjecture] = []
            for tex_file in sorted(path.glob("C*.tex")):
                cid = tex_file.stem
                tex = tex_file.read_text()
                m = re.search(
                    r'\\begin\{theorem\}\[' + re.escape(cid) + r'\]\s*([\s\S]*?)\s*\\end\{theorem\}',
                    tex,
                )
                if m:
                    results.append(parser.parse_statement(m.group(1).strip(), cid))
            return results

        raise FileNotFoundError(f"Cannot load conjectures from {tex_path!r}")

    def _sort_by_iris(
        self, conjectures: list[ParsedConjecture], sort_key: str
    ) -> list[ParsedConjecture]:
        """Sort conjectures by an IRIS score combination (descending).

        sort_key ∈ {'T', 'R', 'L', 'TR', 'TL', 'RL', 'TRL'}.
        Conjectures without IRIS scores are placed at the end.
        """
        def _score(c: ParsedConjecture) -> float:
            s = c.iris_scores
            T = s.get("T", 0.0)
            R = s.get("R", 0.0)
            L = s.get("L", 0.0)
            return {
                "T": T, "R": R, "L": L,
                "TR": T * R, "TL": T * L, "RL": R * L,
                "TRL": T * R * L,
            }.get(sort_key, T * R * L)

        return sorted(conjectures, key=_score, reverse=True)

    def _load_conjecture(
        self, conjecture_id: str, tex_path: str | None = None
    ) -> ParsedConjecture:
        """Load a ParsedConjecture from a .tex file or the combined table."""
        parser = ConjectureParser()

        # 1. Explicit path or auto-discovered individual file
        source = (
            Path(tex_path)
            if tex_path
            else _PROJECT_ROOT / "conjectures" / "individual" / f"{conjecture_id}.tex"
        )
        if source.exists():
            tex = source.read_text()
            # Individual files wrap the statement in \begin{theorem}[ID] ... \end{theorem}
            m = re.search(
                r'\\begin\{theorem\}\[' + re.escape(conjecture_id) + r'\]\s*([\s\S]*?)\s*\\end\{theorem\}',
                tex,
            )
            if m:
                return parser.parse_statement(m.group(1).strip(), conjecture_id)

        # 2. Combined longtable file
        combined = _PROJECT_ROOT / "conjectures" / "conjectures.tex"
        if combined.exists():
            for c in parser.parse_file(combined.read_text()):
                if c.conjecture_id == conjecture_id:
                    return c

        raise FileNotFoundError(
            f"Conjecture {conjecture_id!r} not found.\n"
            f"  Tried individual: {source}\n"
            f"  Tried combined:   {combined}"
        )


# ══════════════════════════════════════════════════════════════════════════════
# CLI entry point
# ══════════════════════════════════════════════════════════════════════════════

def main() -> None:
    p = argparse.ArgumentParser(
        description=(
            "Polytope conjecture orchestrator.\n\n"
            "Single mode:  --id C2\n"
            "Batch mode:   --batch --tex conjectures/conjectures.tex"
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )

    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--id", metavar="ID",
                      help="Single conjecture ID (e.g. C2)")
    mode.add_argument("--batch", action="store_true",
                      help="Batch mode: process all conjectures in --tex with "
                           "7 parallel IRIS-sort workers")

    p.add_argument("--tex", default=None, metavar="PATH",
                   help="Path to .tex file or directory of C*.tex files")
    p.add_argument("--rl-episodes", type=int, default=600, metavar="N",
                   help="RL episodes per conjecture (default: 600)")
    p.add_argument("--llm-rounds", type=int, default=30, metavar="N",
                   help="LLM CE search rounds per conjecture (default: 30)")
    args = p.parse_args()

    orch = Orchestrator()

    if args.batch:
        if not args.tex:
            p.error("--batch requires --tex <path>")
        orch.run_batch(
            tex_path=args.tex,
            rl_episodes=args.rl_episodes,
            llm_rounds=args.llm_rounds,
        )
    else:
        orch.run_from_id(
            conjecture_id=args.id,
            tex_path=args.tex,
            rl_episodes=args.rl_episodes,
            llm_rounds=args.llm_rounds,
        )


if __name__ == "__main__":
    main()
