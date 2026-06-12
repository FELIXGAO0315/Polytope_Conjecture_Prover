#!/usr/bin/env python3
"""
agent/orchestrator.py — Main pipeline orchestrator.

Given a conjecture name, runs three stages:
  Stage 1: p-vector lattice walk (fast, no API — samples the DS lattice)
  Stage 2: unified CE search, led by PlantriCEFinder (agent/plantri_ce_finder):
           its exhaustive screen runs first (no API — analytic constructions,
           then plantri exhaustion; verdicts are final and cached), then four
           parallel tracks on whatever the screen left undecided: LLM (default
           15 rounds) + RL (600 episodes) + Hopper + the finder's constructor
           double check (one stochastic build attempt per survivor)
  Stage 3: Lean prover (gated by the Inventory-entailment pre-check, which
           also runs the automatic plantri decision of any countermodels)

If any stage finds a CE that passes validation:
  → output/conjecture_with_ce/{Cx}/{Cx}.json          (status=failed)
  → output/conjecture_with_ce/{Cx}/{Cx}_witness.png   (planar drawing of the
    verified witness graph, rendered automatically)

If no CE is found after stages 1-2 exhaust:
  → ProverAgent formalizes the conjecture
  → output/conjecture_without_ce/{name}.lean

Input is always JSON (conjectures/conjectures.json or a single *.json file).

Usage:
    python -m agent.orchestrator --name auto_xxx
    python -m agent.orchestrator --name auto_xxx --rl-episodes 600 --llm-rounds 30
    python -m agent.orchestrator --batch
    python -m agent.orchestrator --batch --json conjectures/conjectures.json
"""
from __future__ import annotations

import argparse
import json
import multiprocessing as _mp
import os
import re
import threading
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

from agent.config import Config
from agent.claude_sdk import ClaudeSDKClient
from agent.procutil import set_pdeathsig
from agent.conjectures import load_conjectures, ConjectureSpec
from agent.orchestrator.tools.conjecture_parser import ConjectureParser, ParsedConjecture
from agent.orchestrator.tools.check_pvector import PVectorCheckAgent
from agent.orchestrator.tools.pvec_eval import (
    _dehn_sommerville,
    is_valid_simple_polytope,
    p_vec_props,
    _clean_latex_ws,
    _expand_fractions,
    _implicit_mul_to_explicit,
    _eval_rhs_expr,
    _eval_hypothesis,
    _eval_conclusion_violated,
    is_counterexample,
)
from agent.llm_ce_finder.agent import LLMCEFinder
from agent.plantri_ce_finder.agent import PlantriCEFinder

try:
    from agent.rl_ce_finder.agent import train_on_conjecture as _agents_train_on_conjecture
    _RL_AVAILABLE = True
    _RL_IMPORT_ERR = ""
except Exception as _e2:
    _RL_AVAILABLE = False
    _RL_IMPORT_ERR = str(_e2)

try:
    from agent.hopper_ce_finder.agent import HopperCEFinder as _HopperCEFinder
    _HOPPER_AVAILABLE = True
    _HOPPER_IMPORT_ERR = ""
except Exception as _e3:
    _HOPPER_AVAILABLE = False
    _HOPPER_IMPORT_ERR = str(_e3)

_PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent


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

    For JSON-sourced conjectures the formula is stored verbatim in statement_latex,
    so we return it directly (after the agents-format fixup) instead of re-parsing LaTeX.
    """
    stmt = conjecture.statement_latex.strip()
    if re.match(r'if\s*\(', stmt, re.IGNORECASE):
        return _to_agents_formula(stmt)

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


def _to_agents_formula(formula: str) -> str:
    """Convert this project's formula string to the agents/ RL parser format.

    Two fixes needed:
    1. f2 >= N  →  f_2>=_N  (the other parser's F2 regex requires this form)
    2. Remove parens around integer fractions like (13/14) → 13/14.
       The other parser's _compile_conclusion strips one level of outer parens
       if rhs_raw.startswith("(") and rhs_raw.endswith(")").  Our RHS starts
       with "(13/14)*p3..." and ends with "...(13/7)" which falsely triggers
       that check, mangling the expression.  Removing fraction parens is
       mathematically identical (/ and * share precedence, left-associative).
    """
    formula = re.sub(r'\bf2\s*>=\s*(\d+)', r'f_2>=_\1', formula)
    formula = re.sub(r'\((\d+/\d+)\)', r'\1', formula)
    return formula


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
        """Signed violation gap (positive → p_vec is a CE candidate).

        Sign is tied to the actual `violated` flag so the gradient is correct
        for both >=- and <=-form conclusions and for negative RHS values.
        (The old `RHS − p6` formula inverted the gradient for <=-form
        conclusions and dropped the minus sign of negative RHS.)"""
        for hyp in self.conjecture.hypotheses:
            if not _eval_hypothesis(hyp, p):
                return float('-inf')  # outside feasible region
        violated, detail = _eval_conclusion_violated(self.conjecture.conclusion, p)
        m = re.search(r'p6=(-?[\d.]+).*?RHS=(-?[\d.]+)', detail)
        if m:
            magnitude = abs(float(m.group(1)) - float(m.group(2)))
            return magnitude if violated else -magnitude
        return 1.0 if violated else -1.0

    # ── main search ──────────────────────────────────────────────────────────

    def run(self) -> Optional[dict]:
        """Return CE info dict {p_vector, found_by, found_at_round} or None."""
        import random
        steps_each = max(1, self.num_steps // self.num_restarts)

        print("[Stage 1] Starting random walk to find counterexamples...", flush=True)

        for restart in range(self.num_restarts):
            if self.stop_event.is_set():
                return None

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


_threadpool_limiter = None   # keep the threadpoolctl limiter alive for the process


def _set_compute_threads(n: int) -> None:
    """Limit torch's pools to n and pin BLAS to 1 thread for this process.

    BLAS must be 1, not n: the Hopper/RL hot loops use tiny matrices where
    MKL's dynamic mode already runs sequentially — explicitly granting MKL n
    threads ACTIVATES its pool, and the workers' post-call spin-waiting was
    measured to burn 5+ cores for zero wall-time gain (200-step Hopper probe:
    2.1→5.1 cores at identical speed).
    """
    global _threadpool_limiter
    n = max(1, n)
    try:
        import torch
        torch.set_num_threads(n)
        torch.set_num_interop_threads(max(1, n // 2))
    except Exception:
        pass
    # for libraries or subprocesses initialised after this point
    for var in ("OMP_NUM_THREADS", "MKL_NUM_THREADS",
                "OPENBLAS_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
        os.environ[var] = "1"
    try:
        from threadpoolctl import threadpool_limits
        _threadpool_limiter = threadpool_limits(limits=1, user_api="blas")
    except Exception:
        pass


def _rl_finder_process(
    formula: str,
    name: str,
    num_episodes: int,
    result_queue: "_mp.Queue[dict]",
    stop_event: "_mp.Event",
    conjecture=None,
    num_threads: int = 0,
) -> None:
    """Run RL CE finder in a separate process, push validated CE to result_queue."""
    set_pdeathsig()  # daemon=True only covers clean parent exits; this covers SIGKILL/crash too
    if num_threads > 0:
        _set_compute_threads(num_threads)

    tag = "[validation check ce from rl]"
    if not _RL_AVAILABLE:
        print(f"{tag} disabled: {_RL_IMPORT_ERR}")
        return

    agents_formula = _to_agents_formula(formula)

    try:
        result = _agents_train_on_conjecture(
            formula=agents_formula,
            name=name,
            num_episodes=num_episodes,
            exit_on_first_ce=False,
            stop_event=stop_event,
        )
    except Exception as exc:
        print(f"{tag} train_on_conjecture raised: {exc}")
        return

    ces = result.get("counterexamples", [])
    if not ces:
        return

    print(f"{tag} {len(ces)} CE candidate(s) found, running 5 checks")

    from agent.orchestrator.tools.check_pvector import PVectorCheckAgent
    checker = PVectorCheckAgent(client=None) if conjecture else None

    for idx, raw in enumerate(ces):
        if stop_event.is_set():
            return

        p_vec_list = raw.get("p_vector", [])
        p_vec: dict[int, int] = {
            k + 3: int(v)
            for k, v in enumerate(p_vec_list)
            if isinstance(v, (int, float)) and v > 0
        }

        detail = f"gap={raw.get('gap', 0):.4f}, margin={raw.get('margin', 0):.4f}"

        w_edges = None
        if checker and conjecture:
            report = checker.run_silent(p_vec, conjecture, rl_verified=True)
            for r in report.results:
                mark = "√" if r.passed else "✗"
                print(f"{tag} {mark} {r.label}: {r.detail}")
            if not report.all_passed:
                print(f"{tag} CE #{idx + 1}/{len(ces)}: not valid — proceed to next")
                continue
            w_edges = report.witness_edges

        other_candidates = [
            {k + 3: int(v)
             for k, v in enumerate(r.get("p_vector", []))
             if isinstance(v, (int, float)) and v > 0}
            for r in ces[idx + 1:]
        ]
        ce_record = {
            "p_vector": p_vec,
            "found_by": "rl_agent",
            "found_at_round": raw.get("episode", 0),
            "violation_detail": detail,
            "other_candidates_not_checked": other_candidates,
            "found_at": raw.get("found_at", datetime.now(timezone.utc).isoformat()),
            "witness_edges": w_edges,
        }
        if conjecture:
            try:
                out_path = _write_ce_json(conjecture, ce_record, _PROJECT_ROOT / "output" / "conjecture_with_ce")
                print(f"{tag} The ce candidate is valid, saved CE JSON → {out_path}")
            except Exception as exc:
                print(f"{tag} warning: could not write CE JSON: {exc}")
        result_queue.put(ce_record)
        stop_event.set()
        return


def _hopper_finder_process(
    conjecture,
    num_steps: int,
    result_queue: "_mp.Queue[dict]",
    stop_event: "_mp.Event",
    num_threads: int = 0,
) -> None:
    """Run Hopper CE finder in a separate process, push validated CE to result_queue."""
    set_pdeathsig()
    if num_threads > 0:
        _set_compute_threads(num_threads)

    tag = "[validation check ce from hopper]"
    if not _HOPPER_AVAILABLE:
        print(f"{tag} disabled: {_HOPPER_IMPORT_ERR}")
        return

    try:
        hopper = _HopperCEFinder(
            conjecture=conjecture,
            num_steps=num_steps,
            stop_event=stop_event,
        )
        result = hopper.run()
    except Exception as exc:
        print(f"{tag} HopperCEFinder raised: {exc}")
        return

    if result is None:
        return

    p_vec = result.get("p_vector", {})
    detail = result.get("violation_detail", "")

    from agent.orchestrator.tools.check_pvector import PVectorCheckAgent
    checker = PVectorCheckAgent(client=None)
    report = checker.run_silent(p_vec, conjecture)

    print(f"{tag} CE candidate from Hopper, running 5 checks")
    for r in report.results:
        mark = "√" if r.passed else "✗"
        print(f"{tag} {mark} {r.label}: {r.detail}")

    if not report.all_passed:
        print(f"{tag} CE not valid — Hopper exhausted")
        return

    ce_record = {
        "p_vector": p_vec,
        "found_by": "hopper_agent",
        "found_at_round": result.get("found_at_round", 0),
        "violation_detail": detail,
        "other_candidates_not_checked": [],
        "found_at": result.get("found_at", datetime.now(timezone.utc).isoformat()),
        "witness_edges": report.witness_edges,
    }
    try:
        out_path = _write_ce_json(conjecture, ce_record, _PROJECT_ROOT / "output" / "conjecture_with_ce")
        print(f"{tag} CE valid, saved CE JSON → {out_path}")
    except Exception as exc:
        print(f"{tag} warning: could not write CE JSON: {exc}")
    result_queue.put(ce_record)
    stop_event.set()


# ══════════════════════════════════════════════════════════════════════════════
# Output writers
# ══════════════════════════════════════════════════════════════════════════════

def _write_ce_json(
    conjecture: ParsedConjecture, ce_info: dict, out_dir: Path
) -> Path:
    """Write the CE artifact folder: out_dir/<Cx>/<Cx>.json plus, when a
    witness graph is available, an automatic <Cx>_witness.png rendering."""
    ce_dir = out_dir / conjecture.short_id
    ce_dir.mkdir(parents=True, exist_ok=True)
    out_path = ce_dir / f"{conjecture.short_id}.json"

    p_vec = ce_info.get("p_vector", {})
    props = p_vec_props(p_vec) if p_vec else {}
    kmax = max(p_vec.keys(), default=6)

    counterexample = {
        "p_vector": [p_vec.get(k, 0) for k in range(3, kmax + 1)],
        **{f"p{k}": p_vec.get(k, 0) for k in range(3, kmax + 1)},
        "f2": props.get("f2", 0),
        "num_vertices": props.get("num_vertices", 0),
        "num_edges": props.get("num_edges", 0),
    }
    # persist the verified witness graph — makes the CE independently
    # re-checkable forever (render it with agent/orchestrator/tools/draw_ce_witness.py)
    witness_edges = ce_info.get("witness_edges")
    if witness_edges:
        counterexample["witness_graph"] = {
            "format": "edge_list",
            "num_vertices": 1 + max(max(e) for e in witness_edges),
            "edges": [list(e) for e in witness_edges],
        }

    payload = {
        "conjecture_id": conjecture.conjecture_id,
        "conjecture_latex": conjecture.statement_latex,
        "hypotheses": conjecture.hypotheses,
        "conclusion": conjecture.conclusion,
        "status": "failed",
        "counterexample": counterexample,
        "found_by": ce_info.get("found_by", "unknown"),
        "found_at_round": ce_info.get("found_at_round", -1),
        "violation_detail": ce_info.get("violation_detail", ""),
        "found_at": ce_info.get("found_at", datetime.now(timezone.utc).isoformat()),
        "other_candidates_not_checked": ce_info.get("other_candidates_not_checked", []),
    }
    out_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False))
    if witness_edges:
        try:
            from agent.orchestrator.tools.draw_ce_witness import render_witness
            png = render_witness(out_path)
            print(f"[Output] CE witness rendering → {png}")
        except Exception as exc:
            print(f"[Output] warning: witness rendering failed ({exc}) — "
                  f"JSON written without PNG")
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

    def run_from_name(
        self,
        conjecture_name: str,
        json_path: str | None = None,
        rl_episodes: int = 600,
        llm_rounds: int = 15,
    ) -> None:
        """Single-conjecture entry point by name."""
        conjecture = self._load_conjecture(conjecture_name, json_path)
        self.run(conjecture, rl_episodes=rl_episodes, llm_rounds=llm_rounds)

    def run(
        self,
        conjecture: ParsedConjecture,
        rl_episodes: int = 600,
        llm_rounds: int = 15,
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
            if ce_info.get("found_by") != "rl_agent":
                out_path = _write_ce_json(conjecture, ce_info, self._ce_dir)
                print(f"[Output] CE JSON → {out_path}")
        else:
            self._run_prover(conjecture)

    def run_batch(
        self,
        json_path: str | None = None,
        rl_episodes: int = 600,
        llm_rounds: int = 15,
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
        conjectures = self._load_all_conjectures(json_path)
        if not conjectures:
            print(f"[Batch] No conjectures found in {json_path or 'conjectures/conjectures.json'}")
            return

        print(f"\n[Batch] Loaded {len(conjectures)} conjecture(s) from {json_path or 'conjectures/conjectures.json'}")

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
        """Stage 1 walk, then Stage 2 (exhaustive screen → four parallel
        tracks). Returns validated CE info or None."""
        tag = f"[{conjecture.conjecture_id}{':' + label if label else ''}]"

        formula_str = conjecture_to_formula_string(conjecture)

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
            print(f"Counterexample found at round {rnd}: {p_vec} — {detail}")
            report = PVectorCheckAgent(client=self.client).run(p_vec, conjecture)
            if report.all_passed:
                pvec_result["violation_detail"] = detail
                pvec_result["witness_edges"] = report.witness_edges
                print(f"Counterexample validated at round {rnd}")
                return pvec_result
        print("[Stage 1] Random walk exhausted — no realizable CE. "
              "Proceeding to Stage 2 (unified CE search)...")

        # ── Stage 2: plantri exhaustive screen (no API, decisive) ─────────────
        plantri_finder = PlantriCEFinder(conjecture, client=self.client)
        enum_ce, survivors = plantri_finder.screen()
        if enum_ce:
            return enum_ce

        # ── Stage 2: LLM + RL + Hopper + constructor tracks in parallel ───────
        print(f"[Stage 2] Launching parallel CE searches — RL: {rl_episodes} "
              f"episodes  |  LLM: {llm_rounds} rounds  |  "
              f"Hopper: {'on' if _HOPPER_AVAILABLE else 'off'}  |  "
              f"plantri: {len(survivors)} undecided candidate(s)")

        # Unified stop signal and result queue shared across all four tracks.
        stop_event = _mp.Event()
        result_queue: _mp.Queue = _mp.Queue()

        # One torch thread each. Measured (seeded, identical 40-episode RL
        # run): the PPO/MLP tensors are so small that torch threading is pure
        # spin overhead — torch=1: 155s wall/1.0 cores, torch=4: 165s/4.0,
        # torch=10: 194s/9.8. More threads made RL 25% SLOWER while burning
        # ~10 cores, starving the sibling finder and the LLM tier-4 checks.
        _rl_threads = max(1, int(os.environ.get("RL_TORCH_THREADS", "1")))
        _hopper_threads = max(1, int(os.environ.get("HOPPER_TORCH_THREADS", "1")))

        # RL track (separate process — CPU-heavy, avoids GIL + PyTorch thread contention)
        rl_proc: _mp.Process | None = None
        if _RL_AVAILABLE and formula_str:
            rl_proc = _mp.Process(
                target=_rl_finder_process,
                args=(formula_str, conjecture.conjecture_id, rl_episodes,
                      result_queue, stop_event),
                kwargs={"conjecture": conjecture, "num_threads": _rl_threads},
                daemon=True,
                name=f"RL-{conjecture.conjecture_id}-{label}",
            )
            rl_proc.start()
        else:
            reason = _RL_IMPORT_ERR if not _RL_AVAILABLE else "formula conversion failed"
            print(f"[rl ce finding] disabled: {reason}")

        # Hopper track (separate process — CPU-heavy, avoids GIL + PyTorch thread contention)
        hopper_proc: _mp.Process | None = None
        if _HOPPER_AVAILABLE:
            hopper_proc = _mp.Process(
                target=_hopper_finder_process,
                args=(conjecture, 5_000, result_queue, stop_event),
                kwargs={"num_threads": _hopper_threads},
                daemon=True,
                name=f"Hopper-{conjecture.conjecture_id}-{label}",
            )
            hopper_proc.start()
        else:
            print(f"[Hopper ce finding] disabled: {_HOPPER_IMPORT_ERR}")

        # Constructor track (thread — its work runs in a spawn process pool).
        # One double-check sweep over every screen survivor; once it has
        # covered them all, the CE search is settled either way, so it stops
        # the remaining tracks.
        ctor_thread: threading.Thread | None = None
        if survivors:
            def _ctor_main() -> None:
                ce = plantri_finder.double_check(survivors, stop_event=stop_event)
                if ce:
                    result_queue.put(ce)
                    stop_event.set()
                elif plantri_finder.completed:
                    # Full double check with no CE — every undecided candidate
                    # got its attempt; further sampling is pointless.
                    stop_event.set()

            ctor_thread = threading.Thread(
                target=_ctor_main,
                daemon=True,
                name=f"Constructor-{conjecture.conjecture_id}-{label}",
            )
            ctor_thread.start()

        # LLM track (main thread — I/O bound, no CPU contention)
        check_agent = PVectorCheckAgent(client=self.client)
        llm_result = LLMCEFinder(
            conjecture=conjecture,
            client=self.client,
            num_rounds=llm_rounds,
            stop_event=stop_event,
            check_agent=check_agent,
            model=self.config.model_main,
        ).run()

        if llm_result:
            result_queue.put(llm_result)
            stop_event.set()

        # Wait for RL and Hopper processes to finish (they respect stop_event)
        if rl_proc and rl_proc.is_alive():
            rl_proc.join()
        if hopper_proc and hopper_proc.is_alive():
            hopper_proc.join()

        # Wait for the constructor's double check to finish — its verdict
        # settles the conjecture even after the samplers are exhausted.
        if ctor_thread is not None:
            ctor_thread.join()

        # Prefer the in-process LLM result directly: mp.Queue.put() returns
        # before the feeder thread flushes to the pipe, so get_nowait() can
        # miss even our own item (validated CE silently dropped).
        ce_info = llm_result
        if ce_info is None:
            try:
                ce_info = result_queue.get(timeout=3)
            except Exception:
                ce_info = None

        if not ce_info:
            print(f"[Stage 2] No CE found.")
            return None

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
                    if ce_info.get("found_by") != "rl_agent":
                        out_path = _write_ce_json(c, ce_info, self._ce_dir)
                        print(f"[Output] CE JSON → {out_path}")
                else:
                    no_ce.add(cid)

        print(f"{tag} finished")

    # ── Private helpers ────────────────────────────────────────────────────────

    def _ensure_polib_built(self) -> None:
        """Pre-build Polib.lean so its .olean cache exists for all subsequent lake calls."""
        import subprocess
        polib_path = Path(self.config.polib_path)
        olean = polib_path / ".lake" / "build" / "lib" / "lean" / "Polib.olean"
        if olean.exists():
            return
        print("[Orchestrator] Building Polib cache (first-time setup) …")
        result = subprocess.run(
            [self.config.lake_binary, "build", "Polib"],
            cwd=polib_path,
            capture_output=False,
            timeout=600,
            preexec_fn=set_pdeathsig,
        )
        if result.returncode == 0:
            print("[Orchestrator] Polib cache ready.")
        else:
            print(f"[Orchestrator] Warning: lake build Polib exited {result.returncode}")

    def _entailment_precheck(self, conjecture: ParsedConjecture) -> bool:
        """Return True if Stage 3 (prover) should run.

        A countermodel is a p-vector that satisfies the per-map arithmetic
        content of every Inventory.lean axiom yet violates the conjecture's
        conclusion. If one exists, no honest Lean proof of the conjecture can
        be derived from the current Inventory, so Stage 3 is skipped with an
        explicit verdict instead of burning prover rounds on an impossible
        task. Override with FORCE_PROVER=true.
        """
        from agent.orchestrator.tools.ce_enumerator import (
            enumerate_ce_candidates, inventory_countermodels,
        )
        try:
            candidates = enumerate_ce_candidates(conjecture)
            countermodels = inventory_countermodels(candidates)
        except Exception as exc:
            print(f"[Entailment pre-check] error: {exc} — proceeding with prover")
            return True

        if not countermodels:
            print("[Entailment pre-check] PASS — no Inventory countermodel within "
                  "bounds; formalization is plausible.")
            return True

        print(f"\n[Entailment pre-check] FAIL — conclusion is NOT entailed by Inventory.lean")
        print(f"  {len(countermodels)} p-vector(s) within bounds satisfy every Inventory "
              f"axiom (arithmetic content) yet violate the conclusion, e.g.:")
        for cm in countermodels[:3]:
            print(f"    {cm.p_vec}  (f2={cm.f2})")
        print("  Consequence: no honest Lean proof exists from the current Inventory.")

        # ── Automatic exhaustive decision of the countermodels via plantri ────
        # Resolves the FALSE-vs-TRUE dichotomy wherever the budget allows:
        #   realizable     → verified CE (proof by construction) → JSON written
        #   non-realizable → proof by exhaustion that no such map exists
        ce_info = self._decide_countermodels_with_plantri(conjecture, countermodels)
        if ce_info is not None:
            out_path = _write_ce_json(conjecture, ce_info, self._ce_dir)
            print(f"[Output] CE JSON → {out_path}")
            print("  Conjecture REFUTED by plantri exhaustive decision — skipping Stage 3.")
            return False

        print("  Either:")
        print("    1. the conjecture is FALSE — some undecided candidate above is a real")
        print("       CE (raise CE_PLANTRI_TIMEOUT / CE_PLANTRI_MAX to decide more), or")
        print("    2. the conjecture is TRUE — then Inventory needs new geometric")
        print("       content (hand-curated from a paper source; the prover must never")
        print("       invent it); more LLM retries cannot help.")
        if os.environ.get("FORCE_PROVER", "").lower() == "true":
            print("  FORCE_PROVER=true — running Stage 3 anyway.")
            return True
        print("  Skipping Stage 3. (set FORCE_PROVER=true to override)")
        return False

    def _decide_countermodels_with_plantri(
        self, conjecture: ParsedConjecture, countermodels: list
    ) -> Optional[dict]:
        """Exhaustively decide countermodel realizability with plantri
        (reuses agent/orchestrator/tools/plantri/decide_ce_plantri.decide — a decision procedure,
        not a heuristic). Returns CE info for the first realizable candidate,
        else None.

        Phases (all integer-numbered):
          1. CACHE TRIAGE — persistent verdict cache (output/realizability_
             cache.json), ADVISORY ONLY: non-realizable entries (proofs by
             exhaustion) skip work; the file can be deleted at any time;
          2. HINT RE-VERIFICATION — cached "realizable" entries are mere
             hints and are ALWAYS re-decided by a fresh plantri run before a
             CE is emitted, so a stale or tampered cache can never bypass the
             verification gate;
          3. QUICK triage — ALL remaining candidates in parallel with a short
             timeout (most small search spaces decide in seconds);
          4. DEEP — surviving (timed-out) candidates, cheapest first, with
             the full budget.
        The first validated realizable candidate sets a stop_event that kills
        every sibling plantri process immediately.

        Env knobs:
          CE_PLANTRI_QUICK_TIMEOUT  quick-phase seconds/candidate (default 30)
          CE_PLANTRI_TIMEOUT        deep-phase seconds/candidate (default 1800)
          CE_PLANTRI_PARALLEL       quick-phase concurrent candidates (default 8)
          CE_PLANTRI_PARALLEL_DEEP  deep-phase concurrent candidates (default 2)
          CE_PLANTRI_MAX            max deep-phase candidates (default 40; 0 disables stage)
        """
        try:
            from agent.orchestrator.tools.plantri.decide_ce_plantri import decide, PLANTRI_AD
        except Exception as exc:
            print(f"[Plantri decision] unavailable ({exc}) — skipping automatic decision")
            return None
        if not PLANTRI_AD.exists():
            print(f"[Plantri decision] binary missing at {PLANTRI_AD} — skipping")
            return None

        from concurrent.futures import ThreadPoolExecutor, as_completed

        cpu = _mp.cpu_count() or 8
        quick_t = float(os.environ.get("CE_PLANTRI_QUICK_TIMEOUT", "30"))
        deep_t = float(os.environ.get("CE_PLANTRI_TIMEOUT", "1800"))
        par_quick = max(1, int(os.environ.get("CE_PLANTRI_PARALLEL", "8")))
        par_deep = max(1, int(os.environ.get("CE_PLANTRI_PARALLEL_DEEP", "2")))
        max_deep = int(os.environ.get("CE_PLANTRI_MAX", "40"))
        if max_deep <= 0:
            print("[Plantri decision] disabled (CE_PLANTRI_MAX=0)")
            return None

        # ── persistent verdict cache ───────────────────────────────────────────
        cache_path = _PROJECT_ROOT / "output" / "realizability_cache.json"
        try:
            cache: dict = json.loads(cache_path.read_text()) if cache_path.exists() else {}
        except Exception:
            cache = {}
        cache_lock = threading.Lock()

        def _ckey(pv: dict[int, int]) -> str:
            return ",".join(f"{k}:{v}" for k, v in sorted(pv.items()))

        def _cache_put(pv: dict[int, int], verdict: str, count: int, t_used: float) -> None:
            with cache_lock:
                entry = cache.get(_ckey(pv), {})
                if entry.get("verdict") in ("realizable", "non_realizable"):
                    return  # final verdicts never change
                cache[_ckey(pv)] = {
                    "verdict": verdict, "count": count,
                    "timeout_used": round(max(t_used, entry.get("timeout_used", 0.0)), 1),
                }
                try:
                    cache_path.parent.mkdir(parents=True, exist_ok=True)
                    tmp = cache_path.with_suffix(".json.tmp")
                    tmp.write_text(json.dumps(cache, indent=1, sort_keys=True))
                    tmp.replace(cache_path)   # atomic — readers never see a partial file
                except Exception:
                    pass

        def _make_ce(c, count: int, round_i: int) -> Optional[dict]:
            violated, detail = _eval_conclusion_violated(conjecture.conclusion, c.p_vec)
            if not violated:
                print(f"    WARNING: {c.p_vec} realizable but conclusion not violated — "
                      f"enumerator inconsistency; ignoring")
                return None
            # re-derive an explicit witness graph for the CE JSON (the decide
            # script only returns a count); the realizable verdict is cached,
            # so the constructor's plantri early-exit finds it in seconds
            witness_edges = None
            try:
                import networkx as _nx
                from agent.orchestrator.tools.polytope_constructor import PolytopeConstructor
                G, _m = PolytopeConstructor().build(c.p_vec, timeout=120.0)
                if G is not None:
                    Gi = _nx.convert_node_labels_to_integers(G)
                    witness_edges = sorted(tuple(sorted(e)) for e in Gi.edges())
            except Exception:
                pass
            return {
                "p_vector": c.p_vec,
                "found_by": "plantri_exhaustive_decision",
                "found_at_round": round_i,
                "violation_detail": f"{detail} | plantri count={count} (exhaustive)",
                "witness_edges": witness_edges,
            }

        # cheapest first: few low-degree (3/4) dual vertices explode the search least
        cands = sorted(countermodels,
                       key=lambda c: (c.p_vec.get(3, 0) + c.p_vec.get(4, 0), c.f2))

        # ── exhaustive-reach filter ────────────────────────────────────────────
        # decide() has NO early exit — a verdict requires a COMPLETED plantri
        # enumeration, so a candidate beyond exhaustive reach is a guaranteed
        # timeout at any budget this stage spends (the C14 f2-cliff lesson).
        # Caps mirror the Stage-2 screen, +2 f2 margin because deep_t is ~20x
        # the screen budget (C2 data: roughly one f2 step per ~10x budget).
        f2cap_m5 = int(os.environ.get("PLANTRI_F2_MAX_M5", "36")) + 2
        f2cap_ad = int(os.environ.get("PLANTRI_F2_MAX", "26")) + 2

        def _within_reach(pv: dict[int, int]) -> bool:
            nz = {k: v for k, v in pv.items() if v > 0}
            if not nz:
                return False
            n = sum(nz.values())
            cap = f2cap_m5 if min(nz) >= 5 else f2cap_ad
            return 4 <= n <= cap and max(nz) <= n - 1

        # ── phase 1: cache triage ──────────────────────────────────────────────
        # Cached non-realizable verdicts (proofs by exhaustion) are skipped.
        # Cached "realizable" entries are HINTS ONLY: a CE is never emitted
        # from the cache — the candidate is re-decided by a fresh plantri run
        # in this process, so the verification gate cannot be bypassed by a
        # corrupted/stale cache file.
        n_non, n_hint_undecided, n_budget_exhausted, n_unreachable = 0, 0, 0, 0
        quick_list, deep_only, realizable_hints = [], [], []
        for c in cands:
            entry = cache.get(_ckey(c.p_vec))
            if entry is not None and entry["verdict"] == "realizable":
                # high-value hint — re-verify even if beyond the reach caps
                realizable_hints.append(c)
                continue
            if not _within_reach(c.p_vec):
                n_unreachable += 1
                continue
            if entry is None:
                quick_list.append(c)
            elif entry["verdict"] == "non_realizable":
                n_non += 1
            elif entry.get("timeout_used", 0.0) >= deep_t:
                n_budget_exhausted += 1   # full deep budget already spent — skip
            elif entry.get("timeout_used", 0.0) >= quick_t:
                deep_only.append(c)   # quick phase already proven insufficient
            else:
                quick_list.append(c)
        print(f"[Plantri decision] cache triage of {len(cands)} countermodel(s): "
              f"{len(quick_list)} fresh → quick, "
              f"{len(deep_only)} with >=quick budget spent → straight to deep, "
              f"{n_non} known non-realizable (skipped), "
              f"{n_budget_exhausted} deep-budget exhausted (skipped), "
              f"{n_unreachable} beyond exhaustive reach (skipped), "
              f"{len(realizable_hints)} realizable hint(s) to re-verify", flush=True)

        # ── phase 2: re-verify realizable hints first, full width, full budget ─
        for c in realizable_hints:
            print(f"[Plantri decision] cache hint REALIZABLE for {c.p_vec} — "
                  f"re-verifying with a fresh plantri run", flush=True)
            verdict, count, secs = decide(c.p_vec, cpu, deep_t)
            print(f"    {verdict.upper()} (count={count}) in {secs:.0f}s")
            if verdict == "realizable":
                ce = _make_ce(c, count, 0)
                if ce:
                    return ce
                n_hint_undecided += 1
            elif verdict == "non_realizable":
                print(f"    WARNING: stale/corrupt cache entry for {c.p_vec} "
                      f"(claimed realizable, exhaustion says no) — correcting")
                with cache_lock:
                    cache.pop(_ckey(c.p_vec), None)
                _cache_put(c.p_vec, "non_realizable", count, secs)
                n_non += 1
            else:
                n_hint_undecided += 1

        stop_event = threading.Event()

        def _run_phase(items: list, timeout: float, par: int, label: str,
                       verbose_each: bool):
            """Decide `items` concurrently. Returns (ce_info|None, survivors).

            verbose_each=False prints only ~3 aggregate milestone lines plus
            any REALIZABLE/error immediately (big quick batches would flood
            the log at one line per candidate); True prints every verdict
            (deep phase: one line every few minutes at most).
            """
            nonlocal n_non
            if not items:
                return None, []
            total = len(items)
            jobs_each = max(1, cpu // par)
            print(f"[Plantri decision/{label}] {total} candidate(s), "
                  f"{par} in parallel × {jobs_each} plantri jobs, {timeout:.0f}s each",
                  flush=True)
            milestones = {(total * k + 2) // 3 for k in (1, 2, 3)}
            ph_non, ph_timeout, ph_realized = 0, 0, 0
            t0 = time.time()
            survivors, found = [], None

            # Heartbeat: long-timeout phases can be silent for up to `timeout`
            # seconds between completions — print what is in flight every 5 min
            # so a quiet log is distinguishable from a hung one.
            inflight: dict[str, float] = {}
            ifl_lock = threading.Lock()
            n_done = 0
            hb_stop = threading.Event()

            def _decide_tracked(pv, jobs, t, ev):
                k = str(pv)
                with ifl_lock:
                    inflight[k] = time.time()
                try:
                    return decide(pv, jobs, t, ev)
                finally:
                    with ifl_lock:
                        inflight.pop(k, None)

            def _heartbeat():
                while not hb_stop.wait(300):
                    with ifl_lock:
                        now = time.time()
                        running = [f"{k} ({now - st:.0f}s)"
                                   for k, st in sorted(inflight.items())]
                    if running:
                        print(f"  [{label} heartbeat] {n_done}/{total} done | "
                              f"running: {', '.join(running)}", flush=True)

            hb_thread = None
            if timeout > 300:
                hb_thread = threading.Thread(target=_heartbeat, daemon=True)
                hb_thread.start()

            with ThreadPoolExecutor(max_workers=par) as ex:
                futs = {ex.submit(_decide_tracked, c.p_vec, jobs_each, timeout,
                                  stop_event): c
                        for c in items}
                for i, fut in enumerate(as_completed(futs), 1):
                    c = futs[fut]
                    n_done = i
                    try:
                        verdict, count, secs = fut.result()
                    except Exception as exc:
                        print(f"  [{label}] {c.p_vec} → worker error: {exc}", flush=True)
                        survivors.append(c)
                        continue
                    if verbose_each or verdict == "realizable":
                        print(f"  [{label} {i}/{total}] {c.p_vec} (f2={c.f2}) → "
                              f"{verdict.upper()} (count={count}) in {secs:.0f}s",
                              flush=True)
                    if verdict == "realizable":
                        ph_realized += 1
                        _cache_put(c.p_vec, "realizable", count, secs)
                        ce = _make_ce(c, count, i)
                        if ce and found is None:
                            found = ce
                            stop_event.set()   # kill all sibling plantri runs
                    elif verdict == "non_realizable":
                        ph_non += 1
                        _cache_put(c.p_vec, "non_realizable", count, secs)
                        n_non += 1
                    elif verdict == "timeout":
                        ph_timeout += 1
                        _cache_put(c.p_vec, "timeout", -1, timeout)
                        survivors.append(c)
                    else:  # stopped / error — undecided, not cached
                        survivors.append(c)
                    if not verbose_each and i in milestones:
                        print(f"  [{label} {i}/{total}] {ph_realized} realized, "
                              f"{ph_non} non-realizable, {ph_timeout} timeout "
                              f"({time.time() - t0:.0f}s elapsed)", flush=True)
            hb_stop.set()
            return found, survivors

        # ── phase 3: quick triage over everything ──────────────────────────────
        ce, survivors = _run_phase(quick_list, quick_t, par_quick, "quick",
                                   verbose_each=False)
        if ce:
            return ce

        # ── phase 4: deep decision on the hard ones, cheapest first ───────────
        deep_list = sorted(survivors + deep_only,
                           key=lambda c: (c.p_vec.get(3, 0) + c.p_vec.get(4, 0), c.f2))
        n_skipped = max(0, len(deep_list) - max_deep)
        ce, survivors = _run_phase(deep_list[:max_deep], deep_t, par_deep, "deep",
                                   verbose_each=True)
        if ce:
            return ce

        n_undecided = (len(survivors) + n_skipped + n_hint_undecided
                       + n_budget_exhausted + n_unreachable)
        if n_non == len(cands):
            print("[Plantri decision] ALL countermodels NON-REALIZABLE (proof by exhaustion).")
            print("  The conjecture survives within bounds, but remains unprovable from the")
            print("  current Inventory — it needs new, hand-curated geometric content.")
        else:
            reach_note = (f" — {n_unreachable} beyond exhaustive reach, raise "
                          f"PLANTRI_F2_MAX/_M5 to attempt" if n_unreachable else "")
            print(f"[Plantri decision] no CE realized: {n_non}/{len(cands)} non-realizable, "
                  f"{n_undecided} undecided (timeout/skipped{reach_note}). Verdicts cached in "
                  f"{cache_path.name}; raise CE_PLANTRI_TIMEOUT/CE_PLANTRI_MAX to decide more.")
        return None

    def _run_prover(self, conjecture: ParsedConjecture) -> str:
        """Run Stage 3 (prover). Returns 'proved', 'failed' or 'skipped_entailment'.
        (zero-sorry policy: a 'partial' prover result is NOT proved)."""
        from agent.prover.agent import ProverAgent

        if not self._entailment_precheck(conjecture):
            return "skipped_entailment"

        self._ensure_polib_built()

        agent = ProverAgent(self.config)
        agent._proof_subdir = "conjecture_without_ce"

        print(f"\n[Stage 3] ProverAgent starting for {conjecture.conjecture_id} …")
        try:
            result = agent.prove_conjecture(conjecture)
        except Exception as exc:
            print(f"[Orchestrator] ProverAgent raised: {exc}")
            raise

        if result.nodes_failed:
            print(f"  Failed nodes: {result.nodes_failed}")
        print(f"\n[Stage 3] Done. Result: {result.status}")
        return "proved" if result.status == "success" else "failed"

    def _load_all_conjectures(self, json_path: str | None = None) -> list[ParsedConjecture]:
        """Load every conjecture from a JSON file or directory of individual *.json files.

        Supports:
        - conjectures.json (array or {"unsolved": [...], "solved": [...]})
        - Directory of individual {name}.json files, each {"name": ..., "formula": ...}
        """
        source = Path(json_path) if json_path else _PROJECT_ROOT / "conjectures" / "conjectures.json"

        if source.is_file():
            specs = load_conjectures(str(source))
            return [ParsedConjecture.from_conjecture_spec(s) for s in specs]

        if source.is_dir():
            results: list[ParsedConjecture] = []
            for jf in sorted(source.glob("*.json")):
                try:
                    import json as _json
                    obj = _json.loads(jf.read_text())
                    name = obj.get("name") or jf.stem
                    formula = obj.get("formula", "")
                    if formula:
                        spec = ConjectureSpec(name=name, formula=formula)
                        results.append(ParsedConjecture.from_conjecture_spec(spec))
                except Exception:
                    continue
            return results

        raise FileNotFoundError(f"Cannot load conjectures from {source!r}")

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
        self, conjecture_name: str, json_path: str | None = None
    ) -> ParsedConjecture:
        """Load a single ParsedConjecture by name from a JSON source.

        Search order:
        1. Explicit json_path (file or directory)
        2. conjectures/individual/{name}.json
        3. conjectures/conjectures.json
        """
        import json as _json

        # 1. Explicit path
        if json_path:
            source = Path(json_path)
            if source.is_file():
                for spec in load_conjectures(str(source)):
                    if spec.name == conjecture_name:
                        return ParsedConjecture.from_conjecture_spec(spec)
            elif source.is_dir():
                jf = source / f"{conjecture_name}.json"
                if jf.exists():
                    obj = _json.loads(jf.read_text())
                    formula = obj.get("formula", "")
                    if formula:
                        return ParsedConjecture.from_conjecture_spec(
                            ConjectureSpec(name=conjecture_name, formula=formula)
                        )

        # 2. Individual file
        individual = _PROJECT_ROOT / "conjectures" / "individual" / f"{conjecture_name}.json"
        if individual.exists():
            obj = _json.loads(individual.read_text())
            formula = obj.get("formula", "")
            if formula:
                return ParsedConjecture.from_conjecture_spec(
                    ConjectureSpec(name=conjecture_name, formula=formula)
                )

        # 3. Main conjectures.json
        main_json = _PROJECT_ROOT / "conjectures" / "conjectures.json"
        if main_json.exists():
            for spec in load_conjectures(str(main_json)):
                if spec.name == conjecture_name:
                    return ParsedConjecture.from_conjecture_spec(spec)

        raise FileNotFoundError(
            f"Conjecture {conjecture_name!r} not found.\n"
            f"  Tried individual: {individual}\n"
            f"  Tried main JSON:  {main_json}"
        )


# ══════════════════════════════════════════════════════════════════════════════
# CLI entry point
# ══════════════════════════════════════════════════════════════════════════════

def main() -> None:
    p = argparse.ArgumentParser(
        description=(
            "Polytope conjecture orchestrator.\n\n"
            "Single mode:  --name auto_xxx\n"
            "Batch mode:   --batch\n"
            "Batch mode:   --batch --json conjectures/conjectures.json"
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )

    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--name", metavar="NAME",
                      help="Single conjecture name (e.g. auto_20260310_142638_1)")
    mode.add_argument("--batch", action="store_true",
                      help="Batch mode: process all conjectures with 7 parallel workers")

    p.add_argument("--json", default=None, metavar="PATH",
                   help="Path to conjectures JSON file or directory of individual *.json files "
                        "(default: conjectures/conjectures.json)")
    p.add_argument("--rl-episodes", type=int, default=600, metavar="N",
                   help="RL episodes per conjecture (default: 600)")
    p.add_argument("--llm-rounds", type=int, default=15, metavar="N",
                   help="LLM CE search rounds per conjecture (default: 15)")
    p.add_argument("--skip-ce", action="store_true",
                   help="Skip CE search and go directly to ProverAgent")
    args = p.parse_args()

    orch = Orchestrator()

    if args.batch:
        orch.run_batch(
            json_path=args.json,
            rl_episodes=args.rl_episodes,
            llm_rounds=args.llm_rounds,
        )
    else:
        if getattr(args, "skip_ce", False):
            conjecture = orch._load_conjecture(args.name, args.json)
            orch._run_prover(conjecture)
        else:
            orch.run_from_name(
                conjecture_name=args.name,
                json_path=args.json,
                rl_episodes=args.rl_episodes,
                llm_rounds=args.llm_rounds,
            )


if __name__ == "__main__":
    main()
