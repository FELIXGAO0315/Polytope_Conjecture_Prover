#!/usr/bin/env python3
"""
agent/orchestrator.py — Main pipeline orchestrator.

Given a conjecture name, runs two stages:
  Stage 1: p-vector lattice walk (fast, no API)
  Stage 2: LLM track (30 rounds) + RL track (600 episodes) in parallel

If either track finds a CE that passes validation:
  → output/conjecture_with_ce/{name}.json   (status=failed)

If neither finds one after both tracks exhaust:
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
import re
import threading
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

from agent.config import Config
from agent.claude_sdk import ClaudeSDKClient
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

try:
    from agent.rl_ce_finder.agent import train_on_conjecture as _agents_train_on_conjecture
    _RL2_AVAILABLE = True
    _RL2_IMPORT_ERR = ""
except Exception as _e2:
    _RL2_AVAILABLE = False
    _RL2_IMPORT_ERR = str(_e2)

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


def _rl2_finder_thread(
    formula: str,
    name: str,
    num_episodes: int,
    result_holder: list,
    lock: threading.Lock,
    ce_found_event: threading.Event,
    llm_stop_event: threading.Event,
    label: str = "",
    conjecture=None,
    check_agent=None,
    llm_finished_event: threading.Event | None = None,
) -> None:
    """Run RL CE finder, then validate each CE candidate with 4 checks."""
    tag = "[validation check ce from rl]"
    if not _RL2_AVAILABLE:
        print(f"{tag} disabled: {_RL2_IMPORT_ERR}")
        return

    agents_formula = _to_agents_formula(formula)

    try:
        result = _agents_train_on_conjecture(
            formula=agents_formula,
            name=name,
            num_episodes=num_episodes,
            exit_on_first_ce=False,
            stop_event=llm_stop_event,
        )
    except Exception as exc:
        print(f"{tag} train_on_conjecture raised: {exc}")
        return

    ces = result.get("counterexamples", [])
    if not ces:
        return

    # Wait for the LLM thread to finish printing its stop messages before
    # printing the validation header, so output ordering is deterministic.
    if llm_finished_event is not None:
        llm_finished_event.wait(timeout=5.0)

    print(f"{tag} {len(ces)} CE candidate(s) found, running 4 checks")

    from agent.orchestrator.tools.check_pvector import PVectorCheckAgent
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

        if checker and conjecture:
            report = checker.run_silent(p_vec, conjecture, rl_verified=True)
            for r in report.results:
                mark = "√" if r.passed else "✗"
                print(f"{tag} {mark} {r.label}: {r.detail}")
            if not report.all_passed:
                print(f"{tag} CE #{idx + 1}/{len(ces)}: not valid — proceed to next")
                continue

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
        }
        # Write CE JSON immediately — don't wait for main thread
        if conjecture:
            try:
                out_path = _write_ce_json(conjecture, ce_record, _PROJECT_ROOT / "output" / "conjecture_with_ce")
                print(f"{tag} The ce candidate is valid, saved  CE JSON → {out_path}")
            except Exception as exc:
                print(f"{tag} warning: could not write CE JSON: {exc}")
        with lock:
            if not ce_found_event.is_set():
                result_holder.append(ce_record)
                ce_found_event.set()
        return


# ══════════════════════════════════════════════════════════════════════════════
# Output writers
# ══════════════════════════════════════════════════════════════════════════════

def _write_ce_json(
    conjecture: ParsedConjecture, ce_info: dict, out_dir: Path
) -> Path:
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / f"{conjecture.short_id}.json"

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
        llm_rounds: int = 30,
    ) -> None:
        """Single-conjecture entry point by name."""
        conjecture = self._load_conjecture(conjecture_name, json_path)
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
            if ce_info.get("found_by") != "rl_agent":
                out_path = _write_ce_json(conjecture, ce_info, self._ce_dir)
                print(f"[Output] CE JSON → {out_path}")
        else:
            self._run_prover(conjecture)

    def run_batch(
        self,
        json_path: str | None = None,
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
        """Run parallel LLM + RL CE search. Returns validated CE info or None."""
        tag = f"[{conjecture.conjecture_id}{':' + label if label else ''}]"

        # ce_found_event: set only after a CE is validated and in result_holder
        # llm_stop_event: set when RL finds (unvalidated) CE — stops the LLM promptly
        ce_found_event = threading.Event()
        llm_stop_event = threading.Event()
        result_holder: list[dict] = []
        lock = threading.Lock()

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
            p6_val = p_vec.get(6, 0)
            print(f"Counterexample found at round {rnd}: "
                  f"{p_vec} — p6={p6_val:.1f} < {detail.split('<')[1].strip()}")
            report = PVectorCheckAgent(client=self.client).run(p_vec, conjecture)
            if report.all_passed:
                pvec_result["violation_detail"] = detail
                print(f"Counterexample validated at round {rnd}")
                return pvec_result
        print("Random walk exhausted, falling back to LLM + RL...")

        # ── Stage 2: LLM + agents/ RL in parallel ─────────────────────────────
        print(f"[Stage 2] RL episodes: {rl_episodes}  |  LLM rounds: {llm_rounds}")

        # Shared check_agent (LLM + RL share the same client)
        check_agent = PVectorCheckAgent(client=self.client)

        # llm_finished_event: set by the main thread once LLMCEFinder.run() returns,
        # so the RL validation thread can wait for LLM stop-messages to be printed.
        llm_finished_event = threading.Event()

        # RL track (daemon thread) — sets llm_stop_event on first CE find
        rl2_thread: threading.Thread | None = None
        if _RL2_AVAILABLE and formula_str:
            rl2_thread = threading.Thread(
                target=_rl2_finder_thread,
                args=(formula_str, conjecture.conjecture_id, rl_episodes,
                      result_holder, lock, ce_found_event, llm_stop_event, label),
                kwargs={"conjecture": conjecture, "check_agent": check_agent,
                        "llm_finished_event": llm_finished_event},
                daemon=True,
                name=f"RL2-{conjecture.conjecture_id}-{label}",
            )
            rl2_thread.start()
        else:
            reason = _RL2_IMPORT_ERR if not _RL2_AVAILABLE else "formula conversion failed"
            print(f"[rl ce finding] disabled: {reason}")

        # LLM track (this thread) — stops when llm_stop_event is set
        llm_result = LLMCEFinder(
            conjecture=conjecture,
            client=self.client,
            num_rounds=llm_rounds,
            stop_event=llm_stop_event,
            check_agent=check_agent,
            model=self.config.model_main,
        ).run()

        # Signal the RL thread that LLM output is complete.
        llm_finished_event.set()

        if llm_result:
            with lock:
                if not ce_found_event.is_set():
                    result_holder.append(llm_result)
                    ce_found_event.set()
                    llm_stop_event.set()

        # Always wait for RL thread — it may still be running the validator
        if rl2_thread and rl2_thread.is_alive():
            rl2_thread.join()

        if not result_holder:
            print(f"[Stage 2] No CE found.")
            return None

        ce_info = result_holder[0]
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
        )
        if result.returncode == 0:
            print("[Orchestrator] Polib cache ready.")
        else:
            print(f"[Orchestrator] Warning: lake build Polib exited {result.returncode}")

    def _run_prover(self, conjecture: ParsedConjecture) -> None:
        from agent.prover.agent import ProverAgent

        self._ensure_polib_built()
        print(f"\n[Orchestrator] ProverAgent starting for {conjecture.conjecture_id} …")
        agent = ProverAgent(self.config)
        # Route ProverAgent output directly into conjecture_without_ce/
        agent._proof_subdir = "conjecture_without_ce"

        try:
            result = agent.prove_conjecture(conjecture)
        except Exception as exc:
            print(f"[Orchestrator] ProverAgent raised: {exc}")
            raise

        print(f"\n[Orchestrator] Done. Result: {result.status}")

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
    p.add_argument("--llm-rounds", type=int, default=30, metavar="N",
                   help="LLM CE search rounds per conjecture (default: 30)")
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
