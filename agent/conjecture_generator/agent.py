"""
agent/conjecture_generator/agent.py — Graffiti3 + LLM conjecture generator.

Discovers new p6-bound conjectures and registers them into
conjectures/conjectures.json with status='new' (the evolution loop only ever
runs 'new' entries).

Candidate sources (ALL pass the SAME hard filter — no source is trusted):
  - Graffiti3: data-driven LP fitting on the verified-polytope table —
    fixed classical strata PLUS dynamic cells rotated through the registry's
    uncovered hypothesis combinations, so the LP attacks fresh territory
    every run instead of replaying itself.
  - Mutation engine (tools/mutations.py): repairs refuted bounds past their
    CEs, sharpens slack proved bounds to pool contact, weakens hypotheses of
    proved theorems — new conjectures BUILT FROM existing outcomes; the pool
    of sources grows with every result, so this never dries up.
  - LLM (optional, when `client` is given): proposes formulas directly,
    guided by signals DERIVED from conjectures.json + registry + artifacts
    (proved = primary, refuted = gatekeeper, prover-stuck/survivor = mimic),
    with explicit mutation directives and the round's focus cells.

Hard filter, identical for every candidate:
  1. must render/parse in the project DSL and be evaluable by pvec_eval
  2. must hold on every pipeline-verified realizable p-vector
  3. dedup: in-batch + against conjectures.json (all three buckets)

When `client` is given, an LLM review pass (keep/drop, signal-aware) runs
AFTER the hard filter. Signals influence generation only — never CE finding
or any verification gate.

Standalone:  python -m agent.conjecture_generator [--dry-run] [--limit N] …
"""
from __future__ import annotations

import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

from agent.conjectures import (
    ConjectureSpec,
    canonicalize_formula,
    load_conjecture_dataset,
    reconcile_from_artifacts,
    upsert_conjectures,
)
from agent.conjecture_generator.prompts.conjecture_generator import (
    CONJ_GEN_PROPOSE_PROMPT,
    CONJ_GEN_REVIEW_PROMPT,
    CONJ_GEN_SYSTEM,
)
from agent.conjecture_generator.tools.dataset import (
    NUMERIC_COLS,
    build_discovery_table,
    format_pvec_for_prompt,
    select_representative_pvecs,
)
from agent.conjecture_generator.tools.signals import (
    derive_signals,
    format_hint_block,
)
from agent.conjecture_generator.tools.iris_scoring import compute_iris
from agent.conjecture_generator.tools.mutations import generate_mutations
from agent.conjecture_generator.tools.support_miner import mine_support_bounds
from agent.conjecture_generator.tools.render import render_txgraffiti_conjecture
from agent.conjectures import load_iris_scores
from agent.llm_ce_finder.agent import _extract_json_from_text
from agent.orchestrator.tools.conjecture_parser import ParsedConjecture
from agent.orchestrator.tools.pvec_eval import (
    _compile_conclusion,
    _eval_conclusion_violated,
    _eval_hypothesis,
)

_PROJECT_ROOT = Path(__file__).resolve().parents[2]
_RUN_LOG_DIR = _PROJECT_ROOT / "output" / "conjecture_generator"


class ConjectureGenerator:
    """Discovers conjectures (Graffiti3 + optional LLM) and registers the
    survivors with status='new'."""

    def __init__(
        self,
        client=None,              # ClaudeSDKClient — enables LLM propose + review
        limit: int = 0,           # max accepted conjectures (0 = keep all)
        g3_mode: str = "fast",    # fast | standard | deep
        quick: bool = True,
        linear_only: bool = True,
        enable_sophie: bool = False,
        llm_propose_n: int = 12,  # how many formulas to ask the LLM for
        dry_run: bool = False,    # discover + filter, but do not write anything
        propose_model: str | None = None,  # Haiku via fast_model path; falls back
                                           # to client.model on retry
        review_model: str | None = None,   # Sonnet (or any main model); None = client.model
    ) -> None:
        self.client = client
        self.limit = limit
        self.g3_mode = g3_mode
        self.quick = quick
        self.linear_only = linear_only
        self.enable_sophie = enable_sophie
        self.llm_propose_n = llm_propose_n
        self.propose_model = propose_model
        self.review_model = review_model
        self.dry_run = dry_run
        self.model = getattr(client, "model", None)

    # ── main entry ────────────────────────────────────────────────────────────

    def run(self) -> list[ConjectureSpec]:
        """Discover, filter, dedup, register. Returns the registered specs."""
        print("[conjecture generator] start generating…", flush=True)
        table, row_pvecs, hyp_cols = build_discovery_table()
        print(f"[conjecture generator] discovery table: {len(table)} rows, "
              f"{len(hyp_cols)} hypothesis column(s)", flush=True)

        # Hard-gate dataset: the FULL verified pool, NOT the stratified LP
        # sample. The sample (60 rows per f_2 bucket) exists to bound
        # Graffiti3's LP cost; the consistency gate has no such excuse —
        # C133 and the recycled C137 (2026-07-02) both passed the sampled
        # gate and were refuted minutes later by Stage 0's full-pool replay,
        # wasting a full CE-search cycle each. Same rows Stage 0 scans.
        gate_pvecs = row_pvecs
        try:
            from agent.conjecture_generator.tools.dataset import load_verified_pvecs
            seen: set[tuple] = set()
            gate_pvecs = []
            for pv in row_pvecs + [rec["p_vec"] for rec in load_verified_pvecs()]:
                key = tuple(sorted(pv.items()))
                if key not in seen:
                    seen.add(key)
                    gate_pvecs.append(pv)
            print(f"[conjecture generator] pool gate armed with "
                  f"{len(gate_pvecs)} verified p-vector(s) (full pool)",
                  flush=True)
        except Exception as exc:
            print(f"[conjecture generator] full-pool load failed ({exc}) — "
                  f"gate falls back to the {len(row_pvecs)}-row sample",
                  flush=True)

        # Full-table pass — the historical behavior. LP sees every hypothesis
        # column (including structural ones from dataset.py) and may pick any.
        discovered = self._discover(table) or []
        if not discovered:
            core = [c for c in ["is_simple"] + NUMERIC_COLS if c in table.columns]
            print(f"[conjecture generator] 0 raw conjectures; retrying with core "
                  f"columns only ({core})", flush=True)
            discovered = self._discover(table[core]) or []
        print(f"[conjecture generator] Graffiti3 full-table pass: "
              f"{len(discovered)} raw conjecture(s)", flush=True)

        # Stratified passes — force LP to find bounds CONDITIONED on classical
        # structural assumptions (Eberhard / Jučovič / Grünbaum strata). On the
        # full table LP almost always prefers `f_2 >= N` because it's tighter
        # globally, so the conditional bounds that mathematicians actually
        # study never surface. By filtering the table to each stratum and
        # appending the stratum predicate to every formula's LHS we get one
        # LP fit per classical sub-class. These return ALREADY-RENDERED
        # formulas (predicate injection happens inside) and are merged into
        # `candidates` further down.
        stratified_formulas = self._discover_stratified(table)

        # Fold any pipeline outcomes still sitting only on disk into
        # conjectures.json, THEN derive prompt signals — the generator always
        # sees the latest proved/refuted/stuck truth even when the prover ran
        # through an entry point that skipped status sync.
        reconcile_from_artifacts()
        signals = derive_signals()
        print(f"[conjecture generator] signals: "
              f"{len(signals['proved'])} proved, "
              f"{len(signals['refuted'])} refuted, "
              f"{len(signals['prover_stuck'])} prover-stuck, "
              f"{len(signals['survivor'])} survivor(s)", flush=True)
        existing_unsolved, existing_failed, existing_proved = load_conjecture_dataset()
        existing_all = existing_unsolved + existing_failed + existing_proved
        known_formulas = {canonicalize_formula(s.formula) for s in existing_all}
        # IRIS scores for the LLM's "already registered" template signal.
        existing_iris = load_iris_scores()

        # ── gather candidates from all sources ────────────────────────────────
        # Shape fingerprints of refuted formulas are no longer a HARD drop.
        # With the gate armed with the full pool (every CE witness included),
        # an exact sibling re-fit dies on its own counterexample, while a
        # candidate that clears every known CE is a genuine repair — the
        # dalmatian dynamic the old hard filter blocked. What remains of the
        # filter: a shape-repeat must TOUCH the pool hull (min slack = 0),
        # so only extremal repairs get through, not slack near-duplicates.
        # Shapes that appear among proved theorems are exempt entirely.
        proved_shapes = {self._formula_shape(e.get("formula", ""))
                         for e in signals["proved"]}
        failure_shapes = {self._formula_shape(e.get("formula", ""))
                          for e in signals["refuted"]}
        failure_shapes -= proved_shapes
        failure_shapes.discard(None)

        candidates: list[tuple[str, str]] = []   # (formula, source)
        rejected: list[dict] = []
        for obj in discovered:
            formula = render_txgraffiti_conjecture(obj)
            if not formula:
                rejected.append({"raw": _safe_repr(obj), "source": "graffiti3",
                                 "reason": "render_failed"})
                continue
            candidates.append((self._simplify_hypothesis_clause(formula),
                               "graffiti3"))
        for formula, src_tag in stratified_formulas:
            candidates.append((self._simplify_hypothesis_clause(formula),
                               src_tag))

        # Dynamic-cell pass — Graffiti3 aimed at uncovered hypothesis cells.
        # Coverage counts only ALIVE conjectures (unsolved + proved): a cell
        # whose every registered formula was refuted is open territory again
        # — its boundary deserves a re-fit against the grown pool. Rotation
        # is seeded by the FULL registry size so it advances every
        # productive generation even while the alive count stands still.
        alive_specs = existing_unsolved + existing_proved
        focus_cells = self._dynamic_cells(alive_specs, table,
                                          seed=len(existing_all))
        if focus_cells:
            print(f"[conjecture generator] dynamic cells this round: "
                  + ", ".join(lbl for lbl, *_ in focus_cells), flush=True)
            for formula, src_tag in self._discover_stratified(
                    table, strata=focus_cells, tag="cell"):
                candidates.append((self._simplify_hypothesis_clause(formula),
                                   src_tag))

        # Mutation engine — new conjectures BUILT FROM existing outcomes.
        mutated = generate_mutations(signals, gate_pvecs)
        if mutated:
            print(f"[conjecture generator] mutation engine proposed "
                  f"{len(mutated)} candidate(s) from existing outcomes",
                  flush=True)
        for formula, src_tag in mutated:
            candidates.append((self._simplify_hypothesis_clause(formula),
                               src_tag))

        # Support-function miner — systematically sweeps the tight lower-hull
        # bounds (the C104 class: DS-forced hexagon lower bounds on
        # small-face-starved cells) that dalmatian LP surfaces only by
        # accident. Tight + pool-consistent by construction; known formulas
        # are excluded up front so it always probes NEW edges.
        mined = mine_support_bounds(gate_pvecs, known_formulas)
        if mined:
            print(f"[conjecture generator] support miner proposed "
                  f"{len(mined)} tight lower bound(s)", flush=True)
        for formula, src_tag in mined:
            candidates.append((self._simplify_hypothesis_clause(formula),
                               src_tag))
        # Verified-pool witness sample fed into BOTH propose and review prompts
        # — diverse cross-section the LLM can mentally do CE checks against.
        verified_sample = select_representative_pvecs(row_pvecs)
        verified_block = "\n".join(
            f"  - {format_pvec_for_prompt(pv)}" for pv in verified_sample
        ) or "  (no verified p-vectors available)"

        if self.client is not None:
            focus_block = "\n".join(
                f"  - {pred}" for _, pred, _, _ in focus_cells
            ) or "  (none — every cell with data already has conjectures)"
            for formula in self._llm_propose(signals, existing_all,
                                             existing_iris, len(table),
                                             verified_block=verified_block,
                                             focus_block=focus_block,
                                             row_pvecs=row_pvecs):
                candidates.append((formula, "llm"))

        # ── hard filter — identical for every source ──────────────────────────
        # Per-candidate accept/reject details are saved to the run-log JSON
        # (see _write_run_log); stdout shows only the aggregate counts at the
        # end so the orchestrator log stays readable.
        accepted: list[tuple[str, str]] = []
        n_shape_slack = 0
        for idx, (formula, source) in enumerate(candidates, start=1):
            norm = canonicalize_formula(formula)
            if norm in known_formulas:
                rejected.append({"formula": norm, "source": source,
                                 "reason": "duplicate"})
                continue
            ok, why, min_slack = self._consistent_with_verified(norm, gate_pvecs)
            if not ok:
                rejected.append({"formula": norm, "source": source, "reason": why})
                continue
            # Shape-repeat tightness rule (replaces the old hard shape drop):
            # a candidate matching a refuted shape is admitted ONLY when it
            # touches the pool hull — an extremal repair, not a slack sibling.
            shape = self._formula_shape(norm)
            if (shape is not None and shape in failure_shapes
                    and not (min_slack is not None and min_slack <= 1e-9)):
                n_shape_slack += 1
                rejected.append({"formula": norm, "source": source,
                                 "reason": ("shape_repeat_not_tight: matches a "
                                            "refuted shape and is slack on the "
                                            "pool — a repair must touch the hull")})
                continue
            known_formulas.add(norm)
            accepted.append((norm, source))
            if self.limit and len(accepted) >= self.limit:
                break
        if n_shape_slack:
            print(f"[conjecture generator] tightness rule dropped {n_shape_slack} "
                  f"slack shape-repeat(s)", flush=True)
        print(f"[conjecture generator] pool gate: {len(accepted)} kept, "
              f"{len(candidates) - len(accepted)} dropped", flush=True)

        # ── Deterministic LP-overfit filter (runs before LLM review so the
        # reviewer sees a slimmer batch and is less likely to time out).
        # Any RHS coefficient with denominator > 6 is treated as LP overfit;
        # Lean-friendly denominators are {1, 2, 3, 6} per the propose prompt.
        accepted, overfit_drops = self._drop_lp_overfit(accepted, max_denom=6)
        rejected.extend(overfit_drops)

        # ── Trivial-RHS guard. `p6 >= K` for K ≤ 0 is vacuous (p6 is always
        # a non-negative integer), so the bound carries no information. We
        # also drop empty RHS or pure-zero RHS. Upper bounds `p6 <= K` for
        # tiny constant K with no LHS structure are similarly weak but rarely
        # vacuous in practice, so we only catch the K ≤ 0 case there too
        # (negative ceilings are unsatisfiable, hence "vacuous as a Lean
        # target" — registering them would burn CE / prover cycles).
        accepted, trivial_drops = self._drop_trivial_rhs(accepted)
        rejected.extend(trivial_drops)

        # ── Semantic-duplicate filter: same hypotheses + same arithmetic
        # CE-candidate set as an alive conjecture ⇒ same attack surface,
        # regardless of RHS coefficients (C193 ≡ C199 lesson, 2026-07-04).
        accepted, semdup_drops = self._drop_semantic_dupes(accepted, alive_specs)
        rejected.extend(semdup_drops)

        # ── LLM review (advisory keep/drop, after the hard filter) ────────────
        if self.client is not None and accepted:
            accepted, review_drops = self._llm_review(accepted, signals,
                                                     verified_block=verified_block)
            rejected.extend(review_drops)

        run_ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        specs = self._assign_names([f for f, _ in accepted], run_ts,
                                   existing_all)
        sources = {spec.formula: src for spec, (_, src) in zip(specs, accepted)}
        print(f"[conjecture generator] accepted {len(specs)}, "
              f"rejected {len(rejected)}", flush=True)

        # IRIS scoring on the verified pool. Survivors already pass the hard
        # filter (consistent on every row_pvec), so support ≥ 1 and compute_iris
        # should succeed; we still tolerate None defensively.
        iris_by_name: dict[str, dict] = {}
        for s in specs:
            iris = compute_iris(s, row_pvecs)
            if iris is not None:
                iris_by_name[s.name] = iris
        if specs:
            scored = len(iris_by_name)
            print(f"[conjecture generator] IRIS scored {scored}/{len(specs)} "
                  f"on {len(row_pvecs)} verified p-vector(s)", flush=True)
            # Soft warning: TRL≈0 means no touching points on the pool —
            # bound is loose (won't refute) and useless as a Lean target.
            # We don't gate, but flag so the user knows what's worth tracing.
            DEGEN = 1e-4
            for s in specs:
                trl = ((iris_by_name.get(s.name) or {})
                       .get("sort_keys", {}).get("TRL", 0.0) or 0.0)
                if trl < DEGEN:
                    print(f"[conjecture generator] WARNING degenerate IRIS "
                          f"(TRL={trl:.2e} < {DEGEN:.0e}) {s.name}: "
                          f"{s.formula}", flush=True)

        if self.dry_run:
            print("[conjecture generator] dry run — nothing written")
            for s in specs:
                iris = iris_by_name.get(s.name)
                tag = (f"  iris T={iris['T']:.3f} R={iris['R']:.3f} "
                       f"L={iris['L']:.3f}" if iris else "  iris=unavailable")
                print(f"  would register {s.name}: {s.formula}\n{tag}")
            return specs

        if specs:
            inserted = upsert_conjectures(specs, iris_by_name=iris_by_name)
            print(f"[conjecture generator] conjectures stored with status=new "
                  f"({len(inserted)})", flush=True)
        self._write_run_log(run_ts, specs, sources, rejected, len(table))
        return specs

    # ── discovery: Graffiti3 ──────────────────────────────────────────────────

    def _discover(self, table) -> Optional[list]:
        try:
            from txgraffiti.graffiti3.graffiti3 import Graffiti3, Mode, Stage
            from txgraffiti.graffiti3.heuristics.dalmatian import dalmatian_filter
            from txgraffiti.graffiti3.heuristics.morgan import morgan_filter
        except Exception as exc:
            print(f"[conjecture generator] txgraffiti unavailable ({exc}) — "
                  f"pip install txgraffiti", flush=True)
            return None

        # p6-only: this repo's downstream (render, pvec_eval, prover, prompts)
        # is centred on p6 bounds. Other LHS forms render_failed at >95% in the
        # last run; reinstate them only when render.py + pvec_eval grow proper
        # non-p6 LHS support.
        targets = [c for c in ["p_6", "p6"] if c in table.columns]
        if not targets:
            print("[conjecture generator] no target columns in table", flush=True)
            return None

        mode_enum = {"fast": Mode.FAST, "standard": Mode.STANDARD,
                     "deep": Mode.DEEP}.get(self.g3_mode.lower(), Mode.FAST)
        stages = [Stage.CONSTANT, Stage.LP1, Stage.LP2, Stage.LP3, Stage.LP4]
        if not self.linear_only:
            stages.extend([
                Stage.POLY_SINGLE, Stage.MIXED, Stage.SQRT, Stage.LOG,
                Stage.SQRT_LOG, Stage.GEOM_MEAN, Stage.LOG_SUM,
                Stage.SQRT_PAIR, Stage.SQRT_SUM, Stage.EXP_EXPONENT,
            ])
        try:
            g3 = Graffiti3(
                table,
                max_boolean_arity=2,
                morgan_filter=morgan_filter,
                dalmatian_filter=dalmatian_filter,
                sophie_cfg=dict(
                    eq_tol=1e-4,
                    min_target_support=5,
                    min_h_support=3,
                    max_violations=0,
                    min_new_coverage=1,
                ),
            )
            result = g3.conjecture(
                targets=targets,
                stages=stages,
                mode=mode_enum,
                include_invariant_products=False,
                include_abs=False,
                include_min_max=False,
                include_log=False,
                enable_sophie=self.enable_sophie,
                sophie_stages=stages,
                quick=self.quick,
                show=False,
            )
            return list(result.conjectures)
        except Exception as exc:
            print(f"[conjecture generator] Graffiti3 discovery failed ({exc})",
                  flush=True)
            return None

    # ── discovery: stratified Graffiti3 (classical sub-classes) ──────────────

    # Stratum definition: (label, predicate-injected-into-LHS, row-mask-fn,
    # columns-to-drop-from-LP). Dropped columns are the ones whose value is
    # constant on the stratum — keeping them would make the LP either pick a
    # tautology (e.g. `(p_3 = 0)` when every row already has p_3 = 0) or be
    # vacuously satisfied.
    _STRATA: list[tuple[str, str, str, list[str]]] = [
        # label,        DSL predicate,     filter,                drop columns
        ("p3_eq_0",     "(p_3 = 0)",       "p_3 == 0",            ["p3_eq_0", "p3_eq_0_and_p4_eq_0", "p3_le_2"]),
        ("p4_eq_0",     "(p_4 = 0)",       "p_4 == 0",            ["p4_eq_0", "p3_eq_0_and_p4_eq_0", "p4_eq_0_and_p5_eq_0", "p4_le_2"]),
        ("p5_eq_0",     "(p_5 = 0)",       "p_5 == 0",            ["p5_eq_0", "p4_eq_0_and_p5_eq_0", "p5_le_2"]),
        ("p3=0_p4=0",   "(p_3 = 0) and (p_4 = 0)",
                                            "(p_3 == 0) & (p_4 == 0)",
                                            ["p3_eq_0", "p4_eq_0", "p3_eq_0_and_p4_eq_0",
                                             "p4_eq_0_and_p5_eq_0", "p3_le_2", "p4_le_2"]),
        ("p4=0_p5=0",   "(p_4 = 0) and (p_5 = 0)",
                                            "(p_4 == 0) & (p_5 == 0)",
                                            ["p4_eq_0", "p5_eq_0", "p4_eq_0_and_p5_eq_0",
                                             "p3_eq_0_and_p4_eq_0", "p4_le_2", "p5_le_2"]),
        ("p3_le_2",     "(p_3 <= 2)",      "p_3 <= 2",            ["p3_le_2", "p3_eq_0"]),
    ]

    # Minimum rows required to attempt LP on a stratum — below this the LP
    # over-fits to a handful of corner polytopes and emits 9/14-style
    # coefficients that the overfit guard will reject anyway.
    _STRAT_MIN_ROWS = 60

    # Max formulas to keep per stratum. Without this, large strata
    # (`p_3 <= 2` covers ≈ 1500 / 1553 rows) crowd out the rare-but-precious
    # strata (`p_3 = 0 ∧ p_4 = 0` typically produces 1–3 distinct formulas).
    # Picking 12 matches the per-pass cap of the dense strata (`p_3 = 0`,
    # `p_4 = 0`) so the merged candidate pool stays balanced across
    # classical families. The LP-overfit + trivial-RHS guards remain in
    # effect downstream, so 12 is an upper bound — many strata return
    # fewer naturally.
    _STRAT_PER_STRATUM_CAP = 12

    def _discover_stratified(self, table, strata=None,
                             tag: str = "strat") -> list[tuple[str, str]]:
        """Run Graffiti3 on each structural stratum; return (formula, source)
        pairs already rendered with the stratum predicate injected into the
        hypothesis clause. The full-table pass is the historical one and runs
        separately; this is purely additive.

        ``strata`` defaults to the fixed classical list (_STRATA); the
        dynamic-cell pass feeds computed strata through the same machinery
        with ``tag='cell'``."""
        out: list[tuple[str, str]] = []
        # The stratum row-masks rely on raw p_3, p_4, p_5 (+ the big-face
        # sum) — pull them from the numeric columns dataset.py always keeps.
        try:
            p3 = table["p_3"].astype(int)
            p4 = table["p_4"].astype(int)
            p5 = table["p_5"].astype(int)
            s7 = table["sum_pk_k>=7"].astype(int)
        except Exception as exc:
            print(f"[conjecture generator] stratified discovery skipped "
                  f"(p_k columns missing: {exc})", flush=True)
            return []

        for label, predicate, mask_expr, drop_cols in (strata or self._STRATA):
            # Evaluate the filter using the bound locals — `eval` here is
            # constrained to the {p_3, p_4, p_5, s7} aliases we control.
            try:
                mask = eval(mask_expr,
                            {"__builtins__": {}},
                            {"p_3": p3, "p_4": p4, "p_5": p5, "s7": s7})
            except Exception as exc:
                print(f"[conjecture generator] stratum {label!r} mask failed "
                      f"({exc}); skipping", flush=True)
                continue
            sub = table.loc[mask].copy()
            n_rows = len(sub)
            if n_rows < self._STRAT_MIN_ROWS:
                print(f"[conjecture generator] stratum {label!r}: {n_rows} "
                      f"rows < {self._STRAT_MIN_ROWS} — skipped", flush=True)
                continue
            # Drop columns that are constant on the stratum (would let LP
            # pick a tautological predicate or duplicate the stratum's own
            # condition).
            for col in drop_cols:
                if col in sub.columns:
                    sub.drop(columns=[col], inplace=True)
            print(f"[conjecture generator] stratum {label!r}: {n_rows} rows, "
                  f"{len([c for c in sub.columns if c not in NUMERIC_COLS])} "
                  f"hypothesis col(s) — running Graffiti3", flush=True)
            objs = self._discover(sub) or []
            stratum_out: list[tuple[str, str]] = []
            seen_in_stratum: set[str] = set()
            for obj in objs:
                base = render_txgraffiti_conjecture(obj)
                if not base:
                    continue
                injected = self._inject_predicate(base, predicate)
                if not injected:
                    continue
                # Within-stratum dedup: LP often emits structurally identical
                # bounds at different rounding precisions; canonicalize then
                # uniq before applying the cap so the cap selects DISTINCT
                # formulas rather than the first N near-duplicates.
                canon = canonicalize_formula(injected)
                if canon in seen_in_stratum:
                    continue
                seen_in_stratum.add(canon)
                stratum_out.append((canon, f"graffiti3:{tag}:{label}"))
                if len(stratum_out) >= self._STRAT_PER_STRATUM_CAP:
                    break
            out.extend(stratum_out)
            print(f"[conjecture generator]   → {len(stratum_out)} formula(s) "
                  f"rendered from stratum {label!r} "
                  f"(cap={self._STRAT_PER_STRATUM_CAP})", flush=True)
        return out

    # ── dynamic cells: uncovered hypothesis combinations ──────────────────────

    # Atom menu for cell construction: (key, DSL predicate, mask expr over
    # {p_3, p_4, p_5, s7}, coverage regex, structural cols to drop).
    _CELL_ATOMS: list[tuple[str, str, str, str, list[str]]] = [
        ("p3=0",  "(p_3 = 0)",             "p_3 == 0", r"p_3\s*=\s*0(?!\d)",
         ["p3_eq_0", "p3_eq_0_and_p4_eq_0", "p3_le_2"]),
        ("p4=0",  "(p_4 = 0)",             "p_4 == 0", r"p_4\s*=\s*0(?!\d)",
         ["p4_eq_0", "p3_eq_0_and_p4_eq_0", "p4_eq_0_and_p5_eq_0", "p4_le_2"]),
        ("p5=0",  "(p_5 = 0)",             "p_5 == 0", r"p_5\s*=\s*0(?!\d)",
         ["p5_eq_0", "p4_eq_0_and_p5_eq_0", "p5_le_2"]),
        ("p3<=2", "(p_3 <= 2)",            "p_3 <= 2", r"p_3\s*<=\s*2",
         ["p3_le_2"]),
        ("p4<=2", "(p_4 <= 2)",            "p_4 <= 2", r"p_4\s*<=\s*2",
         ["p4_le_2"]),
        ("p5<=2", "(p_5 <= 2)",            "p_5 <= 2", r"p_5\s*<=\s*2",
         ["p5_le_2"]),
        ("s7>=3", "(sum_pk_k>=7 >= 3)",    "s7 >= 3",  r"sum_pk_k>=7\s*>=\s*3",
         [f"sum_pk_k>=7_at_least_{i}" for i in range(1, 4)]),
        ("s7>=5", "(sum_pk_k>=7 >= 5)",    "s7 >= 5",  r"sum_pk_k>=7\s*>=\s*5",
         [f"sum_pk_k>=7_at_least_{i}" for i in range(1, 6)]),
    ]

    _DYNAMIC_CELLS_PER_RUN = 3

    def _dynamic_cells(self, existing_specs: list[ConjectureSpec],
                       table, seed: int = 0,
                       ) -> list[tuple[str, str, str, list[str]]]:
        """Uncovered atom-pair cells, ranked by table support, rotated by
        `seed` so successive runs attack different territory.

        A cell is 'uncovered' when no ALIVE conjecture's hypothesis matches
        BOTH atoms — pass unsolved+proved specs, not the failed bucket:
        refuted-only territory reopens for a boundary re-fit against the
        grown pool. Returns stratum tuples consumable by
        _discover_stratified. Deterministic per (registry state, seed)."""
        import re as _re
        try:
            p3 = table["p_3"].astype(int)
            p4 = table["p_4"].astype(int)
            p5 = table["p_5"].astype(int)
            s7 = table["sum_pk_k>=7"].astype(int)
        except Exception:
            return []
        env = {"p_3": p3, "p_4": p4, "p_5": p5, "s7": s7}

        def _var(key: str) -> str:
            return key.split("=")[0].split("<")[0]

        cells: list[tuple[int, str, str, str, list[str]]] = []
        atoms = self._CELL_ATOMS
        for i in range(len(atoms)):
            for j in range(i + 1, len(atoms)):
                k1, pred1, m1, rx1, drop1 = atoms[i]
                k2, pred2, m2, rx2, drop2 = atoms[j]
                if _var(k1) == _var(k2):
                    continue
                covered = any(_re.search(rx1, s.formula)
                              and _re.search(rx2, s.formula)
                              for s in existing_specs)
                if covered:
                    continue
                try:
                    mask = eval(f"({m1}) & ({m2})", {"__builtins__": {}}, env)
                    support = int(mask.sum())
                except Exception:
                    continue
                if support < self._STRAT_MIN_ROWS:
                    continue
                cells.append((support, f"{k1}&{k2}",
                              f"{pred1} and {pred2}",
                              f"({m1}) & ({m2})", drop1 + drop2))
        if not cells:
            return []
        cells.sort(reverse=True)
        offset = seed % len(cells)
        picked = [cells[(offset + k) % len(cells)]
                  for k in range(min(self._DYNAMIC_CELLS_PER_RUN, len(cells)))]
        return [(label, pred, mask, drop) for _, label, pred, mask, drop in picked]

    @staticmethod
    def _inject_predicate(formula: str, predicate: str) -> Optional[str]:
        """Inject `predicate` into the hypothesis clause of `formula`.

        Avoids duplicating the predicate if it (or any equivalent surface
        form) is already present. Returns the canonicalized formula or None
        if the formula doesn't have the expected `if (...), then ...` shape.
        """
        if predicate in formula:
            return canonicalize_formula(formula)
        m = re.match(r"if\s*\((.*?)\)\s*,\s*then\s+(.*)",
                     formula, re.IGNORECASE | re.DOTALL)
        if not m:
            return None
        hyp = m.group(1).strip()
        conc = m.group(2).strip()
        if hyp and hyp.lower() not in ("true", ""):
            new_hyp = f"{hyp} and {predicate}"
        else:
            new_hyp = predicate
        return canonicalize_formula(f"if ({new_hyp}), then {conc}")

    # ── data-driven LLM guidance blocks ──────────────────────────────────────

    @staticmethod
    def _pool_composition_block(row_pvecs: list[dict[int, int]]) -> str:
        """Structural breakdown of the verified pool — the LLM sees how many
        polytopes live in each classical stratum so it can spot fertile (and
        already-saturated) territory without us prescribing a list.

        We deliberately show counts only — *not* "propose a conjecture for
        stratum X". The LLM decides where to attack based on the pool size +
        the registry coverage block.
        """
        n = len(row_pvecs) or 1
        rows: list[tuple[str, int, str]] = []

        def _add(label: str, fn, desc: str) -> None:
            c = sum(1 for pv in row_pvecs if fn(pv))
            if c == 0:
                return
            rows.append((label, c, desc))

        _add("(p_3 = 0)",                 lambda pv: pv.get(3, 0) == 0,                                                 "triangle-free")
        _add("(p_4 = 0)",                 lambda pv: pv.get(4, 0) == 0,                                                 "quadrilateral-free")
        _add("(p_5 = 0)",                 lambda pv: pv.get(5, 0) == 0,                                                 "pentagon-free")
        _add("(p_3 = 0) ∧ (p_4 = 0)",     lambda pv: pv.get(3, 0) == 0 and pv.get(4, 0) == 0,                           "fullerene-shaped (5-/6-gons + tail)")
        _add("(p_4 = 0) ∧ (p_5 = 0)",     lambda pv: pv.get(4, 0) == 0 and pv.get(5, 0) == 0,                           "triangles + tail only")
        _add("(p_3 ≤ 2)",                 lambda pv: pv.get(3, 0) <= 2,                                                 "few triangles")
        _add("(p_4 ≤ 2)",                 lambda pv: pv.get(4, 0) <= 2,                                                 "few quadrilaterals")
        _add("(p_5 ≤ 2)",                 lambda pv: pv.get(5, 0) <= 2,                                                 "few pentagons")
        _add("sum_pk_k≥7 ≥ 1",            lambda pv: any(k >= 7 for k in pv),                                           "has at least one big face")
        _add("sum_pk_k≥7 ≥ 5",            lambda pv: sum(v for k, v in pv.items() if k >= 7) >= 5,                      "heavy 7+ tail")
        _add("(f_2 ≥ 30)",                lambda pv: sum(pv.values()) >= 30,                                            "medium polytope")
        _add("(f_2 ≥ 50)",                lambda pv: sum(pv.values()) >= 50,                                            "large polytope")
        _add("(f_2 ≥ 80)",                lambda pv: sum(pv.values()) >= 80,                                            "very large polytope")

        if not rows:
            return "  (pool empty)"
        return "\n".join(
            f"  {label:30s} {count:5d}/{n}  {desc}"
            for label, count, desc in rows
        )

    @staticmethod
    def _registry_coverage_block(existing_specs: list[ConjectureSpec]) -> str:
        """Hypothesis-shape histogram of the current registry.

        Patterns that match very few existing conjectures are visibly under-
        covered; the LLM is expected to spot the imbalance and target the
        thin rows. Patterns are intentionally OVERLAPPING (a conjecture with
        both `(p_3 = 0)` and `(p_4 = 0)` counts in both rows + in the joint
        row) so the LLM sees marginal density, not a partition.
        """
        import re as _re
        if not existing_specs:
            return "  (registry empty — all territory is open)"
        patterns: list[tuple[str, str]] = [
            ("(is_simple) only",                       r"^if\s*\(\(is_simple\)\)"),
            ("(f_2 ≥ N)",                              r"f_2>=_\d+"),
            ("(sum_pk_k≥7 ≥ j)",                       r"sum_pk_k>=7\s*>=\s*\d+"),
            ("(p_3 = 0)",                              r"p_3\s*=\s*0(?!\d)"),
            ("(p_4 = 0)",                              r"p_4\s*=\s*0(?!\d)"),
            ("(p_5 = 0)",                              r"p_5\s*=\s*0(?!\d)"),
            ("(p_3 = 0) ∧ (p_4 = 0)",                  r"(p_3\s*=\s*0.*p_4\s*=\s*0|p_4\s*=\s*0.*p_3\s*=\s*0)"),
            ("(p_3 = 0) ∧ (p_5 = 0)",                  r"(p_3\s*=\s*0.*p_5\s*=\s*0|p_5\s*=\s*0.*p_3\s*=\s*0)"),
            ("(p_4 = 0) ∧ (p_5 = 0)",                  r"(p_4\s*=\s*0.*p_5\s*=\s*0|p_5\s*=\s*0.*p_4\s*=\s*0)"),
            ("(p_3 ≤ N) (small N)",                    r"p_3\s*<=\s*\d+"),
            ("(p_4 ≤ N)",                              r"p_4\s*<=\s*\d+"),
            ("(p_5 ≤ N)",                              r"p_5\s*<=\s*\d+"),
        ]
        n_total = len(existing_specs)
        out: list[str] = [f"  TOTAL in registry: {n_total} conjectures"]
        for label, pat in patterns:
            c = sum(1 for s in existing_specs if _re.search(pat, s.formula))
            if c == 0:
                marker = "  ← UNTOUCHED"
            elif c <= 3:
                marker = "  ← thin"
            elif c >= 25:
                marker = "  ← saturated"
            else:
                marker = ""
            out.append(f"  {label:32s} {c:4d}{marker}")
        return "\n".join(out)

    # ── discovery: LLM proposer ───────────────────────────────────────────────

    def _llm_propose(
        self, signals: dict, existing_specs: list[ConjectureSpec],
        existing_iris: dict[str, dict], n_rows: int,
        verified_block: str = "  (none)",
        focus_block: str = "  (none)",
        max_existing: int = 20,
        row_pvecs: list[dict[int, int]] | None = None,
    ) -> list[str]:
        # Sort existing conjectures by IRIS-TRL desc — the LLM sees high-quality
        # templates at the top of the "do not duplicate" list and can mimic them.
        # Entries without iris (parse failures / pre-IRIS) sort last, untagged.
        def _trl(spec):
            iris = existing_iris.get(spec.name) or {}
            sk = iris.get("sort_keys") or {}
            return float(sk.get("TRL", 0.0) or 0.0)
        ranked = sorted(existing_specs, key=_trl, reverse=True)[:max_existing]
        existing_lines: list[str] = []
        for spec in ranked:
            iris = existing_iris.get(spec.name) or {}
            sk = iris.get("sort_keys") or {}
            T = iris.get("T")
            R = iris.get("R")
            L = iris.get("L")
            trl = sk.get("TRL")
            if trl is not None:
                tag = (f"[T={T:.2f} R={R:.2f} L={L:.2f} TRL={trl:.4f}] "
                       f"{spec.formula}")
            else:
                tag = f"[iris=n/a] {spec.formula}"
            existing_lines.append(f"  - {tag}")
        existing_block = "\n".join(existing_lines) or "  (none)"
        pool_composition_block = (
            self._pool_composition_block(row_pvecs) if row_pvecs else "  (n/a)"
        )
        registry_coverage_block = self._registry_coverage_block(existing_specs)
        prompt = CONJ_GEN_PROPOSE_PROMPT.format(
            success_block=format_hint_block(signals["proved"]),
            failure_block=format_hint_block(signals["refuted"]),
            stuck_block=format_hint_block(signals["prover_stuck"]),
            survivor_block=format_hint_block(signals["survivor"]),
            focus_block=focus_block,
            existing_block=existing_block,
            verified_block=verified_block,
            pool_composition_block=pool_composition_block,
            registry_coverage_block=registry_coverage_block,
            n_rows=n_rows,
            n_propose=self.llm_propose_n,
        )
        # Propose: Sonnet at effort=low is empirically 10–14× faster than
        # Haiku on math content (Haiku effort=low emits 11K reasoning tokens
        # and runs 70 s+; Sonnet effort=low finishes the slimmed prompt in
        # ~10 s — re-measured 2026-06-27 after the system/propose prompt
        # were shrunk to 0.6KB / 5.5KB). We deliberately ignore
        # `self.propose_model` and lock to review_model (= Sonnet) here;
        # callers that try to "save money" by passing Haiku end up paying
        # 7× the wall-clock and usually time out. fast_model kept None so
        # the SDK doesn't shadow the main model on retries.
        propose_model = self.review_model or self.model
        label = propose_model or "default"
        print(f"[conjecture generator] calling LLM propose "
              f"({label}, effort=low, ≤60s, no retry)…", flush=True)
        try:
            text = self.client._call(prompt, model=propose_model,
                                     system=CONJ_GEN_SYSTEM, timeout=60,
                                     max_attempts=1, effort="low")
        except Exception as exc:
            print(f"[conjecture generator] LLM propose skipped ({exc})", flush=True)
            return []
        data = _extract_json_from_text(text) or {}
        out: list[str] = []
        for f in data.get("conjectures", []):
            if isinstance(f, str) and f.strip().lower().startswith("if"):
                out.append(canonicalize_formula(f.strip()))
        print(f"[conjecture generator] LLM proposed {len(out)} candidate(s)",
              flush=True)
        return out

    # ── hypothesis clause simplification ─────────────────────────────────────

    @staticmethod
    def _simplify_hypothesis_clause(formula: str) -> str:
        """Rewrite the LHS to a flat, deduplicated `and`-chain.

        Graffiti3 ANDs predicates in a nested left-associative form
        (`((f_2>=_5) and (is_simple)) and (f_2>=_19)`) and may emit weaker
        siblings of the same family (`f_2>=_5 and f_2>=_19`). Stratified
        passes append an extra predicate on the right. The net result is
        readable garbage that also bloats the shape fingerprint. We:

          1. flatten the `and`-tree to a list of atomic predicates,
          2. collapse families with monotone semantics — keep the strongest
             `f_2>=_N` and `sum_pk_k>=7 >= j`, the smallest `p_k <= N`, the
             largest `p_k >= N`, the unique `p_k = N`,
          3. dedup `is_simple` and any literal duplicates,
          4. re-join with ` and ` in the canonical predicate order.

        Pure rewriting — semantically equivalent on every p-vector.
        """
        if not formula or "then" not in formula:
            return formula
        m = re.match(r"if\s*\((.*)\)\s*,\s*then\s+(.*)",
                     formula, re.IGNORECASE | re.DOTALL)
        if not m:
            return formula
        hyp_raw = m.group(1).strip()
        conc = m.group(2).strip()

        # Step 1: flatten. Strip outer parens repeatedly, then split by ` and `
        # at the TOP level (parens balanced).
        atoms: list[str] = []

        def _walk(s: str) -> None:
            s = s.strip()
            if not s:
                return
            # strip a single layer of fully-enclosing parens if present
            while s.startswith("(") and s.endswith(")"):
                depth = 0
                fully_enclosing = True
                for i, ch in enumerate(s):
                    if ch == "(":
                        depth += 1
                    elif ch == ")":
                        depth -= 1
                        if depth == 0 and i != len(s) - 1:
                            fully_enclosing = False
                            break
                if not fully_enclosing:
                    break
                s = s[1:-1].strip()
            # split on top-level " and "
            parts: list[str] = []
            depth = 0
            buf = ""
            i = 0
            while i < len(s):
                if s[i] == "(":
                    depth += 1
                    buf += s[i]
                elif s[i] == ")":
                    depth -= 1
                    buf += s[i]
                elif depth == 0 and s[i:i + 5].lower() == " and ":
                    parts.append(buf.strip())
                    buf = ""
                    i += 5
                    continue
                else:
                    buf += s[i]
                i += 1
            if buf.strip():
                parts.append(buf.strip())
            if len(parts) == 1:
                atom = parts[0].strip()
                # strip wrapping parens on an atom
                while atom.startswith("(") and atom.endswith(")"):
                    inner = atom[1:-1].strip()
                    if not inner:
                        break
                    atom = inner
                if atom:
                    atoms.append(atom)
                return
            for p in parts:
                _walk(p)

        _walk(hyp_raw)

        # Step 2 + 3: bucket by family, keep the strongest representative.
        is_simple = False
        f2_max: Optional[int] = None
        sum7_max: Optional[int] = None
        pk_eq: dict[int, int] = {}        # k -> N
        pk_le: dict[int, int] = {}        # k -> smallest N
        pk_ge: dict[int, int] = {}        # k -> largest N
        other: list[str] = []
        seen_other: set[str] = set()

        for atom in atoms:
            a = atom.strip()
            if not a:
                continue
            low = a.lower()
            if low == "is_simple":
                is_simple = True
                continue
            mf = re.fullmatch(r"f_2>=_(\d+)", a)
            if mf:
                n = int(mf.group(1))
                f2_max = n if f2_max is None else max(f2_max, n)
                continue
            ms = re.fullmatch(r"sum_pk_k>=7\s*>=\s*(\d+)", a)
            if ms:
                n = int(ms.group(1))
                sum7_max = n if sum7_max is None else max(sum7_max, n)
                continue
            mpe = re.fullmatch(r"p_([3-9])\s*=\s*(\d+)", a)
            if mpe:
                k, n = int(mpe.group(1)), int(mpe.group(2))
                pk_eq[k] = n
                continue
            mpl = re.fullmatch(r"p_([3-9])\s*<=\s*(\d+)", a)
            if mpl:
                k, n = int(mpl.group(1)), int(mpl.group(2))
                pk_le[k] = n if k not in pk_le else min(pk_le[k], n)
                continue
            mpg = re.fullmatch(r"p_([3-9])\s*>=\s*(\d+)", a)
            if mpg:
                k, n = int(mpg.group(1)), int(mpg.group(2))
                pk_ge[k] = n if k not in pk_ge else max(pk_ge[k], n)
                continue
            if a not in seen_other:
                other.append(a)
                seen_other.add(a)

        # Equality dominates le/ge for the same k (since `p_k = N` is strictly
        # stronger and the simpler form for Lean / display).
        for k in list(pk_eq.keys()):
            pk_le.pop(k, None)
            pk_ge.pop(k, None)

        # Step 4: emit in canonical order.
        ordered: list[str] = []
        if is_simple:
            ordered.append("(is_simple)")
        for k in sorted(pk_eq.keys()):
            ordered.append(f"(p_{k} = {pk_eq[k]})")
        for k in sorted(pk_le.keys()):
            ordered.append(f"(p_{k} <= {pk_le[k]})")
        for k in sorted(pk_ge.keys()):
            ordered.append(f"(p_{k} >= {pk_ge[k]})")
        if f2_max is not None:
            ordered.append(f"(f_2>=_{f2_max})")
        if sum7_max is not None:
            ordered.append(f"(sum_pk_k>=7 >= {sum7_max})")
        for a in other:
            ordered.append(f"({a})" if not a.startswith("(") else a)

        if not ordered:
            return formula
        new_hyp = " and ".join(ordered)
        return canonicalize_formula(f"if ({new_hyp}), then {conc}")

    # ── shape signature (used by failure-shape filter) ────────────────────────

    @staticmethod
    def _formula_shape(formula: str) -> Optional[tuple]:
        """Return (hyp_predicates, direction, rhs_variables) — a structural
        fingerprint that ignores constants and coefficients.

        Two formulas with the same shape differ only in numeric values; LP
        will keep producing the same shape with different numbers until the
        pool grows enough to refute it, so we drop shape repeats early.
        Returns None if the formula can't be parsed.
        """
        import re as _re
        if not formula or "then" not in formula:
            return None
        try:
            hyp_clause, conc_clause = formula.split(", then", 1)
        except ValueError:
            return None
        preds: set[str] = set()
        if "is_simple" in hyp_clause:
            preds.add("is_simple")
        if _re.search(r"f_2>=_\d+", hyp_clause):
            preds.add("f_2>=")
        if _re.search(r"sum_pk_k>=7\s*>=\s*\d+", hyp_clause):
            preds.add("sum_pk_k>=7>=")
        # Structural predicates (Eberhard / Jučovič / Grünbaum families).
        # Threshold values are captured into the fingerprint so two formulas
        # with the same structural predicate at different N count as distinct
        # shapes (`p_3 = 0` vs `p_3 = 1` are genuinely different theorems).
        for m_eq in _re.finditer(r"p_([3-9])\s*=\s*(\d+)", hyp_clause):
            preds.add(f"p_{m_eq.group(1)}={m_eq.group(2)}")
        for m_le in _re.finditer(r"p_([3-9])\s*<=\s*(\d+)", hyp_clause):
            preds.add(f"p_{m_le.group(1)}<={m_le.group(2)}")
        for m_ge in _re.finditer(r"p_([3-9])\s*>=\s*(\d+)", hyp_clause):
            preds.add(f"p_{m_ge.group(1)}>={m_ge.group(2)}")
        m = _re.search(r"p6\s*(<=|>=)", conc_clause)
        if not m:
            return None
        direction = m.group(1)
        rhs_only = conc_clause[m.end():]
        rhs_vars = tuple(sorted(set(_re.findall(
            r"p[3-5]|sum_pk_after_p6", rhs_only))))
        return (tuple(sorted(preds)), direction, rhs_vars)

    # ── deterministic LP-overfit guard ────────────────────────────────────────

    @staticmethod
    def _drop_lp_overfit(
        accepted: list[tuple[str, str]], max_denom: int = 6,
    ) -> tuple[list[tuple[str, str]], list[dict]]:
        """Drop candidates whose RHS has any coefficient with denominator > max_denom.

        Lean-friendly bounds use coefficients in {1, 2, 3, 6}. Graffiti3's LP
        emits floats like 0.6428571429 (= 9/14) — those rationals turn into
        sorry-laden proofs even when the bound is correct, and are usually
        also pool-overfit (one f_2 step from a counterexample). This is the
        deterministic version of what the LLM review prompt asks for; running
        it pre-review means the LLM sees a slimmer batch and is much less
        likely to time out.
        """
        import re as _re
        from fractions import Fraction
        kept: list[tuple[str, str]] = []
        dropped: list[dict] = []
        for formula, source in accepted:
            # Look only at the RHS — anything after "then p6 <=" or "then p6 >=".
            m = _re.search(r"then\s+p6\s*[<>]=", formula)
            rhs = formula[m.end():] if m else formula
            offending: list[str] = []
            for tok in _re.findall(r"-?\d+\.\d+|-?\d+/\d+", rhs):
                try:
                    if "/" in tok:
                        frac = Fraction(tok)
                    else:
                        # limit_denominator finds the cleanest rational
                        # within ~1e-6 — catches 0.6428571429 → 9/14.
                        frac = Fraction(tok).limit_denominator(1000)
                except Exception:
                    continue
                if abs(frac.denominator) > max_denom:
                    offending.append(f"{tok} ≈ {frac}")
            if offending:
                reason = (f"lp_overfit: denom > {max_denom} in "
                          f"{', '.join(offending[:3])}")
                dropped.append({"formula": formula, "source": source,
                                "reason": reason})
            else:
                kept.append((formula, source))
        if dropped:
            print(f"[conjecture generator] overfit guard dropped {len(dropped)} "
                  f"candidate(s) with denom > {max_denom}", flush=True)
        return kept, dropped

    # ── trivial-RHS guard ─────────────────────────────────────────────────────

    @staticmethod
    def _rhs_sup_under_hypothesis(formula: str, rhs: str) -> Optional[float]:
        """Supremum of a LINEAR RHS over the box the hypothesis atoms allow.

        Box constraints read from the hypothesis clause:
          `p_k = N` → [N,N]   `p_k <= N` → [0,N]   `p_k >= N` → [N,∞)
          `sum_pk_k>=7 >= j` → [j,∞)
        Every count variable is non-negative; unmentioned vars are [0,∞).

        Returns None when the sup is unbounded above or the RHS is
        nonlinear / unevaluable — the guard acts only on a PROVABLE bound,
        never on a guess.
        """
        import re as _re
        hyp = formula.split(", then", 1)[0]
        names = ("p3", "p4", "p5", "sum_pk_after_p6")
        bounds: dict[str, list[float]] = {v: [0.0, float("inf")] for v in names}
        for m in _re.finditer(r"p_([3-5])\s*=\s*(\d+)", hyp):
            v, n = f"p{m.group(1)}", float(m.group(2))
            bounds[v] = [n, n]
        for m in _re.finditer(r"p_([3-5])\s*<=\s*(\d+)", hyp):
            v, n = f"p{m.group(1)}", float(m.group(2))
            bounds[v][1] = min(bounds[v][1], n)
        for m in _re.finditer(r"p_([3-5])\s*>=\s*(\d+)", hyp):
            v, n = f"p{m.group(1)}", float(m.group(2))
            bounds[v][0] = max(bounds[v][0], n)
        m = _re.search(r"sum_pk_k>=7\s*>=\s*(\d+)", hyp)
        if m:
            bounds["sum_pk_after_p6"][0] = max(
                bounds["sum_pk_after_p6"][0], float(m.group(1)))

        expr = rhs.replace("sum_pk_k>=7", "sum_pk_after_p6").replace("p_", "p")

        def _ev(env: dict[str, float]) -> float:
            return float(eval(expr, {"__builtins__": {}},
                              {n: env.get(n, 0.0) for n in names}))

        try:
            const = _ev({})
            coeffs: dict[str, float] = {}
            for v in names:
                c = _ev({v: 1.0}) - const
                if abs((_ev({v: 2.0}) - const) - 2 * c) > 1e-9:
                    return None          # nonlinear in v
                coeffs[v] = c
            # joint probe catches cross-terms (p3*p5, …) single-var probes miss
            if abs(_ev({v: 1.0 for v in names})
                   - (const + sum(coeffs.values()))) > 1e-9:
                return None
        except Exception:
            return None

        sup = const
        for v, c in coeffs.items():
            if abs(c) < 1e-12:
                continue
            lo, hi = bounds[v]
            if c > 0:
                if hi == float("inf"):
                    return None          # unbounded above — not provably vacuous
                sup += c * hi
            else:
                sup += c * lo
        return sup

    @staticmethod
    def _drop_trivial_rhs(
        accepted: list[tuple[str, str]],
    ) -> tuple[list[tuple[str, str]], list[dict]]:
        """Drop candidates whose RHS makes the bound information-free.

        Triggered shapes:
          • `p6 >= K` with K ≤ 0  — always true (p6 ≥ 0 by definition).
          • `p6 >= RHS(vars)` where the hypothesis atoms already force
            sup(RHS) ≤ 0 — the variable flavour of the same vacuity, judged
            by interval arithmetic (`_rhs_sup_under_hypothesis`). The C137
            lesson (2026-07-02): `p5 ≤ 2 ∧ Σ₇₊ ≥ 5 ⟹ -0.5·Σ₇₊ + p5 ≤ -0.5`
            survived CE search (nothing to refute) and was trivially proved
            — a Lean theorem with zero mathematical content.
          • `p6 <= K` with K < 0  — never satisfiable; no math, just omega.
          • `p6 <= K` with K > 0 and a hypothesis too weak to bound p6 to a
            constant — empirically refutable, RL just rarely budgets enough
            to find the offending large polytope. We require the hypothesis
            to contain at least one "p6-bounding" predicate:
              - `(p_k = N)` for k ∈ {3,4,5}  (exact count + DS pins p6)
              - `(f_2 <= N)` / `(f_2 = N)`   (face count caps p6 directly)
            Without one of those, `p6 <= 20` is just LP fitting the pool's
            largest p6 in the matched stratum — refutable by enlarging f2.
            Lower-bound constants (K > 0 on `p6 >= K`) are KEPT — they're
            informative ("every polytope satisfying H has at least K hexagons").
        """
        import re as _re
        kept: list[tuple[str, str]] = []
        dropped: list[dict] = []
        for formula, source in accepted:
            m = _re.search(r"then\s+p6\s*(<=|>=)\s*\((.*)\)\s*$", formula)
            if not m:
                kept.append((formula, source))
                continue
            op, rhs = m.group(1), m.group(2).strip()
            has_var = bool(_re.search(r"\bp[3-9]\b|sum_pk_after_p6", rhs))
            if has_var:
                if op == ">=":
                    sup = ConjectureGenerator._rhs_sup_under_hypothesis(
                        formula, rhs)
                    if sup is not None and sup <= 0:
                        dropped.append({
                            "formula": formula, "source": source,
                            "reason": (f"vacuous_rhs: hypothesis forces "
                                       f"sup(RHS) = {sup:g} ≤ 0, and p6 ≥ 0 "
                                       f"always — bound excludes nothing"),
                        })
                        continue
                kept.append((formula, source))
                continue
            try:
                fval = float(eval(rhs, {"__builtins__": {}}, {}))
            except Exception:
                kept.append((formula, source))
                continue
            if op == ">=" and fval <= 0:
                dropped.append({"formula": formula, "source": source,
                                "reason": f"trivial_rhs: p6 >= {fval} is always true"})
                continue
            if op == "<=" and fval < 0:
                dropped.append({"formula": formula, "source": source,
                                "reason": f"trivial_rhs: p6 <= {fval} is unsatisfiable"})
                continue
            if op == "<=" and fval > 0:
                hyp_clause = formula.split(", then", 1)[0]
                # Need an EQ or f_2 upper-bound to make a constant ceiling
                # plausible. If none, drop.
                has_pk_eq = bool(_re.search(r"p_[3-5]\s*=\s*\d+", hyp_clause))
                # f_2 cap forms: DSL `f_2<=_N` / `f_2=_N` (underscore prefix),
                # plain `f_2 <= N` / `f_2 = N`, or LaTeX `f_2 \leq N`.
                has_f2_cap = bool(_re.search(r"f_2\s*(?:<=|=)\s*_?\d+",
                                             hyp_clause))
                if not (has_pk_eq or has_f2_cap):
                    dropped.append({"formula": formula, "source": source,
                                    "reason": (f"trivial_rhs: p6 <= {fval} "
                                               f"with no p_k=N / f_2 cap — "
                                               f"hypothesis cannot pin p6 to "
                                               f"a constant")})
                    continue
            kept.append((formula, source))
        if dropped:
            print(f"[conjecture generator] trivial-RHS guard dropped "
                  f"{len(dropped)} candidate(s)", flush=True)
        return kept, dropped

    # ── Semantic-duplicate filter ─────────────────────────────────────────────

    @staticmethod
    def _semantic_signature(formula: str) -> Optional[tuple]:
        """Attack-surface signature: (canonical hypothesis atoms, frozenset of
        DS-valid CE-candidate p-vectors inside a pinned enumeration box).

        Two same-hypothesis conjectures with identical candidate sets are
        attacked — witness-replayed, plantri-screened, refuted, proved —
        identically even when their RHS coefficients differ: C193
        `p6 ≥ -2S+4` vs C199 `p6 ≥ -3S+5` demand the same p6 on every
        arithmetically feasible p-vector (2026-07-04 lesson), so registering
        both burns a full CE-search + prover cycle on a re-run.

        Returns None (candidate exempt from this filter) when parsing fails,
        the enumeration is empty (two tight bounds with different content
        would collide on the empty set), or the enumerator truncated at
        max_results (set equality unreliable under truncation). Bounds are
        pinned rather than env-derived so signatures stay comparable across
        one run regardless of ambient CE_ENUM_* overrides."""
        try:
            from agent.conjectures import ConjectureSpec
            from agent.orchestrator.tools.ce_enumerator import (
                enumerate_ce_candidates,
            )
            conj = ParsedConjecture.from_conjecture_spec(
                ConjectureSpec(name="_semdup_probe", formula=formula))
            cap = 400
            cands = enumerate_ce_candidates(
                conj, f2_max=36, k_max=20, n_large_max=2, max_results=cap)
            if not cands or len(cands) >= cap:
                return None
            hyp_key = tuple(sorted(str(h) for h in conj.hypotheses))
            pv_key = frozenset(tuple(sorted(c.p_vec.items())) for c in cands)
            return (hyp_key, pv_key)
        except Exception:
            return None

    # Hypothesis atoms this DSL emits: `p_3 = 0`, `p_4 <= 2`, `f_2>=_17`
    # (underscore threshold form), `sum_pk_k>=7 >= 3` (the variable name
    # itself contains `>=7`, so it must be matched before the operator).
    _HYP_ATOM_RE = re.compile(
        r"^\s*(?P<var>sum_pk_k>=\d+|f_2|p_\d+)\s*"
        r"(?P<op>>=|<=|=)\s*_?(?P<val>\d+)\s*$")

    @staticmethod
    def _hyp_conclusion_form(formula: str) -> Optional[tuple]:
        """Parse a formula into (hypothesis atoms, normalized conclusion) for
        the implication check: atoms are (var, op, int) triples, conclusion a
        whitespace-stripped string. Returns None (candidate exempt) when any
        hypothesis atom fails to parse — no verdict without full coverage."""
        try:
            conj = ParsedConjecture.from_conjecture_spec(
                ConjectureSpec(name="_semdup_probe", formula=formula))
            atoms = []
            for h in conj.hypotheses:
                h = str(h).strip()
                if h == "is_simple":
                    continue
                m = ConjectureGenerator._HYP_ATOM_RE.match(h)
                if m is None:
                    return None
                atoms.append((m.group("var"), m.group("op"),
                              int(m.group("val"))))
            concl = re.sub(r"\s+", "", str(conj.conclusion or ""))
            if not concl:
                return None
            return tuple(atoms), concl
        except Exception:
            return None

    @staticmethod
    def _atom_implies(a: tuple, b: tuple) -> bool:
        """True iff hypothesis atom `a` implies atom `b`."""
        (va, oa, na), (vb, ob, nb) = a, b
        if va != vb:
            return False
        if oa == "=":
            return ((ob == "=" and na == nb) or (ob == "<=" and na <= nb)
                    or (ob == ">=" and na >= nb))
        if oa == "<=" and ob == "<=":
            return na <= nb
        if oa == ">=" and ob == ">=":
            return na >= nb
        return False

    @classmethod
    def _hyps_imply(cls, stronger: tuple, weaker: tuple) -> bool:
        """conjunction(stronger) ⇒ conjunction(weaker), checked atom-wise:
        every atom of `weaker` must be implied by some atom of `stronger`."""
        return all(any(cls._atom_implies(s, w) for s in stronger)
                   for w in weaker)

    def _drop_semantic_dupes(
        self,
        accepted: list[tuple[str, str]],
        alive_specs: list,
    ) -> tuple[list[tuple[str, str]], list[dict]]:
        """Drop candidates whose attack surface duplicates an ALIVE registered
        conjecture (unsolved + proved) or an earlier candidate in this batch,
        and candidates outright IMPLIED by an alive one — same conclusion
        with hypotheses at least as restrictive (C195 ⇒ C214 lesson,
        2026-07-06): the restricted variant carries zero content while its
        parent is alive, and only earns existence if the parent is later
        refuted by a CE outside the restriction — the mutation engine's job,
        not the generator's.

        Refuted entries are deliberately NOT compared against: a duplicate of
        a refuted formula dies in Stage 0 for the cost of one witness replay,
        while a duplicate of an alive one wastes a full pipeline cycle — and
        signature computation across ~190 refuted entries would dominate the
        filter's cost for no protection."""
        sigs: dict[tuple, str] = {}
        forms: list[tuple[str, tuple, str]] = []   # (name, atoms, conclusion)
        for spec in alive_specs:
            sig = self._semantic_signature(spec.formula)
            if sig is not None and sig not in sigs:
                sigs[sig] = spec.name
            form = self._hyp_conclusion_form(spec.formula)
            if form is not None:
                forms.append((spec.name, form[0], form[1]))
        kept: list[tuple[str, str]] = []
        dropped: list[dict] = []
        for formula, source in accepted:
            cand_form = self._hyp_conclusion_form(formula)
            implied_by = None
            if cand_form is not None:
                cand_atoms, cand_concl = cand_form
                for name, atoms, concl in forms:
                    if concl == cand_concl and self._hyps_imply(cand_atoms,
                                                                atoms):
                        implied_by = name
                        break
            if implied_by is not None:
                dropped.append({
                    "formula": formula, "source": source,
                    "reason": (f"implied_by {implied_by}: same conclusion, "
                               f"hypotheses at least as restrictive — "
                               f"redundant while {implied_by} is alive"),
                })
                continue
            sig = self._semantic_signature(formula)
            if sig is not None and sig in sigs:
                dropped.append({
                    "formula": formula, "source": source,
                    "reason": (f"semantic_duplicate of {sigs[sig]}: same "
                               f"hypotheses + identical arithmetic "
                               f"CE-candidate set — different coefficients, "
                               f"same attack surface"),
                })
                continue
            if sig is not None:
                sigs[sig] = f"this batch: {formula[:60]}"
            if cand_form is not None:
                forms.append((f"this batch: {formula[:60]}",
                              cand_form[0], cand_form[1]))
            kept.append((formula, source))
        if dropped:
            print(f"[conjecture generator] semantic-dup filter dropped "
                  f"{len(dropped)} candidate(s) (duplicate attack surface or "
                  f"implied by an alive conjecture)", flush=True)
        return kept, dropped

    # ── LLM reviewer ──────────────────────────────────────────────────────────

    def _llm_review(
        self, accepted: list[tuple[str, str]], signals: dict,
        verified_block: str = "  (none)",
    ) -> tuple[list[tuple[str, str]], list[dict]]:
        """Hint-aware keep/drop. Advisory only: on any LLM/parse error the
        full accepted list passes through (the hard filter already ran)."""
        candidate_block = "\n".join(
            f"  {i}. {f}   [from {src}]"
            for i, (f, src) in enumerate(accepted, start=1)
        )
        prompt = CONJ_GEN_REVIEW_PROMPT.format(
            failure_block=format_hint_block(signals["refuted"]),
            verified_block=verified_block,
            candidate_block=candidate_block,
        )
        # Review: Sonnet at effort=low. effort=medium triggers extended
        # thinking that reliably blew past every timeout we tried
        # (60/90/120/210 s) on batches of 40+ candidates; effort=low
        # produces well-formed keep/drop verdicts in ~25 s on a 9 KB
        # synthetic prompt but ran longer (≈ 60–80 s) on real candidate
        # batches with more diverse hypothesis structure. 180 s gives that
        # tail room. Review is advisory, so if it does time out the
        # candidate list flows through untouched — no regression.
        review_model = self.review_model or self.model
        label = review_model or "default"
        print(f"[conjecture generator] calling LLM review on {len(accepted)} "
              f"candidate(s) ({label}, effort=low, ≤180s, no retry)…", flush=True)
        try:
            text = self.client._call(prompt, model=review_model,
                                     system=CONJ_GEN_SYSTEM, timeout=180,
                                     max_attempts=1, effort="low")
        except Exception as exc:
            print(f"[conjecture generator] LLM review skipped ({exc})", flush=True)
            return accepted, []
        data = _extract_json_from_text(text) or {}
        reviews = [r for r in data.get("reviews", []) if isinstance(r, dict)]
        drops = {r.get("index"): r.get("reason", "")
                 for r in reviews if r.get("verdict") == "drop"}

        kept: list[tuple[str, str]] = []
        dropped: list[dict] = []
        for i, (formula, source) in enumerate(accepted, start=1):
            if i in drops:
                dropped.append({"formula": formula, "source": source,
                                "reason": f"llm_review_drop: {drops[i]}"})
            else:
                kept.append((formula, source))
        if dropped:
            print(f"[conjecture generator] LLM review dropped {len(dropped)} "
                  f"candidate(s)", flush=True)
        return kept, dropped

    # ── filtering ─────────────────────────────────────────────────────────────

    def _consistent_with_verified(
        self, formula: str, row_pvecs: list[dict[int, int]]
    ) -> tuple[bool, str, Optional[float]]:
        """A candidate must hold on every verified realizable p-vector.

        FAIL-CLOSED: an unevaluable conclusion or hypotheses that match no
        verified polytope reject the candidate — never register a conjecture
        the pipeline's evaluators cannot falsify.

        Returns (ok, why, min_slack). min_slack is the smallest distance to
        equality over the support (0.0 = the bound touches the pool hull) —
        the tightness certificate the shape-repeat rule consumes; None when
        the conclusion direction gives no slack notion.
        """
        try:
            parsed = ParsedConjecture.from_conjecture_spec(
                ConjectureSpec(name="candidate_0", formula=formula))
        except Exception as exc:
            return False, f"parse_failed: {exc}", None

        kind, rhs_fn = _compile_conclusion(parsed.conclusion)
        if kind == "unknown" or rhs_fn is None:
            return False, f"unevaluable conclusion: {parsed.conclusion[:80]}", None

        support = 0
        min_slack: Optional[float] = None
        for pv in row_pvecs:
            try:
                if not all(_eval_hypothesis(h, pv) for h in parsed.hypotheses):
                    continue
                support += 1
                violated, detail = _eval_conclusion_violated(parsed.conclusion, pv)
            except Exception:
                continue
            if violated:
                return False, f"contradicted by verified p-vector {pv} ({detail})", None
            if kind in ("ge", "le"):
                try:
                    rhs = float(rhs_fn(pv))
                    p6 = float(pv.get(6, 0))
                    s = (p6 - rhs) if kind == "ge" else (rhs - p6)
                    if min_slack is None or s < min_slack:
                        min_slack = s
                except Exception:
                    pass
        if support == 0:
            return False, "hypotheses match no verified polytope (vacuous or unparsable)", None
        return True, "", min_slack

    # ── registration helpers ──────────────────────────────────────────────────

    def _assign_names(
        self, formulas: list[str], run_ts: str, existing: list[ConjectureSpec]
    ) -> list[ConjectureSpec]:
        formula_to_name = {canonicalize_formula(s.formula): s.name for s in existing}
        used_names = set(formula_to_name.values())
        specs: list[ConjectureSpec] = []
        # Continue the GLOBAL numeric suffix: short_id ('C<suffix>') keys the CE
        # output dirs, so restarting at 1 per run would collide with existing Cn.
        # Accept both the legacy `auto_<ts>_<n>` shape and the new bare `C<n>`.
        max_suffix = 0
        for n in used_names:
            m = re.search(r"(\d+)$", n or "")
            if m:
                max_suffix = max(max_suffix, int(m.group(1)))
        next_index = max_suffix + 1
        for formula in formulas:
            name = formula_to_name.get(formula)
            if name is None:
                while True:
                    candidate = f"C{next_index}"
                    next_index += 1
                    if candidate not in used_names:
                        name = candidate
                        used_names.add(name)
                        break
            specs.append(ConjectureSpec(name=name, formula=formula))
        return specs

    def _write_run_log(
        self, run_ts: str, specs: list[ConjectureSpec], sources: dict,
        rejected: list[dict], n_rows: int,
    ) -> None:
        try:
            _RUN_LOG_DIR.mkdir(parents=True, exist_ok=True)
            path = _RUN_LOG_DIR / f"run_{run_ts}.json"
            path.write_text(json.dumps({
                "run_timestamp": run_ts,
                "generated_at": datetime.now(timezone.utc).isoformat(),
                "dataset_rows": n_rows,
                "g3_mode": self.g3_mode,
                "linear_only": self.linear_only,
                "llm_enabled": self.client is not None,
                "accepted": [{"name": s.name, "formula": s.formula,
                              "source": sources.get(s.formula, "graffiti3")}
                             for s in specs],
                "rejected": rejected,
            }, indent=2, ensure_ascii=False))
            print(f"[conjecture generator] run log → {path}", flush=True)
        except Exception as exc:
            print(f"[conjecture generator] warning: run log not written ({exc})",
                  flush=True)


def _safe_repr(obj) -> str:
    try:
        s = str(obj)
    except Exception as exc:
        return f"<unprintable: {exc}>"
    return s[:400]
