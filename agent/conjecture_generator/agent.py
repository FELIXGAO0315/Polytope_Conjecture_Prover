"""
agent/conjecture_generator/agent.py — Graffiti3 + LLM conjecture generator.

Discovers new p6-bound conjectures and registers them into
conjectures/conjectures.json with status='new' (the evolution loop only ever
runs 'new' entries).

Candidate sources (both pass the SAME hard filter — no source is trusted):
  - Graffiti3: data-driven LP fitting on the verified-polytope table
  - LLM (optional, when `client` is given): proposes formulas directly,
    guided by the hint store (success hints = primary, failure = gatekeeper)

Hard filter, identical for every candidate:
  1. must render/parse in the project DSL and be evaluable by pvec_eval
  2. must hold on every pipeline-verified realizable p-vector
  3. dedup: in-batch + against conjectures.json (unsolved AND solved)

When `client` is given, an LLM review pass (keep/drop, hint-aware) runs AFTER
the hard filter. Hints influence generation only — never CE finding or any
verification gate.

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
    upsert_conjectures,
)
from agent.conjecture_generator.prompts.conjecture_generator import (
    CONJ_GEN_PROPOSE_PROMPT,
    CONJ_GEN_REVIEW_PROMPT,
    CONJ_GEN_SYSTEM,
)
from agent.conjecture_generator.tools.dataset import NUMERIC_COLS, build_discovery_table
from agent.conjecture_generator.tools.hints import format_hint_block, load_hints
from agent.conjecture_generator.tools.render import render_txgraffiti_conjecture
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
        llm_propose_n: int = 8,   # how many formulas to ask the LLM for
        dry_run: bool = False,    # discover + filter, but do not write anything
    ) -> None:
        self.client = client
        self.limit = limit
        self.g3_mode = g3_mode
        self.quick = quick
        self.linear_only = linear_only
        self.enable_sophie = enable_sophie
        self.llm_propose_n = llm_propose_n
        self.dry_run = dry_run
        self.model = getattr(client, "model", None)

    # ── main entry ────────────────────────────────────────────────────────────

    def run(self) -> list[ConjectureSpec]:
        """Discover, filter, dedup, register. Returns the registered specs."""
        table, row_pvecs, hyp_cols = build_discovery_table()
        print(f"[conjecture generator] discovery table: {len(table)} rows, "
              f"{len(hyp_cols)} hypothesis column(s)", flush=True)

        discovered = self._discover(table) or []
        if not discovered:
            core = [c for c in ["is_simple"] + NUMERIC_COLS if c in table.columns]
            print(f"[conjecture generator] 0 raw conjectures; retrying with core "
                  f"columns only ({core})", flush=True)
            discovered = self._discover(table[core]) or []
        print(f"[conjecture generator] Graffiti3 produced {len(discovered)} raw "
              f"conjecture(s)", flush=True)

        hints = load_hints()
        existing_unsolved, existing_solved = load_conjecture_dataset()
        known_formulas = {
            canonicalize_formula(s.formula)
            for s in existing_unsolved + existing_solved
        }

        # ── gather candidates from all sources ────────────────────────────────
        candidates: list[tuple[str, str]] = []   # (formula, source)
        rejected: list[dict] = []
        for obj in discovered:
            formula = render_txgraffiti_conjecture(obj)
            if formula:
                candidates.append((formula, "graffiti3"))
            else:
                rejected.append({"raw": _safe_repr(obj), "source": "graffiti3",
                                 "reason": "render_failed"})
        if self.client is not None:
            for formula in self._llm_propose(hints, known_formulas, len(table)):
                candidates.append((formula, "llm"))

        # ── hard filter — identical for every source ──────────────────────────
        accepted: list[tuple[str, str]] = []
        for idx, (formula, source) in enumerate(candidates, start=1):
            norm = canonicalize_formula(formula)
            if norm in known_formulas:
                rejected.append({"formula": norm, "source": source,
                                 "reason": "duplicate"})
                continue
            ok, why = self._consistent_with_verified(norm, row_pvecs)
            if not ok:
                rejected.append({"formula": norm, "source": source, "reason": why})
                print(f"[conjecture generator] #{idx} ({source}) rejected: "
                      f"{norm}  ({why})", flush=True)
                continue
            known_formulas.add(norm)
            accepted.append((norm, source))
            print(f"[conjecture generator] #{idx} ({source}) accepted: {norm}",
                  flush=True)
            if self.limit and len(accepted) >= self.limit:
                break

        # ── LLM review (advisory keep/drop, after the hard filter) ────────────
        if self.client is not None and accepted:
            accepted, review_drops = self._llm_review(accepted, hints)
            rejected.extend(review_drops)

        run_ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        specs = self._assign_names([f for f, _ in accepted], run_ts,
                                   existing_unsolved + existing_solved)
        sources = {spec.formula: src for spec, (_, src) in zip(specs, accepted)}
        print(f"[conjecture generator] accepted {len(specs)}, "
              f"rejected {len(rejected)}", flush=True)

        if self.dry_run:
            print("[conjecture generator] dry run — nothing written")
            for s in specs:
                print(f"  would register {s.name}: {s.formula}")
            return specs

        if specs:
            inserted = upsert_conjectures(specs)
            print(f"[conjecture generator] registered {len(inserted)} conjecture(s) "
                  f"with status=new", flush=True)
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

        targets = [c for c in ["p_6", "p6", "p_3", "p_4", "p_5", "sum_pk_k>=7"]
                   if c in table.columns]
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

    # ── discovery: LLM proposer ───────────────────────────────────────────────

    def _llm_propose(
        self, hints: dict, known_formulas: set[str], n_rows: int
    ) -> list[str]:
        existing = sorted(known_formulas)
        existing_block = "\n".join(f"  - {f}" for f in existing[:60]) or "  (none)"
        prompt = CONJ_GEN_PROPOSE_PROMPT.format(
            success_block=format_hint_block(hints["success"]),
            failure_block=format_hint_block(hints["failure"]),
            existing_block=existing_block,
            n_rows=n_rows,
            n_propose=self.llm_propose_n,
        )
        try:
            text = self.client._call(prompt, model=self.model,
                                     system=CONJ_GEN_SYSTEM, timeout=300)
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

    # ── LLM reviewer ──────────────────────────────────────────────────────────

    def _llm_review(
        self, accepted: list[tuple[str, str]], hints: dict
    ) -> tuple[list[tuple[str, str]], list[dict]]:
        """Hint-aware keep/drop. Advisory only: on any LLM/parse error the
        full accepted list passes through (the hard filter already ran)."""
        candidate_block = "\n".join(
            f"  {i}. {f}   [from {src}]"
            for i, (f, src) in enumerate(accepted, start=1)
        )
        prompt = CONJ_GEN_REVIEW_PROMPT.format(
            success_block=format_hint_block(hints["success"]),
            failure_block=format_hint_block(hints["failure"]),
            candidate_block=candidate_block,
        )
        try:
            text = self.client._call(prompt, model=self.model,
                                     system=CONJ_GEN_SYSTEM, timeout=300)
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
                print(f"[conjecture generator] review dropped #{i}: {formula}  "
                      f"({drops[i]})", flush=True)
            else:
                kept.append((formula, source))
        return kept, dropped

    # ── filtering ─────────────────────────────────────────────────────────────

    def _consistent_with_verified(
        self, formula: str, row_pvecs: list[dict[int, int]]
    ) -> tuple[bool, str]:
        """A candidate must hold on every verified realizable p-vector.

        FAIL-CLOSED: an unevaluable conclusion or hypotheses that match no
        verified polytope reject the candidate — never register a conjecture
        the pipeline's evaluators cannot falsify.
        """
        try:
            parsed = ParsedConjecture.from_conjecture_spec(
                ConjectureSpec(name="candidate_0", formula=formula))
        except Exception as exc:
            return False, f"parse_failed: {exc}"

        kind, rhs_fn = _compile_conclusion(parsed.conclusion)
        if kind == "unknown" or rhs_fn is None:
            return False, f"unevaluable conclusion: {parsed.conclusion[:80]}"

        support = 0
        for pv in row_pvecs:
            try:
                if not all(_eval_hypothesis(h, pv) for h in parsed.hypotheses):
                    continue
                support += 1
                violated, detail = _eval_conclusion_violated(parsed.conclusion, pv)
            except Exception:
                continue
            if violated:
                return False, f"contradicted by verified p-vector {pv} ({detail})"
        if support == 0:
            return False, "hypotheses match no verified polytope (vacuous or unparsable)"
        return True, ""

    # ── registration helpers ──────────────────────────────────────────────────

    def _assign_names(
        self, formulas: list[str], run_ts: str, existing: list[ConjectureSpec]
    ) -> list[ConjectureSpec]:
        formula_to_name = {canonicalize_formula(s.formula): s.name for s in existing}
        used_names = set(formula_to_name.values())
        specs: list[ConjectureSpec] = []
        # Continue the GLOBAL numeric suffix: short_id ('C<suffix>') keys the CE
        # output dirs, so restarting at _1 per run would collide with old Cn.
        max_suffix = 0
        for n in used_names:
            m = re.search(r"_(\d+)$", n or "")
            if m:
                max_suffix = max(max_suffix, int(m.group(1)))
        next_index = max_suffix + 1
        for formula in formulas:
            name = formula_to_name.get(formula)
            if name is None:
                while True:
                    candidate = f"auto_{run_ts}_{next_index}"
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
