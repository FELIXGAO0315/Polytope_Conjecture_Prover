"""
agent/orchestrator/evolution_loop.py — generator ⇄ pipeline evolution loop.

One generation:
  ① ConjectureGenerator (Graffiti3 + LLM, hint-aware) registers status='new'
  ② every 'new' conjecture runs CE search (Stage 1 → 2)
       CE found → status='refuted'      + failure hint
       no CE    → Stage 3 prover:
           proved           → status='proven'        + success hint → STOP
           failed / skipped → status='prover_failed' + failure hint
  ③ next generation — the generator now knows this round's outcomes

Stop conditions: first proven conjecture, --max-generations exhausted, or two
consecutive generations producing zero new conjectures.

Rules enforced here:
  - only status='new' conjectures are ever evaluated; entries with results
    never re-enter the loop
  - success hints come ONLY from prover success; surviving CE search is not
    success (prover failure → failure hint)
  - hints feed the generator only; CE finding and all verification gates run
    exactly as in the normal pipeline

Usage:
  python -m agent.orchestrator.evolution_loop
  python -m agent.orchestrator.evolution_loop --max-generations 5 \\
      --rl-episodes 100 --llm-rounds 5 --g3-mode fast --no-llm-gen
"""
from __future__ import annotations

import argparse
import json
from typing import Optional

from agent.conjectures import (
    ConjectureSpec,
    get_conjectures_by_status,
    set_conjecture_status,
)
from agent.conjecture_generator import ConjectureGenerator
from agent.conjecture_generator.tools.hints import add_failure_hint, add_success_hint
from agent.orchestrator.orchestrator import (
    Orchestrator,
    _resolve_lean_output,
    _write_ce_json,
)
from agent.orchestrator.tools.conjecture_parser import ParsedConjecture


def _pv_jsonable(pv) -> Optional[dict]:
    if isinstance(pv, dict):
        return {str(k): v for k, v in pv.items()}
    return None


class EvolutionLoop:
    def __init__(
        self,
        max_generations: int = 10,
        rl_episodes: int = 600,
        llm_rounds: int = 15,
        use_llm_generator: bool = True,
        g3_mode: str = "fast",
        llm_propose_n: int = 8,
        generator_limit: int = 0,
    ) -> None:
        self.orch = Orchestrator()
        self.max_generations = max_generations
        self.rl_episodes = rl_episodes
        self.llm_rounds = llm_rounds
        self.use_llm_generator = use_llm_generator
        self.g3_mode = g3_mode
        self.llm_propose_n = llm_propose_n
        self.generator_limit = generator_limit

    # ── main loop ─────────────────────────────────────────────────────────────

    def run(self) -> Optional[str]:
        """Returns the name of the proven conjecture, or None."""
        empty_streak = 0
        for gen in range(1, self.max_generations + 1):
            sep = "=" * 70
            print(f"\n{sep}\n[Evolution] Generation {gen}/{self.max_generations}\n{sep}",
                  flush=True)

            try:
                ConjectureGenerator(
                    client=self.orch.client if self.use_llm_generator else None,
                    limit=self.generator_limit,
                    g3_mode=self.g3_mode,
                    llm_propose_n=self.llm_propose_n,
                ).run()
            except Exception as exc:
                print(f"[Evolution] generator error: {exc}", flush=True)

            new_specs = get_conjectures_by_status("new")
            if not new_specs:
                empty_streak += 1
                print(f"[Evolution] no new conjectures "
                      f"(empty streak {empty_streak}/2)", flush=True)
                if empty_streak >= 2:
                    print("[Evolution] generator exhausted — stopping.")
                    return None
                continue
            empty_streak = 0
            print(f"[Evolution] {len(new_specs)} new conjecture(s) to evaluate",
                  flush=True)

            for spec in new_specs:
                outcome = self._evaluate(spec)
                print(f"[Evolution] {spec.name}: {outcome.upper()}", flush=True)
                if outcome == "proven":
                    print(f"\n[Evolution] {spec.name} PROVED — stopping loop.")
                    return spec.name

        print("[Evolution] max generations reached without a proof.")
        return None

    # ── single-conjecture evaluation ──────────────────────────────────────────

    def _evaluate(self, spec: ConjectureSpec) -> str:
        c = ParsedConjecture.from_conjecture_spec(spec)
        print(f"\n[Evolution] ── {c.conjecture_id} ({c.short_id})  "
              f"{c.statement_latex}", flush=True)

        try:
            ce_info = self.orch._run_ce_search(c, self.rl_episodes, self.llm_rounds)
        except Exception as exc:
            print(f"[Evolution] CE search error for {c.conjecture_id}: {exc}",
                  flush=True)
            ce_info = None

        if ce_info:
            if ce_info.get("found_by") != "rl_agent":
                out_path = _write_ce_json(c, ce_info, self.orch._ce_dir)
                print(f"[Output] CE JSON → {out_path}", flush=True)
            return self._record_refuted(spec, ce_info.get("p_vector"),
                                        ce_info.get("violation_detail", ""))

        try:
            outcome = self.orch._run_prover(c)
        except Exception as exc:
            print(f"[Evolution] prover error for {c.conjecture_id}: {exc}",
                  flush=True)
            outcome = "failed"

        if outcome == "skipped_entailment":
            # the precheck's plantri decision may have just refuted it
            ce_path = self.orch._ce_dir / c.short_id / f"{c.short_id}.json"
            if ce_path.exists():
                try:
                    ce = json.loads(ce_path.read_text()).get("counterexample", {})
                    pv = {k[1:]: v for k, v in ce.items()
                          if k.startswith("p") and k[1:].isdigit() and v}
                except Exception:
                    pv, ce = None, {}
                return self._record_refuted(spec, pv, "refuted by plantri "
                                            "decision in entailment precheck")

        if outcome == "proved":
            proof = _resolve_lean_output(c, self.orch._no_ce_dir)
            set_conjecture_status(spec.name, "proven",
                                  detail={"proof": str(proof) if proof else None})
            add_success_hint(spec.formula,
                             f"proved in Lean ({proof or 'output path unresolved'})")
            return "proven"

        set_conjecture_status(spec.name, "prover_failed",
                              detail={"outcome": outcome})
        add_failure_hint(spec.formula,
                         f"prover {outcome}: survived CE search but could not "
                         f"be proved from the current Inventory")
        return "prover_failed"

    def _record_refuted(self, spec: ConjectureSpec, pv, violation: str) -> str:
        set_conjecture_status(spec.name, "refuted",
                              detail={"ce_p_vector": _pv_jsonable(pv),
                                      "violation": violation})
        add_failure_hint(spec.formula, f"refuted by CE {pv} ({violation})")
        return "refuted"


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Evolution loop: generate conjectures → CE search → prover, "
                    "with success/failure hints feeding the next generation.")
    ap.add_argument("--max-generations", type=int, default=10)
    ap.add_argument("--rl-episodes", type=int, default=600)
    ap.add_argument("--llm-rounds", type=int, default=15)
    ap.add_argument("--g3-mode", default="fast", choices=["fast", "standard", "deep"])
    ap.add_argument("--llm-propose-n", type=int, default=8)
    ap.add_argument("--generator-limit", type=int, default=0,
                    help="cap accepted conjectures per generation (0 = no cap)")
    ap.add_argument("--no-llm-gen", action="store_true",
                    help="disable the LLM co-generator/reviewer (pure Graffiti3)")
    args = ap.parse_args()

    EvolutionLoop(
        max_generations=args.max_generations,
        rl_episodes=args.rl_episodes,
        llm_rounds=args.llm_rounds,
        use_llm_generator=not args.no_llm_gen,
        g3_mode=args.g3_mode,
        llm_propose_n=args.llm_propose_n,
        generator_limit=args.generator_limit,
    ).run()


if __name__ == "__main__":
    main()
