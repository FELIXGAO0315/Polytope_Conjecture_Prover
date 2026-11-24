# Pre-registration — external-style baseline `llm_direct` vs. the closed loop

**Pre-registered:** 2026-11-18, America/New_York (box TZ = EST), before any `llm_direct`
run started. This file is committed on branch `revision-iclr27` **before** the first run
log timestamp.

**Purpose.** Reviewer z7Pb notes the loop is compared "only against its own components."
This pre-registers ONE external-style baseline: an LLM proposes conjectures directly — no
Graffiti3, no other conjecture source, no outcome feedback — with everything downstream
identical to the F2b open-loop ablation. The result will be reported whatever it is.

## Code under test

- **Arm code commit (the exact code that will be run):** `1131a269` on `revision-iclr27`
  (`supplement_experiment/llm_direct_baseline/f2b_llmdirect_{setup,driver,smoke,metrics}.py`, `run_f2b_llmdirect.sh`,
  `f2b_caps.json`, plus `f2_metrics.py` / `f2b_metrics.py` copied verbatim from the F2b
  harness).
- **Pipeline snapshot:** `/tmp/llm_direct_snap_a1eab93`, verified byte-identical (`diff -r` exit 0,
  `agent/` tree) to commit `a1eab93`, which is confirmed to be the exact pipeline code the
  F2b closed/open runs used (same snapshot each F2b arm was copied from; `a1eab93` is an
  ancestor of `revision-iclr27`).
- **Unchanged metric definitions and novelty baseline** are inherited from the F2b
  pre-registration `2999a6c` (on `analysis/revision-baseline`), copied into the repo at
  `supplement_experiment/llm_direct_baseline/out/f2b_prereg_2999a6c.json`. The **closed/open comparison numbers** come
  from the F2b results `314ed95`, copied in at `supplement_experiment/llm_direct_baseline/out/f2b_results_314ed95.json`.
  Those two arms are **not** rerun.

## 1. Arm definition: `llm_direct`

`llm_direct` is the F2b **open** arm with every non-LLM Stage-1 source turned off, so the LLM
co-proposer is the only conjecture source. All patches are applied, arm-isolated, to a fresh
copy of the snapshot under `/home/felix_gao/llm_direct_exp/f2b_llmdirect/seed<seed>/llm_direct`.
Relative to the open arm, the ONLY changes are:

- **Sources off.** Graffiti3 full-table pass, Graffiti3 stratified pass, and the
  support-function miner are set to produce no candidates (`discovered=[]`,
  `stratified_formulas=[]`, `mined=[]`). The dynamic-cell pass and the mutation engine are
  already off in the open arm (open-arm patch) and stay off. The LLM co-proposer is the only
  source.
- **Same model / effort / temperature / prompt as the open arm.** Model = `model_main` =
  `claude-opus-4-7` (Opus 4.7); `effort="low"`; no temperature is set anywhere (the generator
  pins none — API default, same uncontrolled stochasticity the F2b prereg notes). The propose
  prompt template (`CONJ_GEN_PROPOSE_PROMPT` + `CONJ_GEN_SYSTEM`) is unchanged; the outcome
  hint blocks (PROVED / REFUTED / CE-SURVIVED / SURVIVORS) and the FOCUS CELLS block are empty
  exactly as in the open arm (open-arm patch sets `signals` empty and `focus_cells=[]`).
  **Prompt diff vs the open arm = empty.** The propose prompt does NOT embed any Graffiti3,
  miner, or other this-run source output as context; the only source-derived context is the
  frozen registry (`existing_block` HIGH-TRL templates + registry-coverage), identical in both
  arms and the same registry the novelty metric is measured against — kept, per the pre-run
  decision.
- **Candidate cap.** For each seed and generation, `llm_propose_n` is set to the number of
  candidates the **closed arm evaluated** in the same seed+generation (the pre-gate proposal
  count = accepted+rejected in the closed-arm generator run log), read from `f2b_caps.json`
  (derived from `314ed95`): gen1 = 113 for every seed; gen2 = 127 (s41) / 128 (s7) / 128
  (s123) / 128 (s2024) / 117 (s99). The LLM may return a few more than requested; the valid
  `if…` formulas are **truncated to `n_requested`** so no more than the cap reaches the gates.
  If the LLM produces **fewer valid formulas than the cap**, the shortfall
  (`cap − valid_returned`) is recorded; there is NO retry beyond the open arm's single-call
  budget.
- **Everything after proposal is identical to the open arm.** The 7 gates run unchanged
  (dedup; `_consistent_with_verified` entailment/syntax gate, fail-closed; shape-repeat
  tightness; `_drop_lp_overfit`; `_drop_trivial_rhs`; `_drop_semantic_dupes`), then the
  advisory LLM review (Opus 4.7, effort low). Downstream is deterministic **B** only
  (witness-pool replay → plantri-pool replay → Eberhard-lattice walk 200k steps/60 restarts →
  plantri exhaustive screen; `client=None`; NO RL / LLM / Hopper / stochastic constructor).
  The **prover is disabled**; a no-CE conjecture is a survivor. **Two generations.** **No
  outcome feedback between generations** (open-loop).
- **Seeds:** 41, 7, 123, 2024, 99 (`PYTHONHASHSEED=<seed>`, `CE_CONSTRUCT_SEED=<seed>`; LLM
  adds uncontrolled API stochasticity on top, as in F2b).

### Budget (fixed up front; no verify-then-adjust)

- Propose call: **timeout 600 s, `max_attempts=1`** (no retry), **`max_tokens=32000`** via the
  `CLAUDE_CODE_MAX_OUTPUT_TOKENS` environment variable (honored by the bundled CLI;
  `_query_once` forwards it through `os.environ`). 32000 < Opus 4.7's 128K output ceiling, so
  the explicit cap stands. The smoke check on this exact code commit (one standalone propose
  call at the largest cap, n=128, outside all experiment workspaces, `dry_run`, no downstream,
  no metric computed) confirmed the response parses in full (131 valid formulas returned, 0
  invalid, truncated to the 128 cap, no JSON truncation) with total elapsed **215 s** (propose
  + advisory review) — well under 600 s, so the timeout is **not** raised. Per protocol: had the
  smoke exceeded 600 s, the timeout would have been raised once and re-committed before any run;
  it was not.
- Advisory review call: unchanged from the open arm (effort low, timeout 180 s, `max_attempts=1`).
- Stale log string: the patched propose call still prints "≤60s" (a cosmetic leftover); the
  actual per-call timeout passed is 600 s. No functional effect.

### Infrastructure-failure policy (NOT counted as shortfall)

In `llm_direct` the single propose call is the only conjecture source, so an API error,
rate-limit, timeout, or empty/truncated/zero-valid response would zero a generation for reasons
unrelated to the method. Any such failure is treated as a **crash**: the patched `_llm_propose`
raises, the driver exits non-zero, and the runner reruns that seed **from scratch with
unchanged settings**, up to 3 attempts; every occurrence (with cause) is recorded in
`seed<seed>_failures.log`. Shortfall is recorded **only** for valid responses that simply
contain fewer formulas than the cap.

### Render failures / invalid LLM outputs

A returned string that is not a valid `if…` formula (and a parse/empty/truncated JSON) is the
LLM analog of a Graffiti3 render failure: it does not enter the gate loop. Non-`if` strings are
counted as **invalid LLM outputs** (per generation) and excluded from the candidate count; a
JSON parse failure or zero valid formulas is an infra crash (above), not shortfall.

## 2. Metrics

- **Primary — novel hypothesis cells over two generations.** `primary__novel_hypothesis_cells_vs_frozen`
  from `f2b_metrics.py` (identical code and `hyp_cell` definition as the F2b ablation):
  the number of DISTINCT hypothesis cells among the arm's accepted conjectures (gen1 + gen2)
  that are NOT covered by the frozen `a1eab93` registry (`baseline.json["reg_cells"]`, captured
  pre-run by `f2_metrics.py`). A hypothesis cell is the sorted set of non-`is_simple` atoms in
  the `if (...)` clause. The `llm_direct` baseline is the same frozen registry as closed/open.
- **Secondary:** distinct accepted hypothesis cells (`sec__distinct_hypothesis_cells_accepted`);
  accepted conjectures (`accepted_conjectures`); refuted conjectures (`sec__refuted_count`,
  plus by-tier); survivors; LLM-review drops; and **invalid/unparseable LLM outputs** (summed
  from the per-generation propose instrumentation), plus per-generation shortfall.

## 3. Comparison and decision rule

- Compare `llm_direct` against the **existing** closed-arm and open-arm numbers for seeds
  41, 7, 123, 2024, 99 from `314ed95` (those arms are not rerun).
- **Decision rule:** the closed loop "beats" `llm_direct` iff it has more novel hypothesis
  cells than `llm_direct` in **at least 3 of the 5 seeds**. (Three-seed fallback, only if the
  deadline forces it: 41, 7, 123 — the first three seeds in the original pre-registered F2b
  order — with the rule "at least 2 of 3". The wall-time estimate shows all five finish by the
  deadline, so the five-seed rule applies.)

## 4. Reporting and isolation

- **All results will be reported regardless of outcome**, including any seed where
  `llm_direct` wins, and every deviation from this pre-registration however small.
- Isolation: each seed is a fresh full copy of the `a1eab93` snapshot under
  `/home/felix_gao/llm_direct_exp/f2b_llmdirect/seed<seed>/llm_direct`. The F2b closed/open
  workspaces and all repo/registry/witness-pool/cache state outside that tree are never
  touched. Concurrency ≤ 2 seeds at a time (recorded in the runner log). Hard stop
  2026-11-18 23:00 America/New_York.
- After the runs, the run logs, generator run logs, propose instrumentation, baselines, and
  computed metrics are copied out into `supplement_experiment/llm_direct_baseline/out/llm_direct/` and committed, so nothing
  depends on the `/tmp` snapshot.
