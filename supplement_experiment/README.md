# supplement_experiment

Reviewer-requested supplementary experiments and artifacts. **None of this is part
of the core discovery loop** (`agent/`, `polib/`, `conjectures/`, `output/`,
`run.py`, `formalize.py`) — it can be removed without affecting the pipeline.

All scripts are run from the repository root, e.g.
`python3 supplement_experiment/independence_check.py`.

| Path | What it is |
|------|------------|
| `ablation/` | Ablation studies (E4/E6/E7/E8): feedback ablation, open-conjecture sensitivity, campaign replay, downstream-feedback, leave-one-out, stochastic. Code + `out/` results. |
| `llm_direct_baseline/` | F2b "llm_direct" external baseline — the LLM co-proposer as the *only* conjecture source (all other Stage-1 sources off), 5 seeds, compared against the closed/open loop. Code + `out/` run logs. |
| `prereg_llm_direct.md` | Pre-registration for the `llm_direct` baseline (arm definition, budget, metrics, decision rule). |
| `export_training_data.py`, `export/` | Export the repository's *decided* conjectures into a trustworthy labeled dataset: re-verified counterexamples (exact arithmetic) + qualifying zero-`sorry` Lean proofs. |
| `tests/` | End-to-end tests for the export — `python3 -m pytest supplement_experiment/tests`. |
| `independence_check.py` | Offline check that the proved conjectures are not merely nonnegative linear combinations of the known theorems (Euler / Jucovič / Barnette). Analysis only; never a pipeline gate. |
