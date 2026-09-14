# Polytope Conjecture Prover — Agent v3.5 plus

A **closed-loop autonomous discovery system** for conjectures about simple convex 3-polytopes. One command runs the full cycle:

1. **Generate** — `ConjectureGenerator` (Graffiti3 + an LLM co-proposer, both hint-aware) discovers new conjectures over a p-vector discovery table;
2. **Refute** — every new conjecture is attacked by the CE pipeline: a lattice random walk, an exhaustive plantri screen (decisive: verdicts are proofs by construction or by exhaustion), and four parallel stochastic tracks (LLM + RL + Hopper + constructor double check); the screen and the double check are the two roles of `PlantriCEFinder`;
3. **Prove** — survivors with no counterexample go to the Lean 4 ProverAgent (zero-`sorry` policy, closed axiom base);
4. **Learn** — every outcome (refuted / proven / prover-failed) becomes a success/failure hint that steers the next generation.

Every counterexample is backed by an **explicit verified witness polytope** (5 independent checks); every proof is a **compiling Lean 4 file** that uses only the hand-curated `Inventory.lean` axiom base.

```bash
# one-click autonomous mode: generate → CE search → prove → outcomes feed the next generation
python -m run project
```

---

## What's New in v3.5 plus (2026-07-04)

### 🎉 C201 proved; C215 brings the current total to four

`python -m formalize C201` went end-to-end: 7 nodes, zero `sorry`, root
theorem compiles. C201 (`p4=0 ∧ p5=0 ∧ Σ₇₊ ≥ 1 ⟹ p6 ≥ −Σ₇₊ + 2`) closes
through `P6InequalityPart` — the m≥6-gated Jucovič inequality part in
`Inventory.lean` — combined with the per-term coefficient bound
`⌊(k+1)/2⌋ − 6 ≥ −2` for k ≥ 7, giving `3·p6 ≥ 12 − 2·Σ₇₊ = 10` in the
single-big-face case. Lesson recorded: that lemma is stronger than the
occupation section suggests — check its reach BEFORE declaring a survivor
unprovable (the pre-run analysis here predicted a missing axiom; the prover
found the route on its own).

C215 is also now a complete Lean artifact: with `p4 = p5 = 0` and
`f2 ≥ 7`, it proves `3·p6 + 2·Σ₇₊ ≥ 12` (equivalently
`p6 ≥ -2/3·Σ₇₊ + 4`).

### The first genuine open conjectures: C193, C195, C198

The v3.5 batch produced three survivors that beat the ENTIRE arsenal —
witness replay, pool replay, random walk, exhaustive plantri screen,
constructor double check, RL, Hopper, LLM — and then failed the prover for
a reason that is now precisely understood. All three are "reverse bounds"
`p6 ≥ −c·Σ₇₊ + d`: they only constrain maps with ≤ 1 big face, so a
counterexample must be an **ocean of small faces enclosing at most one
exceptional face** — a configuration that is arithmetically feasible but
(on all evidence) geometrically impossible. The entailment pre-check's
countermodels double as a non-derivability proof: the conclusions are NOT
logical consequences of Inventory's arithmetic content, so the prover
fails exactly at the case that needs realizability — not a skill issue,
a missing-theorem issue.

- **C193** (`p3=0, f2≥17 ⟹ p6 ≥ −2Σ₇₊+4`) — needs: *no simple 3-polytope
  is pentagons(+squares) + exactly one k≥7-gon + ≤1 hexagon*. ~170
  candidates decided by plantri exhaustion (pipeline screen + an
  independent audit up to f2=30), zero realizable. No such theorem in
  Inventory, Mathlib, or (as far as we know) the literature — nearest
  neighbors are Eberhard's theorem, Grünbaum–Motzkin's fullerene p6=1
  impossibility, and the (5,6,k)-sphere literature. Prover failed at
  `C193_CaseOneS` after proving the other 4 sub-lemmas: `linarith` rightly
  finds no contradiction, because arithmetically there is none.
- **C195** (`p5=0, f2≥7 ⟹ p6 ≥ −Σ₇₊+2`) — the smallest gap: one textbook
  fact (`f2 ≥ m+1`, a k-gon has k distinct neighbors) closes the whole
  S=1 case, leaving a single finite hole: `{4:6, 6:1}` is plantri-proven
  non-realizable but invisible to the axiom base.
- **C198** (`p4=0, f2≥17 ⟹ p6 ≥ −2Σ₇₊+4`) — the triangle variant of
  C193's missing lemma.
- **C199 deleted** — semantically identical to C193 (`−3Σ₇₊+5` vs
  `−2Σ₇₊+4` demand the same p6 on every DS-feasible p-vector; their 144
  arithmetic CE candidates coincide exactly). See the new generator
  filter below.

Current standing: **proved 4** (C104, C124, C201, C215), **refuted 204**
(witness-verified; 206 CE artifact directories total, excluding C21 and
C22 because their `witness_graph` is empty/missing), **open 3** among
numbered C-series conjectures (C193, C195, C198 — each with its missing
lemma documented).

### Soundness fix: a failed formalization can no longer be recorded "proven"

Step 8 of the prover saves a partial artifact (the proved sub-lemmas,
zero `sorry`) even when the run FAILS — and `reconcile_from_artifacts`
treated any sorry-free `.lean` under `conjecture_without_ce/` as a full
proof. C193's failed run landed in the `proved` bucket, and the audit
found C1 had been sitting there since 06-30 with `-- Failed (1): C1_Main`
in its own header. Fixes (`agent/conjectures.py`):

- **Proof qualification**: an artifact counts only if it has zero active
  `sorry`, no `-- Failed (n>0)` header line, AND the root theorem
  declaration (`theorem C<num>`, `_Main` variant accepted) is present.
  Anything else is a *partial* artifact.
- **Demotion pass**: an entry sitting in `proved` without a qualifying
  artifact is demoted — to `prover_failed` when a partial artifact shows
  the prover ran and lost, to `new` when nothing is on disk — and the
  stale `status_detail.proof` pointer is removed. Disk artifacts are now
  the single source of truth in BOTH directions.
- **Update (2026-07-04, same day)**: step 8 now writes **no `.lean`
  artifact at all** on a failed run — `output/conjecture_without_ce/`
  holds complete proofs only (currently exactly c104, c124, c201, c215).
  Nothing is lost: a failed run's proved sub-lemmas persist in
  `Polib.lean` for the future re-run. The pre-existing partial artifacts
  (c1, c193, c195) were deleted and their stale `status_detail.partial`
  pointers cleaned; the reconcile qualification guard stays as a
  belt-and-suspenders check against stray or legacy files.

### Generator: semantic-duplicate filter (the C193 ≡ C199 lesson)

Two formulas with different RHS coefficients can still be the same
conjecture: their demands differ only on arithmetically infeasible
p-vectors. New filter in the accept pipeline (after the trivial-RHS
guard, before LLM review): each candidate gets an **attack-surface
signature** — (sorted hypothesis atoms, frozenset of its
`enumerate_ce_candidates` p-vectors under pinned bounds) — and is dropped
when it matches an ALIVE conjecture (unsolved + proved) or an earlier
candidate in the batch. Refuted entries are deliberately not compared:
their duplicates die in Stage 0 for one witness replay, and 204 extra
witness-verified refutation signatures would dominate the filter's cost.
Conservative by design:
parse failure, empty candidate set, or truncation at the 400 cap exempts
the candidate (two tight bounds must not merge on the empty set).

### Log hygiene: stop_event cancellation is not a failure

When one CE track wins, the losers abort mid-LLM-call with
`call aborted: stop_event set`. That expected cancellation used to
produce two lies per settled search: a `[claude_sdk escalate] … next try:
effort=high` line (there is no next try — the retry loop re-raises
immediately) and `[LLM ce finding] disabled — CLI preflight failed`
(reads like a tripped breaker; the search was simply over).
`claude_sdk._call` now re-raises stop_event aborts immediately — no
escalate log, no backoff, no phantom retries — and skips the escalate
message on genuinely final attempts; the LLM preflight exits silently on
stop_event, same rule as the round loop. Real failures still log loudly.

### Housekeeping: dead-code sweep (−302 lines, 1 file)

Whole-repo reconnaissance (3 parallel read-only scans, every finding
re-verified by grep before deletion):

- `agent/prover/lean_codegen.py` **330 → 46 lines**: 11 functions with
  zero external references deleted (`rename_last_decl`, `strip_markdown`,
  `format_errors_for_prompt`, …) — the last orphans of the legacy
  `_generate_lean` fix loop retired in v3.4. Survivors: `has_sorry`,
  `face_count_tokens`.
- `LEAN_PREAMBLE` deleted from `prompts/lean_generation.py` — its only
  consumer was the dead `ensure_preamble` (supersedes the v3.4 note that
  kept it).
- `agent/conjecture_generator/backfill_iris.py` deleted — one-off IRIS
  backfill, verified 100% complete (200/200 entries scored).
- `agent/exceptions.py:ParseError`, `Config.max_sorry_total` (env knob
  never read — and misleading under the zero-`sorry` policy), and
  `conjectures.py:write_conjectures_dataset()` (never called) deleted.
- Deliberately KEPT after inspection: `plantri_harvest.py` (pool
  maintenance tool), both `__main__.py` entry shims, `store.json` +
  `logs/` (actively written by `StoreManager` / `FormalizationLogger`),
  `draw_ce_witness.py` (renders every saved CE), the legacy
  `solved`→`failed` load fold, and all `set_pdeathsig` wiring.
- Regression after the sweep: `compileall` clean, 64/64 modules import,
  functional spot checks on every edited module (Config, lean_codegen,
  exceptions, reconcile idempotency, semantic-dup signature) all pass.

---

## What's New in v3.5 (2026-07-02)

### The generator can no longer run dry — conjectures now breed conjectures

The deterministic Graffiti3 source is a pure function of (table, strata): a
frozen pool meant identical candidates every generation, two empty
generations, loop stop. v3.5 makes every existing outcome a SOURCE of new
candidates:

- **Mutation engine** (`agent/conjecture_generator/tools/mutations.py`) —
  the dalmatian dynamic, made explicit. From every **refuted** bound:
  `repair-const` (shift the RHS constant just past the worst violator,
  snapped outward to denominator ≤ 6) and `repair-f2` (raise/add the
  `f_2>=_N` atom to exclude every known violator, then chain a
  constant-sharpen so the repair lands ON the pool hull). From every
  **proved / survivor / prover-stuck** bound: `sharpen-const` (pull a slack
  constant to pool contact) and `weaken-hyp` (drop one hypothesis atom —
  a strictly stronger theorem candidate). All exact-Fraction arithmetic,
  self-verified against the full pool before emission, ≤ 12 per run,
  most-recent outcomes first. **The fuel supply grows with every result.**
- **Dynamic cells** — each run picks up to 3 uncovered hypothesis-atom
  pairs (pool support ≥ 60, zero registered conjectures) and aims a
  dedicated Graffiti3 pass at them, rotated by registry size so successive
  runs attack different territory.
- **Shape filter retired → tight-repair rule.** The old hard drop on
  refuted shapes blocked exactly the repair loop above. Now the pool gate
  itself kills exact re-fits (every CE witness is in the gate data), and a
  shape-repeat is admitted only when it **touches the pool hull**
  (`min_slack = 0`) — extremal repairs pass, slack near-duplicates don't.
- **Full-pool hard gate.** `_consistent_with_verified` now checks ~25k
  verified p-vectors (sampled table ∪ full plantri harvest ∪ every CE
  witness) instead of the 60-per-f₂-bucket LP sample — twice a candidate
  had passed the sampled gate only to die minutes later in Stage 0.
- **Vacuity gate** (the C137 lesson). `p6 >= RHS` whose hypothesis atoms
  already force `sup(RHS) ≤ 0` is information-free — un-refutable (nothing
  to refute) and trivially provable, the perfect exploit of a loop that
  stops on "proved". Detected by deterministic interval arithmetic and
  dropped at generation; the heuristic TRL≈0 warning stays warn-only.
- **Support-function miner** (`tools/support_miner.py`) — the C104
  factory. C104 is geometrically a lower hull edge of the pool: a tight
  supporting line on a small-face-starved cell, forced by Dehn-Sommerville.
  Dalmatian LP surfaces that class only by accident; the miner sweeps it
  systematically — for every (cell × RHS variable × denominator-≤6 slope),
  compute the exact support constant `c = min(p6 − a·v)` over the full
  pool and emit `p6 ≥ a·v + c` when it is a true edge (≥ 2 touching rows
  at distinct v), supported (≥ 30 rows) and non-vacuous. Tight and
  consistent BY CONSTRUCTION; acceptance test: the miner re-derives C104
  verbatim from the pool. Lower bounds only — the provable direction.
- **Three-strikes lineage rule** (mutation engine) — a shape refuted ≥ 3
  times keeps dying because its violator family scales with f₂ (hexagon
  bands exist at every size); repairs for such lineages stop.
- **Alive-only cell coverage** — dynamic-cell territory is claimed only by
  unsolved/proved conjectures; refuted-only cells reopen for boundary
  re-fits against the grown pool.
- **LLM propose** default 8 → 12; the prompt now has explicit
  EXPLORE / SHARPEN / REPAIR task modes plus a FOCUS CELLS block.

Measured effect: same data, **no LLM**, previous config accepted 0 — the
full v3.5 stack accepts 51, including 14 miner-class negative-slope lower
bounds (the accumulated repair debt of 150+ refutations plus reopened
territory; later generations shrink naturally as candidates register).
First runs after the upgrade are a burst — `--generator-limit 15` bounds a
generation.

### Signals are derived, never stored (hints.json deleted)

The old side-channel hint store rotted the moment a prover run bypassed the
evolution loop — 4 Lean-proved theorems and 204 witness-verified
refutations now reach the generator. Every prompt signal (**proved /
refuted / prover-stuck / survivor**) is derived fresh from
`conjectures.json` + `registry.json` + on-disk artifacts at generation time
(`tools/signals.py`), and
`reconcile_from_artifacts()` (agent/conjectures.py) folds on-disk outcomes
(CE JSON, proof `.lean`, evolution-loop records) back into
`conjectures.json` from **every** entry point — `run.py`, `formalize`,
the evolution loop, and the generator itself. Stale `prover_failed`
records contradicted by later evidence self-heal (deleted). Proved-but-
vacuous theorems (touch = 0 on the pool) are excluded from the PROVED
prompt block — an empty bound must not become a template.

### Step 6 deep check: Lean itself is now the arbiter

C137 was proved sorry-free and killed by a textual false positive
(`∑ k in` vs `∑ k ∈` — the pipeline's own autofix — plus an explicit
`(… : ℤ)` ascription the elaborator inserts anyway). Two fixes:

- `_norm` collapses known-equivalent notation (big-operator `in`/`∈`,
  atomic numeric ascriptions) — general `∈`/`in` still distinct.
- **Defeq arbitration**: when the textual comparison still fails, the gate
  appends `example : ∀ <locked binders>, <locked conclusion> := <name>` to
  the saved code and compiles it. Lean's definitional equality is stricter
  than any string match against real drift (an added hypothesis cannot
  typecheck) while being immune to notation noise. Not a weakening — an
  upgrade to the mathematically correct comparison.

Footnote: C137 itself turned out to be *vacuously true* (hypothesis forces
RHS ≤ −1 < 0 ≤ p6) and was deleted end-to-end (dataset, registry, proof
artifacts, Polib sections, store caches) — hence the vacuity gate above.

### Housekeeping

- **Post-run scratch cleanup**: `wipe_temp_scratch()` removes
  `polib/Polib/_Temp` sources **and** their `.lake` build artifacts after
  every run (once measured at 1217 files / 1.6 GB), then removes the empty
  scaffolding dirs; everything is auto-recreated on demand. Hooked into all
  three entry points; a startup prune covers killed runs.
- New conjectures use bare `C<n>` names (global suffix continues);
  `run.py` name resolution accepts both `auto_…_<n>` and `C<n>`.
- Registering a conjecture now also ensures its `registry.json` entry, so
  survivor counters accumulate regardless of which CE entry point runs.

## What's New in v3.4

### 🎉 First successful end-to-end formalization (2026-07-01)

C104 (`if p_4=0 ∧ p_5≤2 ∧ f_2≥7, then 2·p_6 ≥ 4 − Σ_{k≥7} p_k`) was
proved by the pipeline for the **first time** on 2026-07-01 — 101-line
Lean 4 file, **zero new sorry**, using only the accepted
`Inventory.lean` axiom base (`Juc_EulerFormula`, `Juc_InequalityPart`,
`Barnette_P6Bound`, `p_range`).  The proof file lives at
[`output/conjecture_without_ce/c104/c104.lean`](output/conjecture_without_ce/c104/c104.lean), with a companion informal proof at [`c104.md`](output/conjecture_without_ce/c104/c104.md).

Every strategic decision (blueprint decomposition, tactic choice,
Inventory lemma selection) was made by the LLM — the Python layer only
enforces universal Lean-schema gates (`IsMap` required,
`SimplyCon3ConnectedMap 0` mandatory, no `IsSimple`/`maps.f2`, no
new sorry), plantri-refutation soundness on intermediates, and the
retry-with-correction loop.  **No human-injected proof steps, no
problem-specific hints, no cheating.**

### Prover module: aggressive dead-code cleanup (~2400 lines + 6 files deleted)

The legacy compile-fix-loop machinery (`_generate_lean`,
`_partial_solver`, `_compile_loop`, `_targeted_fix*`,
`_try_mechanical_*`, `_inventory_template_probe`, `_PROOF_PATTERNS`,
`_build_sandwich_summary`, and every hint-generator that fed them) was
retired when the new single-session `agent/prover/proof_agent.py` took
over per-node proving.  The dead scaffolding sat there for weeks —
this release deletes it.

**Files removed** (all confirmed 0 callers via grep):

- `agent/prover/_strategies_mixin.py` (empty placeholder MRO shim)
- `agent/prover/_helpers.py` (three functions, all consumed by one caller)
- `agent/prover/tools/prompt_optimizer.py` (dep-import trimming for `_generate_lean`)
- `agent/prover/tools/output_search.py` (compiled-output ref lookup for `_generate_lean`)
- `agent/prover/tools/loogle_validator.py` (real-Mathlib-name suggestion for `_generate_lean`)
- `agent/prover/tools/llm_hint_generator.py` (LLM hint tier for `_generate_lean`)
- `agent/prover/prompts/inventory.py` (rendered `FIX_LOOP_POLIB_REF`, dead)

**Modules slimmed:**

- `agent/prover/agent.py`: 1037 → 351 lines (−686). All hint fields,
  pattern-injection tables, sandwich summaries, and per-error hint
  helpers removed.  FormalizerAgent is now just cache helpers + polib
  bootstrap + a `formalize()` delegate.
- `agent/prover/tools/search.py`: ~950 → 210 lines (−740). Kept
  `PolibSearch` (polib index + fuzzy TF-IDF alias) + `SavedEntry`;
  dropped `LoogleSearch`, `MathlibSearch`, `GitHubLean4Search`,
  `CombinedHintGenerator`, `LLMProofReasoningHintGenerator` — all
  five only fed dead `_generate_lean` paths.
- `agent/prover/prompts/lean_generation.py`: 268 → 121 lines.  Kept
  `SHARED_MODULE_CONTENT` (used by blueprint cache key) and
  `LEAN_PREAMBLE` (used by `lean_codegen`).  Deleted
  `LEAN_GENERATION_PROMPT`, `LEAN_GENERATION_SYSTEM_PROMPT`,
  `FIX_LOOP_POLIB_REF`, and every `_GOAL_CONTEXT_*` / `_GOAL_INSTR_*`
  template that was consumed only by `_generate_lean`.

### The bug fixes that unlocked C104 (2026-06-30 → 2026-07-01)

Every one of these was a real dead-lock the run walked into:

1. **Per-node `LockedGoal` in step 4** — proof_agent was receiving the
   MAIN theorem's signature for every sub-lemma, so the LLM wrote
   `theorem C104` in every file, and our acceptance check (which
   searched for `theorem {node_id}`) correctly rejected all of them
   as sub-lemma proofs.  Fixed: sub-lemmas now get a per-node
   `LockedGoal` built from `node.lean_signature`; main target still
   uses the step-2 lock.
2. **`_signature_compiles` pre-check** — before Opus burns its
   1500-second budget on a sub-lemma, Python now compiles
   `{sig} := by sorry` against Mathlib+Inventory+Polib and fails
   fast if the type doesn't check.  Catches planner-side syntax /
   arity / namespace errors in seconds instead of minutes.
3. **`_autofix_lean_sig`** — Lean-3 `∑ k in Finset.…` gets rewritten
   to Lean-4 `∑ k ∈ Finset.…` (same for `∏`, `⋃`, `⋂`) before the sig
   is used or handed to Opus.  Planner LLMs often emit the Lean-3
   form because it dominates training data; this is a pure syntax
   normalization, not a semantic patch.
4. **`_evict_blueprint_for_bad_sig`** — when the sig-check fails, the
   blueprint cache is cleared so the next run re-plans instead of
   pulling the same broken blueprint out of `store.json` and looping
   on it.
5. **Verbatim-signature gate demoted to INFO** — the quality checker
   used to require the locked signature as a verbatim substring of
   the emitted code, but Opus frequently adds `open Finset` or minor
   binder-spacing changes that break substring match while every
   semantic check (constant fidelity, conclusion match, hypotheses
   covered, overall faithfulness) still passes.  Verbatim match is
   now logged as `INFO` — the semantic checks are the load-bearing
   guarantee.  Fixes the "proof_agent: proved / then: [fail] — ok"
   deadlock that was blocking C104's main theorem for 3 retries in a
   row.
6. **Step 5 retry now honors `verbose`** — the retry loop was hard-
   coded to `verbose=False`, so a 25-minute silent retry looked
   indistinguishable from a hang.  Retries now stream the same
   `[proof-agent]` / `[lean_compile #N]` telemetry as first attempts.
7. **Absolute paths in proof_agent user message** — the LLM used to
   spend its first 4-6 tool calls hunting the workspace with `find` /
   `ls`, sometimes typo'ing `Polytope-Conjecture-Prover` (hyphens).
   The `## Working directory` block in the user message now gives
   exact absolute paths for `Inventory.lean`, `Polib.lean`, and the
   Mathlib root.
8. **No-new-sorry policy hard-enforced end-to-end** — `polib_manager
   .save` now raises `PolibSaveError` on any `sorry`, planner hints
   filter to `status == "proved"` only, and `_load_polib_code`
   refuses to read `(partial)` sections.  Every `partial` code path
   in `pipeline.py` / `FormalizationResult` was removed as dead.  The
   `_sorry_inc` / `_sorry_get` counter (always 0 in practice) was
   deleted with it, along with the entire "SORRY REPORT" block in
   `_write_complete_proof_file`.
9. **`_step2_lock_goal` no longer caches best-effort signatures** —
   the loader already refused to return unconfirmed cache entries, so
   writing them out was pure disk pollution.  Now unconfirmed sigs
   are logged and skipped; only confirmed ones persist.
10. **`_check_signature_static` replaces the LLM `GoalValidator`** —
    the old validator prompt did 6 syntactic checks and 3 semantic
    ones; six of the syntactic checks were pure regex work.  All
    checks are now Python regex (deterministic + fast + no JSON parse
    failures), and the LLM validator (plus `GoalValidationResult`
    dataclass + `GOAL_VALIDATION_PROMPT`) is gone.  Cuts one LLM call
    per attempt (worst-case 6 → 3 for step 2).

### Latency knobs and VPN notes

- **`CLAUDE_TIMEOUT=300`** in the env is recommended for VPN users
  — the real DISCOVERY_BLUEPRINT_PROMPT for a C104-class conjecture
  is ~9-10 KB and Sonnet at even `effort=low` takes ~170-280 seconds
  end-to-end over CN VPN.  The default (240s) hits attempt-0 timeout
  and forces a redundant `effort=high` retry.
- **`MODEL_FAST=claude-haiku-4-5-20251001`** speeds up the
  decomposer + goal extractor 3-5x with no observed quality loss —
  the plantri-pool BlueprintValidator catches Haiku's occasional
  false intermediate before it reaches Opus.  Set both env vars
  together for the fastest reliable run.
- **`effort="low"` + `allowed_tools=[]`** are now passed explicitly
  by the decomposer's `messages.create` call and by the step-2 goal
  extractor.  JSON-schema tasks don't need extended thinking or
  grep-side-quests; forcing this in the SDK call cuts wallclock 3-5x
  on identical inputs.
- **Retry loop uses `_ESCALATION_SCHEDULE = [(medium, 40), (high, 60), (high, 60)]`**
  — the caller-supplied `effort` argument overrides the schedule
  when set, so JSON-output callsites pin `low` and only the
  proof_agent per-node work follows the escalation.

### Direct prover CLI (unchanged from v3.4-preview)

```bash
python -m formalize C104              # skip every CE-search stage
python -m formalize C100-110          # range
python -m formalize 104               # 'C' prefix optional
```

- Entry point at [`formalize.py`](formalize.py) (shim) + actual
  implementation at [`agent/prover/formalize.py`](agent/prover/formalize.py).
- Both `python -m run` (full pipeline) and `python -m formalize`
  (prover-only) converge on
  [`agent/prover/runner.py:formalize_conjecture()`](agent/prover/runner.py)
  — single source of truth for "actually invoke the prover".

---

## What's New in v3.3

**Stage 0 — cross-conjecture witness pool replay (new stage, decisive, microseconds–seconds)**

- Every witness-verified CE the pipeline has found is reused as a generic refuter for new conjectures. Before any expensive search, Stage 0 runs two sub-phases against every new conjecture:
  - **(a) Sibling-witness replay** (`_replay_witness_pool`): each counted CE record under `output/conjecture_with_ce/C*/C*.json` must carry a non-empty `witness_graph` edge list; we re-evaluate hypotheses + conclusion on its p-vector, and on hit re-verify the saved graph via the full 5-check `PVectorCheckAgent` (no shortcut — a stale or tampered file cannot bypass verification). Own folder excluded. The current disk count is 204 witness-verified refutations out of 206 CE directories; C21 and C22 have empty/missing `witness_graph` data and are excluded from this replay/count.
  - **(b) plantri-harvested pool replay** (`_replay_plantri_pool`): ~24-25k verified-realizable p-vectors collected by `agent/conjecture_generator/tools/plantri_harvest.py` (f₂ ≤ 28). Filter is arithmetic-only (microseconds per entry); plantri rebuilds the witness graph on hits (~1-10 s each).
- **Post-batch re-sweep** (`_witness_pool_resweep`): the pool grew during the run, so a CE found late may refute a conjecture that failed early. After every worker finishes, Stage 0 (a) re-runs over the still-undecided survivors. High ROI in practice — C23 / C28 / C37 were all caught by exactly this mechanism on 2026-06-28.
- **Stages renumbered**: 0 = witness pool replay, 1 = random walk, 2 = unified CE search (plantri screen + 4 tracks), 3 = Lean prover. Stage 0 + Stage 1 are pure compute (no API), so they front-load every cheap refutation before any LLM/RL/Hopper budget is spent.

**Batch mode — 7 parallel IRIS-sort workers**

- `python -m run` (no args) used to iterate sequentially. It now launches **7 worker threads** that all consume the same conjecture pool, each in a different IRIS sort order — `T`, `R`, `L`, `TR`, `TL`, `RL`, `TRL`. A `threading.Lock`-protected `claimed`/`completed` set guarantees that no two workers touch the same conjecture, and the first worker to find a CE marks it done so the others skip. Conjectures without a CE feed into `ProverAgent` after the re-sweep.
- **IRIS T / R / L scoring** lives in the generator (`agent/conjecture_generator/tools/iris_scoring.py`) and is written into each entry's `iris` field in `conjectures.json` at insertion time. T = touching points (rows where LHS = RHS), R = consistency residual, L = LP closeness. The 7 sort orders express different prioritization tradeoffs; running them in parallel is "free" because Stage 0 and the lattice walk are CPU-bound on different cores, not API-bound.

**Conjecture generator — IRIS-feedback + plantri-pool ground truth**

- **Plantri pool harvester** (`tools/plantri_harvest.py` → `output/conjecture_generator/plantri_pool.json`): replaces the old `local/` data engines. ~24k verified-realizable p-vectors stratified by f₂ ∈ {0, 20, 30, 40} buckets via `_stratify_augmentation`, each bucket gated by `(f_2 >= N)` so the LP rows stay informative; structural extremals kept first. The pool is the *only* gate now (`_consistent_with_verified` on the full augmented row_pvecs); `verify_on_polytopes` / `CLASSICAL_BATTERY` / `is_structurally_sound` / R1-R5 / `pool_saturation_stats` are all gone — their role is subsumed by plantri ground truth + the verified-p-vec sample injected into both prompts.
- **IRIS-feedback prompt** (2026-06-18): LLM propose now sees the existing conjecture block sorted by IRIS-TRL descending, plus survivor signals (unsolved entries with ≥20 CE attempts). Degenerate TRL ≈ 0 is warned, not gated.
- **LLM model refit**: propose = Haiku, effort=low, ≤90s. Review = Sonnet, effort=medium, ≤90s. Bypassed the previous `convex_hull` shortcut entirely.
- **LP overfit drop** (`_drop_lp_overfit`): any coefficient with denominator > 6 is rejected — replaces the old `pool_saturation_stats` / `formula_signature` heuristics. Drop reason logged.
- **Stratified hull by f₂** (`compute_pool_facets`): runs on the FULL pool (not a downsample), buckets by f₂, emits each facet with its own `f_2 >= _N` guard.

**`claude-agent-sdk` migration**

- `agent/claude_sdk.py` moved off raw `claude -p` subprocess invocations to the official `claude-agent-sdk` Python package (`ClaudeSDKClient` + `ClaudeAgentOptions`). The subprocess path was reverted once after a 403 incident; re-migrated 2026-06-27 with the LLM CE preflight wired end-to-end. **Do not revert without testing the preflight again** — bare subprocess hits 403 in batch mode here.
- **Circuit breaker** trips on the first 403 / auth-fail and short-circuits every subsequent `_call` to microseconds, so a dead claude CLI can no longer burn the per-track timeout budget.

**5-Check Validator — Check 3 negated-LHS parser**

- Conclusions of the shape `-(p6) >= -EXPR` (semantically `p6 <= EXPR`, produced when the LLM/Graffiti negates both sides) silently fell through the conclusion-violated regex, so Check 3 returned "not violated" and verified counterexamples were dropped. This had killed CEs for **C55 / C59 / C61 / C64 / C65**. Two extra regex branches added to `pvec_eval.py` cover the negated-LHS form and its symmetric variant.

**RL CE finder — validation bugs squashed + C23 / C24 refuted**

- Two latent bugs in the RL track caused valid CEs to be silently discarded: the witness-drop path didn't propagate the verified graph to disk, and the `stop_event` guard around episode termination raced with the validator. Fixed 2026-06-12; C23 / C24 were both refuted as a direct consequence. C23 was further automated 2026-06-28 via the new Stage 0 witness pool replay.

**`python -m run` infrastructure**

- **Range syntax**: `python -m run C104-122` now expands to `C104 C105 … C122` automatically (works with any `[cC]?\d+-[cC]?\d+` form).
- **Batch-mode status sync** (`_sync_batch`): the orchestrator persists CE files and Lean proofs to disk but never updated `conjectures.json` itself. `run.py` now reconciles every conjecture against on-disk artifacts after `run_batch()` returns, mapping `refuted` (CE file present) and `proven` (Lean proof present) back into `conjectures.json` and moving entries between `unsolved` and `solved` accordingly.
- **Per-token sync** extended from refuted-only to all three terminal states.
- **ID-mapping fix**: `ParsedConjecture.conjecture_id` is the short id (`C105`), but `conjectures.json` keys by `spec.name` (`auto_..._105`). The status syncer now uses the original spec name; calling `set_conjecture_status("C105", ...)` returned `False` silently and was why earlier batch runs left `status='new'` even after CE files landed.

**Lean Inventory — Barnette's alternate p₆ bound (§4.4)**

- New lemma `Barnette_P6Bound` (`polib/Inventory.lean §4.4`) — Barnette 1969 / Jučovič eq. (4), the second main p₆ lower bound for simple 3-polytopes on the sphere (g = 0):

  $$2\,p_6 \;\geq\; 4 + p_3 - p_5 - 2\!\!\sum_{k \geq 7} p_k$$

  under the side condition $\sum_{k \geq 7} p_k \geq 3$. Stated in integer-clear form (`2·p_6 ≥ …`) to avoid rational arithmetic; `hm ≥ 6` matches the rest of Inventory and is implied by `hsum`.
- **Complementary to `Juc_InequalityPart` / `P6InequalityPart`**: Jučovič's bound is tight when low-degree faces (`p_4`, `p_5`) are small but loose when $\sum_{k \geq 7} p_k$ is small and dominated by `k = 7, 8`; Barnette's bound is tight in the latter regime. Together they pin `p_6` from below in every Euler-feasible configuration on the sphere.
- **Accepted sorry, same pattern as §2**: Barnette's proof builds the critical-face adjacency graph $G$ (Theorem 1 proof, p.2 of `p6.tex`) and counts $\delta(F),\ \varphi(v)$ — adjacency data that `SimplyCon3ConnectedMap` does not carry. Marked SORRY (accepted, paper statement) in the same category as `euler_formula` / `handshake` / `Juc_InequalityPart`; the prover's zero-`sorry` policy still applies to every other file.

---

## What's New in v3.2

(no release notes were written at v3.2 — the changes from that commit are folded into the v3.3 section above, in particular the RL validation fixes and the C23 / C24 refutation push.)

---

## What's New in v3.1

**Stage 2 reorganized around plantri — `PlantriCEFinder`**

- The exhaustive screen and the constructor track now live in one dedicated agent, **`agent/plantri_ce_finder/`** (replaces `agent/constructor_ce_finder/`; the screen moved out of the orchestrator). Rationale: plantri is the main force — within its reach its verdicts are final in *both* directions; the constructor is the one-sided fallback for candidates beyond exhaustive reach. One log tag covers both roles — `[plantri ce finding] plantri:` (screen) and `[plantri ce finding] constructor:` (double check). The "Phase A / Phase B" naming is gone.
- **The constructor is now a single double check, not an endless retry loop**: every screen survivor gets exactly one construction attempt, with the seed salted by the attempt count recorded in `output/realizability_cache.json` — so the *next program run* automatically draws fresh trajectories; the retry lives across runs, not inside one. A completed sweep settles every in-bounds candidate, but only a *found CE* stops the other tracks — LLM/RL/Hopper can propose p-vectors outside the enumeration bounds, so "No CE" is concluded only after all four tracks exhaust their own budgets. Progress prints at 1/3 and 2/3 of the survivor list plus a final `double check over` line.

**LLM track actually produces candidates now — extended-thinking root cause found**

- Every CE round used to time out (360 s and 180 s alike), so the circuit breaker killed the track before it ever emitted a candidate. Root cause: the nested `claude -p` call ran with **extended thinking** — the CLI's adaptive default on 4.6+ models, amplified to `xhigh` when the pipeline is launched from a Claude Code session (the child inherits `CLAUDE_EFFORT`) — and the math-heavy round prompt made the model think for 4+ minutes before writing any JSON (measured: >240 s, zero output). Fix: CE rounds pass `--effort low` explicitly (`LLM_CE_EFFORT`) and `CLAUDE_EFFORT` is stripped from the subprocess environment. Measured after: **a full round answers in ~8 s with 5 parsed candidates**. Low effort is deliberate — candidates are verified locally (tiers 1–3 instant, tier 4 is the real gate), so breadth beats depth.
- A 60 s **preflight** call (`LLM_CE_PREFLIGHT_TIMEOUT`) runs before round 1: if the claude CLI is dead (usage-limit exhaustion, auth, network), the track disables itself in ≤1 minute instead of burning three full round timeouts on the circuit breaker. Per-round timeout dropped 360 s → 180 s (`LLM_CE_TIMEOUT`). RL / Hopper / constructor are unaffected either way.

**Orphan processes are structurally impossible now**

- Root cause found for leaked workers (one set burning 4 cores for 40 minutes, an older set idle for 8+ hours): `KeyboardInterrupt` only reaches the main thread, so `finally`-based pool teardown in daemon threads never ran, and orphaned spawn workers block forever on the pool call queue (sibling workers hold the pipe open — EOF never arrives). Every child the pipeline spawns — pool workers, RL/Hopper processes, plantri enumerations, claude CLI calls, lake builds — now registers Linux **`PR_SET_PDEATHSIG`** via `agent/procutil.py`: the kernel kills it the moment its parent dies, covering Ctrl-C, crashes and even SIGKILL. Verified by simulation: parent SIGKILL leaks workers without it, kills them with it.

---

## What's New in v3.0

**The loop is closed — generation joined the pipeline**

- **`ConjectureGenerator`** (`agent/conjecture_generator/`): Graffiti3 (`txgraffiti`) discovers candidate inequalities over the polytope discovery table; an optional LLM co-proposer adds candidates and an LLM reviewer filters; duplicates against the known dataset are rejected. Survivors are registered with `status='new'` in `conjectures/registry.json`.
- **Evolution loop** (`agent/orchestrator/evolution_loop.py`, `python -m run project`): each generation runs generate → CE search → prover for every new conjecture. Outcomes are written to `conjectures/conjectures.json` (`refuted` / `proven` / `prover_failed`, with CE / proof detail); the generator derives its prompt signals (proved / refuted / prover-stuck / survivor) fresh from that store plus on-disk artifacts each generation — there is no side-channel hint file to go stale. Signals feed **only** the generator prompts — never CE finding, never a verification gate. Stops on the first Lean-proved conjecture, `--max-generations`, or two consecutive empty generations.

**Stage 2/3 merged into one unified CE search stage**

- **Phase A — exhaustive screen** (decisive, no API): analytic constructions + plantri exhaustion; verdicts final and cached. Returns the undecided *survivors*.
- **Phase B — four parallel tracks**: LLM + RL + Hopper + the new **constructor track**, which runs rotating multi-pass stochastic realization over the survivors for as long as the other tracks are still searching (attempt+pass-salted seeds, escalating timeouts). The old `retry_round` / re-entry machinery is deleted — the constructor track *is* the retry, running concurrently instead of afterwards.
- Stages renumbered: **1 = random walk, 2 = unified CE search, 3 = Lean prover**.

**LLM CE rounds ~2× faster, breaker fixed**

- The round prompt now demands *silent* verification and a ≤3-sentence reasoning field (the step-by-step arithmetic it used to print is re-checked locally in microseconds anyway). Measured on a live round-1 prompt: **152 s / 10.6 K output tokens → 78 s / 5.7 K tokens** — comfortably inside the 360 s timeout, so the 3-strikes circuit breaker no longer kills the LLM track on latency spikes.

**plantri `-m5` dispatch**

- Min-degree-5 p-vectors are decided by the `plantri_mf` binary (`-m5` generation tree): ~3 orders of magnitude faster, raising the exhaustive screen's reach to `PLANTRI_F2_MAX_M5=36` for pentagon/hexagon-dominated candidates, while min-deg-3/4 candidates stay on `plantri_ad` (`PLANTRI_F2_MAX=26`).

<details>
<summary><b>Previous release notes (v2.3 – v2.6 plus)</b></summary>

> **Historical note on stage numbers:** these release notes use the old four-stage numbering — Stage 2 = boundary enumeration, Stage 3 = LLM+RL+Hopper, Stage 4 = Lean prover. The pipeline documentation sections further down use the current numbering (1 = walk, 2 = unified CE search, 3 = prover).

## What's New in v2.6 plus

**Headline result: conjecture C5 (`auto_20260310_142638_5`) is REFUTED.** Stage 2 realized the counterexample `{3:2, 5:16, 6:5, 16:1}` (f₂ = 24, p₆ = 5 < RHS = 6) via the plantri exhaustive tier, and it passed all five checks — including the new fully-independent final validation. CE artifacts for C2/C3/C4 were migrated to the new folder layout with back-filled witness graphs.

**Throughput — Stage 2 went from ~50 min to minutes**

- **plantri single-phase early exit**: splits now generate ASCII witnesses directly (line-buffered via `stdbuf -oL`) instead of count-then-regenerate — the first output line from *any* split is already a witness, so realizable candidates are decided in seconds even when only 1–2 realizations exist in the whole space. The non-realizable verdict is unchanged in strength: it is only accepted when every split exits cleanly *and* prints its enumeration summary.
- **Candidate-level parallelism**: Stage 2 realizes candidates in a spawn-based `ProcessPoolExecutor` (`CE_ENUM_REALIZE_PARALLEL`, default 4), each worker's internal plantri split count capped so pool × splits ≈ cores (`PLANTRI_JOBS`).
- **Construction-failure cache**: when the full strategy stack fails at budget T, a `construction_failed` record (with `timeout_used`) is written to `output/realizability_cache.json` — re-runs at budget ≤ T skip instantly. This is *not* a verdict: a larger budget still re-runs everything, and a later exhaustive verdict overwrites the record. Cache writes are now cross-process safe (flock on a `.json.lock` sidecar + atomic replace).
- **LLM round batching**: each LLM round's arithmetically-surviving candidates are realizability-checked **concurrently** (`LLM_CE_CHECK_PARALLEL`, default 5) in a reused spawn pool instead of serially — per-round check time drops from ~150 s to ~one constructor timeout.

**CPU sanity (all measured, seeded A/B)**

- RL and Hopper torch pools cut to **1 thread** (`RL_TORCH_THREADS` / `HOPPER_TORCH_THREADS`). The old 2/3-of-cores allocation made RL **25% slower while burning 9.8 cores** (OpenMP spin overhead on tiny PPO tensors) — this is why the RL track looked starved until Hopper finished. Concurrent RL + Hopper interference is now ~3%.
- BLAS (MKL) pinned to 1 thread in finder processes: explicitly granting MKL n threads *activates* its dormant pool on small matrices and burns ~5 cores at zero wall-time gain.
- **Instant teardown on CE**: pool workers are process-group leaders, and an early CE kills each in-flight worker *together with its plantri children* (`worker_setpgrp` / `kill_pool_pgroups`). Previously a found CE looked like a hang of up to one full candidate timeout at exit; now the run exits in ~2 s with zero orphaned plantri processes.

**Rigor — the validator is now 5 checks**

- **Check 5 — Final ce validation check** (fully independent, zero shared code with Checks 1–4): re-evaluates hypotheses + conclusion with a from-scratch AST-whitelist evaluator working directly off the raw statement (it does not trust `pvec_eval` *or* the upstream hypothesis splitter — a `pvec_eval` hypothesis bug minted the retracted C3 f₂=8 CE), and re-validates the witness graph with networkx instead of graphcalc: 3-regular + planar + 3-connected (Steinitz ⇒ simple 3-polytope) + the p-vector re-derived by tracing every face of the planar embedding must match the candidate exactly.
- **CE artifacts are folders with visualization**: `output/conjecture_with_ce/C{id}/` contains `C{id}.json` (for counted witness-verified refutations, this persists the full non-empty verified `witness_graph` edge list, so the CE is independently re-checkable) plus an automatically rendered `C{id}_witness.png` planar drawing, where every interior region is an actual face of the polytope. Current count: 206 CE directories, of which 204 have complete witness graphs and pass the five-check witness-verified standard; C21 and C22 are retained as records but excluded from the witness-verified refutation count. Re-render anytime: `python agent/orchestrator/tools/draw_ce_witness.py output/conjecture_with_ce/C5/C5.json --labels`.

**Quieter logs**: Stage 2 prints `[10/40] … [40/40]` milestones instead of two lines per candidate; Hopper reports every 1000 steps instead of every 100.

---

## What's New in v2.6

**Headline result: conjecture C2 (`auto_20260310_142638_2`) is REFUTED.** The counterexample `{3:1, 5:16, 6:4, 13:1}` (f2 = 22, p6 = 4 < RHS = 5) has exactly **2** realizations as a simple 3-polytope in the entire space — found and validated autonomously by the new pipeline in 31 seconds (`output/conjecture_with_ce/C2/C2.json`, full witness edge list included). Notably, all five triangle-free candidates at f2 = 22 are exhaustively **non**-realizable; the unique counterexample family member needs exactly one triangle.

- **plantri exhaustive tier** (decisive, both directions): `PolytopeConstructor` now calls [plantri 5.8](https://users.cecs.anu.edu.au/~bdm/plantri/) (Brinkmann & McKay, `allowed_deg` plugin, bundled in `agent/orchestrator/tools/plantri/`) as Strategy 3. plantri enumerates *all* sphere triangulations with the target degree multiset, isomorph-free, in parallel `res/mod` splits — so a candidate either yields an explicit witness graph (dual of the triangulation, face-traced from the embedding) or is **proven non-realizable by exhaustion**. Definitive rejections surface in the 4-Check output as `[Tier 4 plantri] exhaustively NON-realizable`.
- **In-memory realizability cache**: exhaustive verdicts (never timeouts) are cached within a run, so retries skip already-decided candidates instantly.
- **Explicit witness validation**: the 4-Check Validator accepts a `witness_graph` — re-verified with graphcalc (never trusted), exact p-vector match required.
- **Hopper witness fix** (critical): Hopper used to discard its own dual-hull geometry and route validation through the chop constructor, self-rejecting every exotic CE it found. It now extracts the primal witness graph from the dual hull (`hull.neighbors` facet adjacency) and submits it for verification.
- **Dual-space perturbation search** (Strategy 3b): hill-climbing with annealing + cap seeding over point configurations on the unit sphere; reaches topologies chop search cannot.
- **A\* chop search gated on p3 ≥ 1** (provable): every chop's last triangle persists in the final graph, so triangle-free targets are unreachable by chopping — the budget goes to the dual-space strategies instead.
- **Standalone batch decider**: `python agent/orchestrator/tools/plantri/decide_ce_plantri.py --name <conjecture>` exhaustively decides all enumerated candidates of a conjecture (cheapest-first, resumable, stops on the first realizable hit).
- RL-track caveat documented: its chop-only action space provably cannot reach p3 = 0 targets.

---

## What's New in v2.5

**Counterexample side**

- **Tier-4 realizability constructor revived**: a stale `graphcalc.graphs.polytopes` import (that path no longer exists in graphcalc ≥ 1.3) silently failed and permanently disabled the Tier-4 witness constructor — every CE candidate outside the known families was auto-rejected with `graphcalc_unavailable`. Fixed to top-level imports. **All "no CE found" verdicts produced before this fix are unreliable and should be re-run.**
- **Stage 2 — Boundary Enumeration** (new, no API, seconds): exhaustively enumerates *every* DS-valid p-vector within bounds that satisfies the hypotheses and violates the conclusion (the random walk only samples this space), then tries to realize the most constructible candidates via the 4-Check Validator.

**Prover side**

- **Inventory-entailment pre-check**: before Stage 4, the orchestrator searches for *countermodels* — p-vectors satisfying the per-map arithmetic content of every Inventory axiom while violating the conjecture's conclusion. If any exist, no honest Lean proof can be derived from the current Inventory; Stage 4 is skipped with an explicit verdict naming sample countermodels (override: `FORCE_PROVER=true`).
- **Soundness guard**: proofs that construct a `SimplyCon3ConnectedMap` instance (`.mk`, structure literal, `where`-definition, `{ maps with … }` copy-update) are hard-rejected before compilation on every code path and fail the quality check. A fabricated instance lets a proof derive `False` from the sorried axioms (e.g. v = 0, e = 0 makes `euler_formula` yield `0 = 2`), making everything "provable".
- **Axiom soundness fix**: `kgon_occupation_bound` is restated on `total_occ` and is now **proved** from `occupation_bound` (the old formulation quantified over arbitrary `Finset ℕ` and was refutable inside Lean); `quad_occ_reduction` and the phantom `quad_adj_constraint` are removed — their faithful statements need face-adjacency data the structure does not carry.
- **Inline node retry** replaces the v2.4 orchestrator-level 3-attempt restart: failed nodes are retried inside the prover run (parse/goal/blueprint are not redone), with a per-node budget (`MAX_NODE_RETRIES`, default 4), dependency gating (nodes whose deps are still failing are skipped), and stall/exhaustion exits.
- **Claude CLI retries escalate timeouts** (150 s → 210 s → 270 s; previously they *shrank* to 90 s/60 s, guaranteeing repeat failures), and infrastructure failures (CLI timeouts, unresolved deps, aborts) are no longer recorded into cross-run failure memory.
- **Dependency-signature injection**: generation and fix prompts include the exact Polib signatures of proved dependencies so the LLM cannot hallucinate argument counts; helper-lemma prompts pin the parent theorem's genus.

---

## What's New in v2.4

- **Quality Checker rewrite**: The old quality checker used token-matching between JSON formula tokens (e.g. `is_simple`, `f_2`) and Lean code tokens — this was always false because JSON tokens never appear literally in Lean. The checker is now fully rewritten to use Claude semantic verification. For intermediate helper nodes, only a sorry audit is performed (signatures need not match the root formula). For the root theorem node, Claude answers four questions: `CONCLUSION_MATCH`, `HYPOTHESES_COVERED`, `NO_EXTRA_CONSTRAINTS`, and `OVERALL_FAITHFUL`. Scoring: faithfulness 0.70 + sorry audit 0.20 + proof structure 0.10. A node passes when `score >= 0.85` and `faithfulness_ok`.
- **Auto-retry**: The orchestrator retries failed nodes up to 3 times. Nodes that are already proved are already in Polib and are loaded (skipped); only failed nodes are re-attempted.
- **Cross-run failure memory**: On each failure the last error message plus up to 1 200 characters of the failed code are stored in `store.json` (up to 4 records per node). On retry, `_generate_lean` injects a "Previous failed attempts — do NOT repeat these approaches" block into the Claude prompt.
- **Improved terminal display**: Step numbering `[1/9]`–`[8/9]`, a `[6/9] Checking formalization quality...` section, a `[fix]` log line before each fix attempt, and a `fix #N` counter that increments across all rounds.

---

## What's New in v2.3

- **Hopper CE Finder** (new track in Stage 3): dual-space hop algorithm adapted from Swirszcz et al. (2025), achieves ~96% valid-hop rate by working in the dual simplicial polytope representation. Runs online: a small neural network is trained from scratch during the search and improves hop quality over time.
- **True parallelism**: the RL and Hopper tracks now run as separate **OS processes** (`multiprocessing.Process`) instead of threads. This eliminates GIL contention and PyTorch thread-pool competition — all three CE tracks now run on independent CPU cores simultaneously.
- **Inventory.lean**: a foundational Lean 4 lemma library (`polib/Inventory.lean`) containing formalized constituents of Euler's formula, the Jučovič theorem, and the general-genus p₆ inequality. Replaces the previous monolithic `Polib.lean`.

</details>

---

## Quick Start

> One-time setup first: see [Installation](#installation) (Python deps + Lean 4/Mathlib + `claude` CLI).

```bash
# ── A. Autonomous mode (v3.0) ─ generate → CE search → prove → learn ─────────
python -m run project

# with budgets / knobs (all optional):
python -m run project --max-generations 5 --rl-episodes 300 --llm-rounds 10 \
                      --g3-mode fast --llm-propose-n 12 --generator-limit 15
python -m run project --no-llm-gen          # pure Graffiti3, no LLM co-proposer

# ── B. Attack a single existing conjecture ───────────────────────────────────
python -m run 43          # short numeric ID (matches name ending in _43)
python -m run c43         # same

# ── C. Batch: all conjectures in conjectures/conjectures.json ────────────────
python -m run             # 7 parallel IRIS-sort workers

# ── D. Direct prover — skip every CE-search stage, go straight to Lean ───────
python -m formalize C104          # single
python -m formalize C1 C2 C3      # batch (sequential)
python -m formalize C100-110      # range (inclusive)
python -m formalize 104           # 'C' prefix optional

# Keep a log (stdout is already line-buffered):
python -m run project 2>&1 | tee logs/evolution_$(date +%m%d_%H%M).log
```

The short form `43` or `c43` resolves to any conjecture whose name ends with `_43` in `conjectures/conjectures.json`. Mode A stops at the first Lean-proved conjecture, after `--max-generations` (default 10), or after two consecutive generations that produce nothing new.

Modes A/B/C run the full pipeline: Stage 0 (witness pool replay) → Stage 1 (random walk) → Stage 2 (plantri + RL + Hopper + LLM CE search) → Stage 3 (prover, only if no CE found). **Mode D skips Stages 0-2** and invokes the prover directly — useful when you already know the conjecture is provable (e.g. retrying a known-good C104 after a prompt change) and don't want to spend 5-30 min on CE search. Both `python -m run` and `python -m formalize` end up calling the same `agent/prover/runner.py:formalize_conjecture()`, so prover behaviour is identical between the two entry points.

---

## Pipeline Overview

In autonomous mode (`python -m run project`) the whole diagram below is wrapped
in the **evolution loop**: a generation starts at the generator, every new
conjecture flows through Stages 1–3, and the outcomes flow back into
`conjectures.json`, from which the next generation derives its prompt signals.
In single/batch mode the run starts directly at the Formula Parser with
existing conjectures.

```
┌─────────────────────────────────────────────────────────────┐
│  Conjecture Generator  (evolution mode only)                │
│  Graffiti3 (txgraffiti): full table + classical strata      │
│    + dynamic cells (uncovered hypothesis combos, rotated)   │
│  + Mutation engine (repair refuted / sharpen proved bounds) │
│  + Support miner (tight C104-class lower-hull bounds)       │
│  + LLM co-proposer + LLM reviewer  (signal-aware)           │
│  full-pool gate (~25k p-vecs) + tight-repair rule +         │
│  vacuity / overfit / semantic-dup guards → status='new'     │
└────────────────────────┬────────────────────────────────────┘
                         │ conjectures/conjectures.json (+ registry entry)
                         ▼
conjectures/conjectures.json
         │
         ▼
   [ Formula Parser ]
         │  ParsedConjecture (id, hypotheses, conclusion)
         ▼
┌─────────────────────────────────────────────────────────────┐
│  Stage 1 — P-Vector Random Walk  (no API, <1 min)           │
│  DS-preserving lattice walk, 60 restarts × 200k steps       │
└────────────────────────┬────────────────────────────────────┘
                         │ CE candidate?
                         │ YES ──► [ 5-Check Validator ] ──► PASS ──► output
                         │ NO
                         ▼
┌─────────────────────────────────────────────────────────────┐
│  Stage 2 — Unified CE Search  (led by PlantriCEFinder)      │
│                                                             │
│  Exhaustive Screen  (plantri — no API, minutes, decisive)   │
│  Enumerate ALL DS-valid violating p-vectors within bounds   │
│  → analytic constructions → plantri exhaustion (verdicts    │
│  final + cached); undecided candidates = "survivors"        │
│                         │ CE realized? YES ──► output       │
│                         │ NO                                │
│                         ▼                                   │
│  Four Parallel Tracks                                       │
│  ┌────────────┐ ┌──────────────┐ ┌───────────┐ ┌─────────┐ │
│  │ LLM Track  │ │ RL Track     │ │  Hopper   │ │ Constr. │ │
│  │ main thread│ │ own process  │ │own process│ │ thread+ │ │
│  │ Claude     │ │ PPO+FiLM-GNN │ │ dual-space│ │ proc.   │ │
│  │ 15–30 rnds │ │ 600 episodes │ │ hop + NN  │ │ pool    │ │
│  └─────┬──────┘ └──────┬───────┘ └─────┬─────┘ └────┬────┘ │
│        └───────────────┴─────┬─────────┴────────────┘      │
│                              ▼                              │
│                    [ 5-Check Validator ]                    │
│                    first PASS → stop all tracks             │
│  (constructor = ONE double-check build attempt per each     │
│   screen survivor; sweep complete → whole CE search ends)   │
└────────────────────────┬────────────────────────────────────┘
                         │ CE found?
                         │ YES ──► output/conjecture_with_ce/C<id>/
                         │         (C<id>.json + C<id>_witness.png)
                         │ NO
                         ▼
┌─────────────────────────────────────────────────────────────┐
│  Stage 3 — Lean 4 Prover                                    │
│  Blueprint decomposition + compile-fix loop                 │
│  Lemma search over Mathlib + polib/Inventory.lean           │
└────────────────────────┬────────────────────────────────────┘
                         ▼
              output/conjecture_without_ce/{id}/{id}.lean
              output/conjecture_without_ce/{id}/{id}.md    (informal proof)

   every outcome → conjectures.json (reconcile from artifacts,
                   ALL entry points: run.py / formalize / evolution loop)
        refuted        → REFUTED signal + repair-mutation source ┐
        prover_failed  → PROVER-STUCK signal (mimic, don't avoid)├─► next
        proved         → PROVED signal + sharpen-mutation source ┘   generation
```

---

## The Evolution Loop (autonomous mode)

`python -m run project` runs `agent/orchestrator/evolution_loop.py`. One generation:

1. **Generate** — `ConjectureGenerator` reconciles statuses from on-disk artifacts, derives the four prompt signals (proved / refuted / prover-stuck / survivor), builds the discovery table, then gathers candidates from every source: Graffiti3 full-table + classical strata + this round's dynamic cells, the mutation engine (repairs of refuted bounds, sharpenings of proved ones), the support-function miner (tight C104-class lower bounds swept from the full pool), and optionally `--llm-propose-n` LLM proposals with an LLM review pass. Every candidate faces the same hard gates — full-pool consistency (~25k verified p-vectors), tight-repair rule for refuted shapes, LP-overfit and vacuity guards, dedup (exact-formula AND attack-surface: same hypotheses + same arithmetic CE-candidate set as an alive conjecture ⇒ semantic duplicate, dropped) — before registration with `status='new'` in `conjectures.json` (+ a `registry.json` entry for survivor counters).
2. **Evaluate** — every `status='new'` conjecture runs the full pipeline (Stage 0 → 1 → 2; survivors → Stage 3):
   - CE found → `status='refuted'` (+ CE p-vector + violation detail)
   - proved in Lean → `status='proven'` (+ proof path) → **loop stops**
   - prover failed → `status='prover_failed'` (+ outcome)
3. **Next generation** — signals are re-derived from `conjectures.json`, so this round's outcomes (and any result produced meanwhile through `run.py` or `formalize`) feed the next one automatically.

**Stop conditions**: first proven conjecture, `--max-generations` exhausted (default 10), or two consecutive generations producing zero new conjectures.

**Rules enforced** (soundness is non-negotiable):
- Only `status='new'` entries are ever evaluated — conjectures with results never re-enter the loop.
- `proven` comes **only** from prover success. Surviving CE search is *not* success — it records `prover_failed`, a distinct signal class (probably-true-but-unprovable) the generator treats as structure to mimic, not territory to avoid.
- Since v3.5 plus, `reconcile_from_artifacts` enforces this in both directions: a `.lean` artifact qualifies as a proof only with the root theorem declared and no failed nodes in its header, and a `proved` entry whose artifact is missing or partial is demoted (`prover_failed` / `new`) automatically.
- Signals feed the generator only. CE finding, the 5-Check Validator, and the prover run exactly as in single/batch mode.

**Flags** (`python -m run project [flags]`):

| Flag | Default | Meaning |
|---|---|---|
| `--max-generations` | 10 | generation budget |
| `--rl-episodes` | 600 | RL track budget per conjecture |
| `--llm-rounds` | 15 | LLM track budget per conjecture |
| `--g3-mode` | `fast` | Graffiti3 search depth (`fast` / `standard` / `deep`) |
| `--llm-propose-n` | 12 | extra formulas requested from the LLM co-proposer |
| `--generator-limit` | 0 | cap accepted conjectures per generation (0 = no cap) |
| `--no-llm-gen` | off | disable LLM propose/review (pure Graffiti3) |

**State files**: `conjectures/conjectures.json` (3-bucket dataset — the single source of truth for statuses) and `conjectures/registry.json` (CE-attempt counters, auto-created). Generator signals are derived, never stored.

---

## Input Format

All conjectures live in `conjectures/conjectures.json`:

```json
{
  "unsolved": [
    {
      "name": "auto_20260310_142638_43",
      "formula": "if ((is_simple) and (f_2>=_30)), then p6 >= (-5*sum_pk_after_p6 + 10)"
    },
    {
      "name": "auto_20260310_142638_13",
      "formula": "if (((is_simple) and (f_2>=_18)) and (sum_pk_k>=7 >= 1)), then p6 >= (-4*sum_pk_after_p6 + 8)"
    }
  ],
  "solved": [
    {
      "name": "auto_20260310_142638_2",
      "formula": "if ((is_simple) and (f_2>=_22)), then p6 >= (-5*sum_pk_after_p6 + 10)"
    }
  ]
}
```

### Formula syntax

Every formula follows the pattern:

```
if (<hypothesis> [and <hypothesis> ...]), then p6 >= <expr>
```

or with an upper bound:

```
if (<hypothesis> [and <hypothesis> ...]), then p6 <= <expr>
```

**Supported hypothesis tokens:**

| Token | Meaning |
|---|---|
| `is_simple` | polytope is simple (every vertex has degree 3) |
| `f_2>=_N` | total number of 2-faces $f_2 = \sum p_k \geq N$ |
| `sum_pk_k>=7 >= N` | $\sum_{k \geq 7} p_k \geq N$ |

**Variables in the RHS expression:**

| Variable | Meaning |
|---|---|
| `p3`, `p4`, `p5`, `p6` | number of triangular, quad, pentagonal, hexagonal faces |
| `sum_pk_after_p6` | $\sum_{k \geq 7} p_k$ |

Coefficients may be integer or decimal (e.g. `-3.5*sum_pk_after_p6 + 7`).

### Name resolution

When you run `python -m run 43`, the system strips any leading `c`/`C` and matches names ending in `_43`. If more than one name matches, it prints the ambiguous options and exits.

---

## Stage 1 — P-Vector Random Walk

A fast **Dehn-Sommerville lattice walk** that searches for CE candidates without any API calls or graph construction.

Every valid simple 3-polytope p-vector must satisfy Euler's formula combined with 3-regularity:

$$\sum_{k \geq 3}(6 - k)\,p_k = 12 \qquad \text{(Dehn-Sommerville constraint)}$$

The walk stays on this lattice by applying **DS-preserving moves**: for any pair $(k_1 < 6,\; k_2 > 6)$:

$$p_{k_1} \mathrel{+}= (k_2 - 6), \qquad p_{k_2} \mathrel{+}= (6 - k_1)$$

This move changes two face counts while keeping the DS sum at exactly 12. The walk starts from a perturbed dodecahedron, runs for up to 200,000 steps per restart across 60 restarts, and greedily maximises the **violation gap** (how strongly the conclusion is broken). Any candidate with a positive gap is sent to the 5-Check Validator.

Terminal output:

```
[Stage 1] Starting random walk to find counterexamples...
[Stage 1] Random walk exhausted — no realizable CE. Proceeding to Stage 2 (unified CE search)...
```

---

## Stage 2 — Unified CE Search

Stage 2 is led by **`PlantriCEFinder`** (`agent/plantri_ce_finder/`). plantri
— exhaustive enumeration of all polytope graphs with a given face count — is
the project's realizability oracle: within its reach its verdicts are final
in *both* directions. The finder runs its two roles under one log tag: a
decisive exhaustive screen (`[plantri ce finding] plantri:`), then four
parallel stochastic tracks on whatever the screen left undecided, one of
which is the finder's own constructor double check
(`[plantri ce finding] constructor:`).

### Exhaustive Screen (plantri — no API, decisive)

The random walk *samples* the DS lattice; the screen *exhausts* it within
bounds. It enumerates every p-vector that

- is non-negative with DS sum = 12,
- satisfies all conjecture hypotheses, and
- violates the conclusion,

over all large-face multisets (sizes 7..`CE_ENUM_KMAX`, at most
`CE_ENUM_NLARGE_MAX` faces ≥ 7) and total face counts up to `CE_ENUM_F2_MAX`.
Each candidate then goes through analytic constructions (known families /
prisms, instant) and the plantri exhaustive screen (batched multi-target
sweeps for min-deg-5 candidates, budgeted per-candidate decisions for the
rest). Verdicts are **final and cached**: `nonrealizable` is a proof by
exhaustion. Candidates the screen cannot decide within budget are the
**survivors** handed to the constructor double check.

```
[plantri ce finding] plantri: 284 candidate p-vector(s) satisfy the arithmetic constraints. Exhaustive enumeration can decide 250 of them directly; 34 have too many faces to enumerate exhaustively.
[plantri ce finding] plantri: CE realized (plantri_batch_f2=24): {3: 2, 5: 16, 6: 5, 16: 1}
[Check p-vector] ✓ Realizability: [Tier 4 Constructor] plantri_exhaustive: witness graph with 44 vertices, ...
[Check p-vector] ✓ Final ce validation check: independent re-eval (statement): hypotheses TRUE, conclusion FALSE ...
```

A realized candidate is a **verified counterexample** (`found_by:
"boundary_enumeration"`). This is exactly how C2 and C5 were refuted.
If *no* arithmetic candidate exists at all, the conjecture is arithmetically
tight in this region — strong evidence for Stage 3. If the screen decides
*every* candidate nonrealizable, no realizable CE exists in this region at
all and the parallel stage still runs only the sampler tracks (which can
leave the region's bounds).

### Parallel Tracks — LLM + RL + Hopper + Constructor Double Check

Four tracks run in **true parallel** — each track is isolated from the others: the RL and Hopper tracks run as separate OS processes (`multiprocessing.Process`) so they have independent CPU cores and no GIL or PyTorch thread-pool contention; the constructor double check is a thread whose work runs in a spawn process pool. All four share a single `multiprocessing.Event` stop signal: the first track to produce a validated CE sets the event and causes the others to exit promptly. That is the *only* early-stop — a double check that completes with no CE settles the in-bounds candidates but lets the samplers (which can leave the bounds) run out their own budgets before "No CE" is concluded.

Each finder process is pinned to **1 torch thread and 1 BLAS thread**
(`RL_TORCH_THREADS` / `HOPPER_TORCH_THREADS`, default 1). This is a measured
optimum, not a compromise: on tiny PPO/MLP tensors extra threads are pure
spin overhead (seeded A/B: torch=10 ran 25% slower than torch=1 while
burning 9.8 cores), and explicitly granting MKL multiple threads activates
its dormant pool for ~5 cores of busy-waiting at zero wall-time gain. The
freed cores go to plantri enumeration and the LLM track's parallel checks.

```
[Stage 2] Launching parallel CE searches — RL: 600 episodes  |  LLM: 15 rounds  |  Hopper: on  |  plantri: 34 undecided candidate(s)
```

### LLM Track (main thread)

- A 60 s **preflight** call (`LLM_CE_PREFLIGHT_TIMEOUT`) runs before round 1: if the claude CLI is dead (usage limit, auth, network) the track disables itself in ≤1 minute instead of burning three round timeouts; per-round timeout is 180 s (`LLM_CE_TIMEOUT`)
- Rounds run at `--effort low` (`LLM_CE_EFFORT`): extended thinking on the math-heavy round prompt made rounds take >240 s (every round timed out); low effort answers in ~8 s, and candidate quality is enforced locally by the validator anyway
- Up to **15–30 rounds**, each asking Claude for 3–5 candidate p-vectors
- Each round's prompt includes: the conjecture statement, all previously tried candidates (up to 50), and the last 5 failures with reasons
- Candidates are hard-deduplicated across rounds via frozenset keys; the LLM cannot repeat a vector
- Instant arithmetic filtering first, then the surviving violators go to the 5-Check Validator **as a parallel batch** (`LLM_CE_CHECK_PARALLEL`, default 5, spawn pool reused across rounds) — a round's realizability cost is ~one constructor timeout instead of five in sequence; a worker failure falls back to a serial re-check

Terminal output per round:

```
[LLM ce finding] Round 1/15: 5 candidate(s), 0 valid, tier1-3 passed, tier 4 didn't — next round
[LLM ce finding] Round 2/15: 5 candidate(s), 0 valid, tier1-3 passed, tier 4 didn't — next round
```

If LLM finds a CE:

```
[LLM ce finding] Round 7/15: CE found — {5: 12, 7: 2} — p6=0 < 3.14
```

### RL Track (separate process — PPO + FiLM-GNN)

- A **PPO policy** with a FiLM-conditioned graph neural network learns to build cubic planar graphs via repeated **node-chop** operations (replace a degree-3 vertex with a triangle)
- The reward combines: polytope validity bonus, a shaped term that rewards moves pushing towards violation, a gap-improvement term, and `+100` on CE
- At each episode reset, if the formula has a threshold hypothesis (e.g. `sum_pk_k>=7 >= 1`), the environment pre-expands the graph to satisfy it before the policy takes over
- Trained for up to **600 episodes**; stops early if any track (including itself) finds a validated CE

Terminal output:

```
[rl ce finding] Episode 1/600
[rl ce finding] Episode 100 | R: 22.62 | Len: 12.3 | Stop0:  5.00% | CE: 0.00% | Gap:  3.532
[rl ce finding] Episode 200 | R: 18.41 | Len: 15.7 | Stop0:  3.50% | CE: 0.00% | Gap:  4.801
...
```

| Column | Meaning |
|---|---|
| `R` | mean episode reward (last 100 episodes) |
| `Len` | mean episode length in steps |
| `Stop0` | fraction of episodes where the policy stopped at step 1 |
| `CE` | fraction of episodes that produced a CE candidate |
| `Gap` | best violation gap seen (higher is more violated) |

If RL finds a CE:

```
[rl ce finding] Episode 137 ce found! p_vector=[38, 7, 6, ...]
[validation check ce from rl] 1 CE candidate(s) found, running 5 checks
[validation check ce from rl] √ Dehn-Sommerville: DS sum = 12 ✓
[validation check ce from rl] √ Hypotheses: all satisfied
[validation check ce from rl] √ Conclusion: p6=5 < RHS=8.3 — violated by 3.3
[validation check ce from rl] √ Realizability: [Tier 4 Constructor] ... witness graph ... PROVEN by explicit construction
[validation check ce from rl] √ Final ce validation check: independent re-eval: hypotheses TRUE, conclusion FALSE | witness re-validated by networkx
[validation check ce from rl] The ce candidate is valid, saved CE JSON → output/conjecture_with_ce/C43/C43.json
```

If RL exhausts all episodes:

```
[rl ce finding] Episode 600 | R: -1.33 | Len:  2.3 | Stop0:30.17% | CE:0.00% | Gap: -8.000 no ce found
```

### Hopper Track (separate process — dual-space hop + neural network)

Adapts the **Hopper algorithm** (Swirszcz et al., 2025) for simple 3-polytopes. The key insight is to work in **dual simplicial polytope space**:

- Every simple 3-polytope P has a dual simplicial polytope P* (all faces triangles). The vertex valences of P* equal the p-vector of P.
- The Dehn-Sommerville constraint is automatically satisfied because it is equivalent to Euler's formula on P*, which always holds — so no DS-check is needed after each hop.
- A **hop** moves one dual vertex to a new position determined by a random hyperplane. ~96% of hops produce a valid simplicial hull (vs. 0% in primal simple-polytope space).

When Hopper finds a violating p-vector, it extracts the **primal witness graph** directly from its dual hull (facet adjacency via `hull.neighbors`) and submits it to the 5-Check Validator's `witness_graph` path — the graph is re-verified with graphcalc, so exotic candidates no longer die at the chop constructor.

The neural network (`HopperBrain`) scores each candidate hyperplane as one of three classes:
- `0` — good hop (predicts improvement in violation gap)
- `1` — geometrically infeasible (LP test fails)
- `2` — feasible but expected no improvement

The network is trained **online from scratch** during the search using a replay buffer of recent hops. A pool of up to 50 dual polytopes is maintained; the best polytopes (by violation slack) are kept, allowing the search to explore from many starting points simultaneously. The objective alternates every 200 steps between two modes:

- **slack mode**: minimise the violation gap (how close p₆ is to violating the bound)
- **f2 mode**: maximise the total face count (explore larger polytopes)

Terminal output every 100 steps:

```
[Hopper ce finding] Init: 6 seed(s) in pool | device: cpu
[Hopper ce finding] Step 100/5000  | Pool: 6 | Slack:+0.000 | Hops: 108 | Train:  1 | Obj:slack
[Hopper ce finding] Step 200/5000  | Pool: 6 | Slack:+0.000 | Hops: 199 | Train:  3 | Obj:f2
[Hopper ce finding] Step 300/5000  | Pool: 7 | Slack:+0.000 | Hops: 307 | Train:  5 | Obj:f2
[Hopper ce finding] Step 400/5000  | Pool: 7 | Slack:+0.000 | Hops: 425 | Train:  7 | Obj:slack
[Hopper ce finding] Step 800/5000  | Pool:27 | Slack:+0.000 | Hops: 903 | Train: 15 | Obj:slack
[Hopper ce finding] Step 1100/5000 | Pool:47 | Slack:+0.000 | Hops:1311 | Train: 21 | Obj:f2
```

| Column | Meaning |
|---|---|
| `Pool` | number of dual polytopes currently in the pool |
| `Slack` | best violation slack seen (positive = CE found) |
| `Hops` | total hop attempts so far |
| `Train` | number of neural-network training steps completed |
| `Obj` | current objective mode (`slack` or `f2`) |

If Hopper finds a CE:

```
[Hopper ce finding] Step 843/5000: CE found — {5: 12, 7: 2} — p6=0 < RHS=1.0
[validation check ce from hopper] CE candidate from Hopper, running 5 checks
[validation check ce from hopper] √ Dehn-Sommerville: DS sum = 12 ✓
[validation check ce from hopper] √ Hypotheses: all satisfied
[validation check ce from hopper] √ Conclusion: p6=0 < RHS=1.0 — violated
[validation check ce from hopper] √ Realizability: [Tier 2] prism family {4:7, 7:2}
[validation check ce from hopper] √ Final ce validation check: independent re-eval: hypotheses TRUE, conclusion FALSE | witness re-validated by networkx
[validation check ce from hopper] CE valid, saved CE JSON → output/conjecture_with_ce/C13/C13.json
```

If Hopper exhausts all steps without a CE:

```
[Hopper ce finding] Stopped by stop_event
```

(or simply no output if another track already found a CE and set the stop event)

### Constructor Double Check (thread + spawn process pool)

The second role of `PlantriCEFinder`: the screen's undecided survivors —
candidates beyond plantri's exhaustive reach — each get **exactly one**
stochastic construction attempt (`CE_ENUM_REALIZE_TIMEOUT` seconds,
`CE_ENUM_REALIZE_PARALLEL` workers). Construction is one-sided: a successful
build is a verified CE with an explicit witness graph; a failed build proves
nothing. Every attempt is recorded in `output/realizability_cache.json`, and
seeds are salted with the cached attempt count — so the *next program run*
draws provably fresh trajectories; the retry lives across runs, not inside
one.

Termination: it aborts instantly when any track finds a CE (stop signal).
When its own sweep completes with no CE, the in-bounds candidates are
settled, but the sampler tracks keep running — they can propose p-vectors
outside the enumeration bounds, so "No CE" requires all four tracks to
exhaust their budgets. Per-worker plantri splits are capped so that the
constructor pool and the LLM track's tier-4 check pool together fit the
machine (`cores / (CE_ENUM_REALIZE_PARALLEL + LLM_CE_CHECK_PARALLEL)`).

```
[plantri ce finding] constructor: trying to build a polytope for each of 34 undecided candidate(s) (90s per attempt)...
[plantri ce finding] constructor: 11/34 candidate(s) attempted, none realized so far (162s elapsed)
[plantri ce finding] constructor: 22/34 candidate(s) attempted, none realized so far (331s elapsed)
[plantri ce finding] double check over — all 34 candidate(s) attempted, no CE found (502s, results cached).
```

or, on success:

```
[plantri ce finding] constructor: CE found (17/34): {3: 2, 5: 16, 6: 5, 16: 1}
```

A realized candidate is a verified counterexample (`found_by:
"constructor_finder"`).

---

## The 5-Check Validator

Every CE candidate — from the random walk, the exhaustive screen, the LLM, the RL agent, Hopper, or the constructor double check — must pass all five checks. Failure at any check immediately rejects the candidate.

### Check 1 — Dehn-Sommerville + Euler

| Condition | Formula |
|---|---|
| Non-negativity | $p_k \geq 0$ for all $k \geq 3$ |
| Dehn-Sommerville | $\sum_k(6-k)\,p_k = 12$ |
| Minimum faces | $f_2 = \sum p_k \geq 4$ |
| Vertex / edge count | $V = 2(f_2 - 2)$, $E = 3(f_2 - 2)$, Euler: $V - E + f_2 = 2$ |

### Check 2 — Hypotheses Satisfied

Evaluates each hypothesis (`is_simple`, `f_2>=_N`, `sum_pk_k>=7 >= N`) against the candidate. All must hold — if any hypothesis fails, the candidate is not in the conjecture's domain and is rejected.

### Check 3 — Conclusion Violated

Substitutes the p-vector into the RHS expression and confirms the inequality is genuinely violated (e.g. $p_6 < \text{RHS}$ for a `>=` conjecture). Computes and reports the **violation margin**.

### Check 4 — Realizability (hard gate)

Passing Checks 1–3 proves the p-vector is arithmetically correct and violates the conjecture, but DS = 12 is a *necessary* condition for realizability, not a *sufficient* one. Check 4 requires building an **explicit witness graph**.

**Tier 1 — Exact known polytopes** (O(1) lookup):

| p-vector | Polytope |
|---|---|
| `{3:4}` | Tetrahedron |
| `{4:6}` | Cube |
| `{5:12}` | Dodecahedron |
| `{3:2, 4:3}` | Triangular prism |
| `{4:5, 5:2}` | Pentagonal prism |

**Tier 2 — Proven infinite families:**

- Prism family `{4:n, n:2}` for any $n \geq 7$ → accepted
- Fullerene family `{5:12, 6:k}` for $k \geq 2$ → accepted
- `{5:12, 6:1}` → **rejected** (known non-realizable, Grünbaum 1967)

**Tier 4 — PolytopeConstructor (mandatory for all other cases):**

> Requires `graphcalc` ≥ 1.3 (top-level `simple_polytope_graph` / `p_vector` API). If the import fails, every Tier-4 candidate is rejected with `graphcalc_unavailable` — treat that message as a broken environment, not a mathematical verdict.

Physically builds a 3-connected 3-regular planar witness graph using a sequence of strategies within a shared timeout:

1. Direct construction for known shapes and prisms
2. **plantri exhaustive decision** (for $f_2 \leq$ `PLANTRI_F2_MAX`, default 26): enumerates *all* dual triangulations with the target degree multiset in parallel splits — returns a witness graph, or **proves non-realizability by exhaustion** (verdict cached in memory within a run)
3. Dual-space perturbation search (annealed point-configuration search on the sphere; handles triangle-free and single-large-face targets)
4. A\* chop-search from dodecahedron / tetrahedron / $k_{max}$-gon prism — only attempted when the target has $p_3 \geq 1$ (chop results always contain a triangle, so triangle-free targets are provably unreachable)

After construction, `graphcalc` verifies the graph's p-vector matches the target exactly and confirms it is a valid simple polytope graph. **If all strategies fail, the CE is rejected with no fallback.** There is no "probably realizable" path — only an explicit verified graph is accepted. A plantri exhaustion verdict is stronger than a rejection: it *proves* the p-vector is not realizable.

CE finders that hold their own geometric witness (Hopper's dual hull) submit it via the validator's `witness_graph` parameter — the graph is re-verified with graphcalc, never trusted.

### Check 5 — Final ce validation check (independent re-verification)

Checks 2/3 share the `pvec_eval` parser, and Check 4's graph verification goes through graphcalc — each a single point of failure (a `pvec_eval` hypothesis-evaluation bug once minted the retracted C3 f₂=8 "counterexample"). Check 5 re-derives everything through code paths that share **nothing** with Checks 1–4:

**(a) Formula re-evaluation** — a from-scratch substitution + AST-whitelist evaluator works directly on the *raw conjecture statement* (it performs its own `if`/`then` split, so it does not trust the upstream hypothesis splitter either; falls back to the parsed hypothesis/conclusion strings with paren balancing). All hypotheses must evaluate `True` and the conclusion must evaluate `False`. Anything the independent evaluator cannot parse rejects the CE — there is no lenient path.

**(b) Witness re-validation with networkx** (graphcalc not used) — the witness graph from Check 4 must be:

| Property | Why |
|---|---|
| simple, 3-regular, connected | simple polytope graphs are cubic |
| planar | Steinitz necessary condition |
| 3-connected | planar + 3-connected ⇔ polytope graph (Steinitz) |
| embedding p-vector match | every face of the planar embedding is traced (well-defined by Whitney uniqueness for 3-connected planar graphs); the resulting face-size histogram must equal the candidate p-vector exactly, and V − E + F = 2 |

When the realizability tier accepted via a family citation without an explicit graph, the formula re-evaluation still runs and the graph part is reported as skipped. Verified witnesses are exported to the CE JSON (`counterexample.witness_graph`), so every accepted CE remains independently re-checkable forever.

Check output format (all five checks printed for each candidate):

```
[Check p-vector] ✓ Dehn-Sommerville + Euler: DS=12 ✓  f2=24  V=44  E=66  (Euler: 44-66+24=2)
[Check p-vector] ✓ Hypotheses: ✓ (is_simple)  |  ✓ (f_2>=_24) [f2=24]
[Check p-vector] ✓ Conclusion violated: p6=5.0 < RHS=6.0000 (violation)  |  violation margin=-1.0000
[Check p-vector] ✓ Realizability: [Tier 4 Constructor] plantri_exhaustive: witness graph with 44 vertices, 66 edges,
                  p-vector verified — realizability PROVEN by explicit construction
[Check p-vector] ✓ Final ce validation check: independent re-eval (statement): hypotheses TRUE, conclusion FALSE
                  [5 >= (-6*1 + 12)] | witness re-validated by networkx: 3-regular, planar, 3-connected,
                  all 24 faces traced — p-vector matches (V=44, E=66, F=24)
```

A rejection at any check stops the candidate:

```
[validation check ce from hopper] √ Dehn-Sommerville: DS sum = 12 ✓
[validation check ce from hopper] √ Hypotheses: all satisfied
[validation check ce from hopper] √ Conclusion: p6=0 < RHS=1.0 — violated
[validation check ce from hopper] ✗ Realizability: [Tier 4 Constructor] all construction strategies exhausted — CE rejected
```

---

## Output

### Counterexample found → `output/conjecture_with_ce/C{id}/`

Each refuted conjecture gets its own **artifact folder**:

```
output/conjecture_with_ce/
└── C5/
    ├── C5.json           # full CE record incl. verified witness edge list
    └── C5_witness.png    # planar drawing, rendered automatically
```

```json
{
  "conjecture_id": "auto_20260310_142638_5",
  "conjecture_latex": "if ((is_simple) and (f_2>=_24)), then p6 >= (-6*sum_pk_after_p6 + 12)",
  "hypotheses": ["(is_simple)", "(f_2>=_24)"],
  "conclusion": "p6 >= (-6*sum_pk_after_p6 + 12)",
  "status": "failed",
  "counterexample": {
    "p_vector": [2, 0, 16, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    "p3": 2, "p5": 16, "p6": 5, "p16": 1,
    "f2": 24,
    "num_vertices": 44,
    "num_edges": 66,
    "witness_graph": {
      "format": "edge_list",
      "num_vertices": 44,
      "edges": [[0, 1], [0, 5], [0, 12], "... 66 edges total"]
    }
  },
  "found_by": "boundary_enumeration",
  "found_at_round": 11,
  "violation_detail": "p6=5.0 < RHS=6.0000 (violation)"
}
```

`found_by` is one of `"pvector_walk"`, `"boundary_enumeration"`, `"llm_finder"`, `"rl_agent"`, `"hopper_agent"`, or `"plantri_exhaustive_decision"`. The `witness_graph` edge list is the **verified witness** — the CE is independently re-checkable forever without re-running the pipeline.

The PNG is a **planar drawing**: every interior region of the picture is an actual face of the polytope (the outer region is the remaining face). Re-render anytime:

```bash
python agent/orchestrator/tools/draw_ce_witness.py output/conjecture_with_ce/C5/C5.json            # → C5_witness.png
python agent/orchestrator/tools/draw_ce_witness.py output/conjecture_with_ce/C5/C5.json --labels   # with vertex labels
```

The folder name uses the **short ID** (`C5`) derived from the trailing number of the full conjecture name.

### No counterexample → `output/conjecture_without_ce/{id}/{id}.lean` (+ `{id}.md`)

If the CE search ends with nothing — the samplers exhaust their budgets and the constructor double check completes with no CE — the conjecture goes to **ProverAgent** (Stage 3) unconditionally. See the [Stage 3](#stage-3--lean-4-prover) section below for the full 9-step pipeline, quality checker, inline retry loop, cross-run failure memory, and the natural-language proof written alongside the Lean file on clean success.

> **Note on `sorry` placeholders:** Sub-goals that require planar graph geometry lemmas not yet present in Mathlib (Steinitz's theorem, Eberhard's theorem, face-counting for 3-polytopes) are left as `sorry`. The surrounding proof structure still type-checks and compiles.

---

## Stage 3 — Lean 4 Prover

When no counterexample is found, **ProverAgent** produces a Lean 4 formalization through a 9-step pipeline. The prover runs unconditionally on every survivor — the old Inventory-entailment precheck (which used to gate Stage 3 on the existence of arithmetic countermodels) was retired on 2026-06-15. Honest Lean proofs can still be derived from Mathlib first principles even when Inventory alone doesn't entail the conclusion, so gating on Inventory entailment was unnecessarily lossy.

### Soundness Guard

Generated proofs must work only with the `maps` parameter given in the theorem signature. Any construction of a `SimplyCon3ConnectedMap` instance — `.mk`, a structure literal `{ m := …, p_i := … }`, an ascribed anonymous constructor `⟨…⟩ : SimplyCon3ConnectedMap`, a `where`-definition, or a `{ maps with … }` copy-update — is rejected **before compilation** (error class `X`, fed back to the fix loop) and independently fails the quality check. Reason: the geometric axioms are sorried statements that hold only for maps of real polytopes; applied to fabricated data they yield `False` (e.g. v = 0, e = 0 ⟹ `euler_formula` gives `0 = 2`), from which any goal is "provable".

### The 9-Step Pipeline

| Step | Name | What it does |
|---|---|---|
| `[1/9]` | Parse conjecture | Reads the JSON formula and resolves the conjecture name |
| `[2/9]` | Extract & lock goal | Derives the root Lean theorem signature; caches it in `store.json` (keyed by formula hash) |
| `[3/9]` | Decompose blueprint | Calls Claude to decompose the root goal into a DAG of helper lemmas; computes topological order |
| `[4/9]` | Formalize nodes | For each node in topological order: search hints → generate Lean → compile → fix loop (up to `MAX_ROUNDS_PER_NODE` rounds) |
| `[5/9]` | Retry failed nodes | Inline retry loop — re-attempts only the failed nodes, feeding cross-run failure memory and newly-proved dep signatures back into the prompts |
| `[6/9]` | Deep quality check | Per-node deep check: QR sanity, signature drift vs locked sig, axiom sweep, instance sweep. A textual signature mismatch is arbitrated by a defeq compile check (`example : <locked ∀-type> := NAME`) so notation noise can't kill a valid proof while real drift still fails the type checker. Failed nodes are downgraded AND purged from `Polib.lean` |
| `[7/9]` | Validate Polib | `PolibValidator` end-to-end integrity check of `Polib.lean`; broken sections are removed and their nodes downgraded to failed |
| `[8/9]` | Collect & save | Classifies node statuses and writes the complete `.lean` file to `output/conjecture_without_ce/{id}/{id}.lean` |
| `[9/9]` | Write NL proof | On clean success only: one LLM call that reads the locked goal + blueprint + verified `.lean` and writes an informal Markdown proof to `{id}.md` alongside the Lean file. Silent no-op on any earlier failure. |

### Quality Checker

The quality checker runs after all nodes are compiled and applies different criteria depending on the node type.

**All nodes** — soundness guard first: a proof that constructs a `SimplyCon3ConnectedMap` instance hard-fails with score 0 regardless of anything else (see [Soundness Guard](#soundness-guard)).

**Intermediate helper nodes** — only a sorry audit is performed. The node passes if it introduces no new `sorry` statements (sorried axioms in `Inventory.lean` are allowed). The node's signature does not need to match the root formula.

**Root theorem node** — Claude answers four semantic questions about the Lean code versus the original JSON formula:

| Question | Meaning |
|---|---|
| `CONCLUSION_MATCH` | The Lean conclusion is equivalent to the formula's conclusion |
| `HYPOTHESES_COVERED` | All JSON hypotheses appear as Lean hypotheses |
| `NO_EXTRA_CONSTRAINTS` | The Lean theorem adds no hypotheses absent from the JSON formula |
| `OVERALL_FAITHFUL` | The theorem as a whole faithfully represents the conjecture |

**Scoring:**

```
score = faithfulness * 0.70 + sorry_audit * 0.20 + proof_structure * 0.10
passed = score >= 0.85 and faithfulness_ok
```

### Inline Retry Loop

Failed nodes are retried **inside** the prover run — parse/goal/blueprint are not redone (this replaces the v2.4 orchestrator-level 3-attempt restart). Proved nodes are saved to Polib and skipped; per sweep, failed nodes are retried in topological order with:

- **Dependency gating** — a node whose direct dependencies are still failing is skipped (`[skip] waiting on failed dep(s)`) instead of burning a Claude call + lake build on a near-certain failure. It unblocks within the same sweep the moment its deps succeed.
- **Per-node budget** — each node is retried at most `MAX_NODE_RETRIES` times (default 4), logged as `retry N/4`.
- **Stall / exhaustion exit** — the loop stops after 2 consecutive sweeps without progress, when every remaining node is blocked or out of budget, or after 20 sweeps, whichever comes first.

Each retry regenerates with updated dependency signatures and cross-run failure memory.

### Cross-Run Failure Memory

When a node fails to compile after all fix rounds, the last error message plus up to 600 characters of the failed Lean code are stored in `store.json` (up to 3 records per node — older attempts are stale baggage). **Infrastructure failures (claude CLI timeouts, unresolved deps, aborts) are not recorded** — they carry no information about the proof approach. On the next attempt, `_generate_lean` reads these records and prepends a block to the Claude prompt:

```
Previous failed attempts — do NOT repeat these approaches:
  Attempt 1: <error> | <failed code excerpt>
  Attempt 2: ...
```

This prevents Claude from regenerating the same broken tactic patterns.

### Fix Attempt Tracking

Within each formalization round, fix attempts are numbered with a `fix #N` counter that increments across all rounds (not just within the current round). Each fix attempt is logged with `[fix]` before it starts:

```
[fix]  C2_LowerDegreeFacesBound round 0, fix #1: trying targeted_fix + targeted_fix_strict in parallel
[ok]  C2_LowerDegreeFacesBound compiled via parallel fix (targeted_fix_parallel, round 0, fix #1)
```

### Terminal Output Example

```
[Stage 3] ProverAgent starting for C2 …
[1/9] Parsing conjecture...
      theorem: C2 (0 steps)
[2/9] Extracting & locking goal...
      [cache hit] goal loaded from store (key=f33f8...)
      signature: theorem C2 (maps : SimplyCon3ConnectedMap 0) ...
[3/9] Decomposing blueprint...
      nodes: ['C2_DomainConstraintsFromMap', 'C2_LowerDegreeFacesBound', 'C2_MainGoalConversion', 'C2']
      topo order: ['C2_DomainConstraintsFromMap', ...]
[4/9] Formalizing nodes...
  [hints] C2_DomainConstraintsFromMap: 4 (combined, verified)
  [gen] C2_DomainConstraintsFromMap — 4 hints (validated)
  [ok]  C2_DomainConstraintsFromMap compiled (round 0)
  [saved] C2_DomainConstraintsFromMap → polib (proved)
  [hints] C2_LowerDegreeFacesBound: 7 (combined, verified)
  [gen] C2_LowerDegreeFacesBound — 7 hints (validated)
  [err] C2_LowerDegreeFacesBound round 0: unexpected token 'have'
  [fix]  C2_LowerDegreeFacesBound round 0, fix #1: trying targeted_fix + targeted_fix_strict in parallel
  [ok]  C2_LowerDegreeFacesBound compiled via parallel fix (targeted_fix_parallel, round 0, fix #1)
  [saved] C2_LowerDegreeFacesBound → polib (proved)
  [err] C2_MainGoalConversion round 2: linarith failed
  [dep-fail] C2 — unresolved deps: ['C2_MainGoalConversion']

[retrying]
  [C2_MainGoalConversion] previous failure: linarith failed
  [C2_MainGoalConversion] retry 1/4: regenerate with updated dep signatures + cross-run failure memory
  [C2_MainGoalConversion] retry successfully → proved
  [C2] previous failure: unresolved deps: ['C2_MainGoalConversion']
  [C2] retry 1/4: regenerate with updated dep signatures + cross-run failure memory
  [C2] retry successfully → proved
  [retrying] all nodes resolved after 1 iteration(s)
[6/9] Deep quality check...
  [C2_DomainConstraintsFromMap] Deep check: PASS
  [C2] Deep check: PASS
  [6/9] Deep check summary: 2/2 nodes passed
[7/9] Validating Polib (post-flight safety net)...
  [polib-validate] Polib builds cleanly — no repairs needed
[8/9] Formalization saved → /home/.../output/conjecture_without_ce/c2/c2.lean
[9/9] Writing proof in natural language...
  Done!
  Markdown saved → /home/.../output/conjecture_without_ce/c2/c2.md

[Stage 3] Done. Result: success
```

---

## Lean Proof Library — `polib/Inventory.lean`

`polib/Inventory.lean` is the foundational lemma library used by the Lean 4 prover. It formalizes three source papers:

| Section | Source | Status |
|---|---|---|
| §1 — Data structure | — | `SimplyCon3ConnectedMap` structure (no sorry) |
| §2 — Foundational lemmas | `Euler_inductive.tex`, `jucovic_theorem.tex`, `p6.tex` | Sorried axioms (Mathlib lacks surface-embedded graph API) |
| §3 — Jučovič theorem (sphere) | `jucovic_theorem.tex` | Partial: identity + arithmetic proved; inequality sorry |
| §4 — p₆ inequality (genus g) + Barnette bound | `p6.tex` | Partial: edge-count equation proved; Jučovič inequality + Barnette alternate bound (§4.4) sorry |
| §5 — Euler's formula (inductive) | `Euler_inductive.tex` | Base case, tree case, inductive step all proved |

### §1 — Data Structure

```lean
structure SimplyCon3ConnectedMap (g : ℤ) where
  m         : ℕ       -- max face size
  p_i       : ℕ → ℕ  -- p_i k = number of k-gonal faces
  v         : ℕ       -- vertex count
  e         : ℕ       -- edge count
  total_occ : ℕ → ℤ  -- triangle-edge occupation per face size
```

### §2 — Foundational Lemmas (sorried)

These are the **only** permitted `sorry` in the file. They axiomatize geometric facts that Mathlib's `SimpleGraph` API cannot yet express:

| Lemma | Statement |
|---|---|
| `euler_formula` | $V - E + F = 2 - 2g$ |
| `handshake` | $2E = \sum_k k \cdot p_k$ |
| `regularity` | $3V = 2E$ (3-regularity) |
| `p_range` | $p_k = 0$ for $k > m$ |
| `occupation_conservation` | $\sum_{k \geq 4} \text{occ}(k) = 3p_3$ |
| `occupation_bound` | $0 \leq \text{occ}(k) \leq \lfloor k/2 \rfloor \cdot p_k$ |
| `equality_family` | existence of an injective infinite equality family with $m \ge n+6$ |

Derived in §2 (proved, **not** an axiom):

| Lemma | Statement |
|---|---|
| `kgon_occupation_bound` | $\text{occ}(k) \leq \lfloor k/2 \rfloor \cdot p_k$ — proved from `occupation_bound` |

> **Soundness fix (2026-06)**: the former `kgon_occupation_bound` and `quad_occ_reduction` quantified over arbitrary `Finset ℕ` instead of the map's occupation data and were refutable inside Lean (e.g. occ = {0,1,2}, k = 4 gives 3 ≤ 2), making the axiom base inconsistent. `kgon_occupation_bound` is restated on `total_occ` and proved; `quad_occ_reduction` ("an $r$-gon adjacent to a quad occupies $\leq \lfloor r/2 \rfloor - 1$") is **removed** — its faithful statement needs face-adjacency data the structure does not carry (the same Mathlib gap that blocks `Juc_InequalityPart`).

> **Equality-family guard**: `equality_family` now states an injective infinite family whose witnesses satisfy `m ≥ n + 6`; it no longer prescribes `m = n + c` for every `n`. The earlier `n + 3` form admitted small exceptional cases; combined with `p_range`, the `n = 0`, `g = 0` witness forced the equality equation into `0 = 12`.

### §3 — Jučovič Theorem (sphere, g = 0)

**Proved without sorry:**

- `Juc_KGonMaxOccupation` — $\text{occ}(k) \leq \lfloor k/2 \rfloor \cdot p_k$ for $k \geq 4$ (alias of `kgon_occupation_bound`)
- `Juc_HexMaxOccupation` — hexagonal face occupies at most 3 triangle-edges
- `Juc_NonHexEdgeBound` — total non-hex occupation $\leq \sum_{k \neq 6} \lfloor k/2 \rfloor \cdot p_k$
- `Juc_EulerFormula` — $3p_3 = 12 - 2p_4 - p_5 + \sum_{k \geq 7}(k-6)p_k$
- `Juc_EqualityConstruction` — infinite family achieving equality

**Remaining sorry:**

- `Juc_InequalityPart` — $3p_6 \geq 12 - 2p_4 - 3p_5 + \sum_{k \geq 7}(\lfloor(k+1)/2\rfloor - 6)p_k$
  - *Blocker: quad-occupation cancellation argument requires surface-graph adjacency theory not in Mathlib*
- `JucovicTheorem` — full theorem (depends on `Juc_InequalityPart`)

### §4 — p₆ Inequality for General Genus g

**Proved without sorry:**

- `P6EdgeCountEquation` — $3p_3 = 12(1-g) - 2p_4 - p_5 + \sum_{k \geq 7}(k-6)p_k$

**Remaining sorry:**

- `P6InequalityPart` — $3p_6 \geq 12(1-g) - 2p_4 - 3p_5 + \sum_{k \geq 7}(\lfloor(k+1)/2\rfloor - 6)p_k$ (same blocker)
- `P6GenusG` — full genus-g theorem

#### §4.4 — Barnette's alternate p₆ bound (sphere, g = 0)

- `Barnette_P6Bound` — $2p_6 \geq 4 + p_3 - p_5 - 2\sum_{k \geq 7} p_k$ under the side condition $\sum_{k \geq 7} p_k \geq 3$ (Barnette 1969 / Jučovič eq. (4), `p6.tex` Theorem 1).
  - Stated in integer-clear form to avoid rational arithmetic; `hm ≥ 6` and `hsum` together imply `m ≥ 7`.
  - *Blocker*: critical-face adjacency graph counts ($\delta(F),\ \varphi(v)$) — same adjacency-data gap as §2; SORRY accepted as a paper statement.
  - *Why both*: Jučovič is tight when $p_4, p_5$ are small; Barnette is tight when $\sum_{k \geq 7} p_k$ is small and dominated by $k = 7, 8$. The pair pins $p_6$ from below across the full Euler-feasible region on the sphere.

### §5 — Euler's Formula (inductive constituents)

All three proved without sorry:

```lean
lemma eulerBaseCase    : (1 : ℤ) - 0 + 1 = 2
lemma eulerTreeCase    (v : ℕ) : (v : ℤ) - ((v : ℤ) - 1) + 1 = 2
lemma eulerInductiveStep (v e f : ℤ) (h : v - e + f = 2) : v - (e + 1) + (f + 1) = 2
```

---

## Project Structure

```
Polytope_Conjecture_Prover/
├── run.py                              # CLI entry point (python -m run [project|<id>])
├── conjectures/
│   ├── conjectures.json                # All conjectures (unsolved / failed / proved) — single truth source
│   └── registry.json                   # CE-attempt counters for the survivor signal (auto-created)
├── agent/
│   ├── config.py                       # Config (env vars, paths, model names)
│   ├── claude_sdk.py                   # Thin wrapper around the claude CLI binary
│   ├── procutil.py                     # PR_SET_PDEATHSIG helper — every child dies with its parent
│   ├── conjectures.py                  # JSON loader + formula canonicalizer + registry I/O
│   ├── conjecture_generator/
│   │   ├── agent.py                    # Graffiti3 + LLM co-proposer/reviewer (signal-aware)
│   │   ├── data/                       # Discovery table assembly
│   │   └── tools/                      # dataset / signals / mutations / support_miner / render
│   ├── orchestrator/
│   │   ├── orchestrator.py             # Top-level pipeline (stages 0–3)
│   │   ├── evolution_loop.py           # Autonomous mode: generate → CE → prove → statuses
│   │   └── tools/
│   │       ├── check_pvector.py        # 5-Check Validator (+ spawn-pool worker entry)
│   │       ├── polytope_constructor.py # Witness graph builder (Tier 4, plantri early-exit, failure cache)
│   │       ├── ce_enumerator.py        # Stage 2 enumeration
│   │       ├── conjecture_parser.py    # Formula → ParsedConjecture
│   │       ├── draw_ce_witness.py      # CE witness renderer (planar drawing; auto-called on CE)
│   │       └── plantri/
│   │           ├── plantri_ad          # plantri 5.8 + allowed_deg plugin (min-deg 3/4)
│   │           ├── plantri_mf          # plantri -m5 build (min-deg-5 fast path, ~1000×)
│   │           ├── count_multiset.c    # multiset-counting plugin source
│   │           ├── decide_ce_plantri.py # standalone batch realizability decider
│   │           └── plantri-guide.txt   # upstream documentation (Apache 2.0)
│   ├── plantri_ce_finder/
│   │   └── agent.py                    # plantri-led CE search: exhaustive screen + constructor double check
│   ├── rl_ce_finder/
│   │   └── agent.py                    # PPO + FiLM-GNN CE search
│   ├── llm_ce_finder/
│   │   ├── agent.py                    # Claude-based CE search
│   │   └── prompts/                    # CE round prompts (silent-verification format)
│   ├── hopper_ce_finder/
│   │   └── agent.py                    # Dual-space hop + online NN CE search
│   └── prover/
│       ├── agent.py                    # Lean 4 formalization agent
│       └── tools/
│           ├── lean_compiler.py        # lake build wrapper
│           ├── search.py               # Mathlib + Inventory lemma search
│           ├── blueprint.py            # Proof decomposition
│           ├── quality_checker.py      # Semantic quality checker (Claude-verified)
│           ├── polib_manager.py        # Polib I/O + SessionState (cross-run failure memory)
│           └── latex_parser.py         # LaTeX theorem parsing
├── output/
│   ├── realizability_cache.json        # permanent verdicts + construction-failure records
│   ├── conjecture_with_ce/             # C{id}/C{id}.json + C{id}_witness.png per refuted conjecture
│   └── conjecture_without_ce/         # {id}/{id}.lean + {id}.md — Lean proof + informal NL proof
├── polib/
│   ├── Inventory.lean                  # Foundational lemma library
│   └── lakefile.lean                   # Lake build config for polib
└── requirements.txt
```

---

## Installation

### 1. Python dependencies

```bash
pip install -r requirements.txt
```

Key packages: `torch`, `graphcalc`, `networkx`, `scikit-learn`, `numpy`, `scipy`, `matplotlib`, `python-dotenv`, `tqdm`.

> **PyTorch CPU-only (recommended unless you have a CUDA GPU):**
> ```bash
> pip install torch --index-url https://download.pytorch.org/whl/cpu
> ```

### 2. Lean 4 + Mathlib

```bash
# Install elan (Lean toolchain manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Fetch Mathlib cache and build polib (first time: ~30–60 min)
cd polib
lake exe cache get
lake build
```

### 3. Claude CLI

The LLM track and prover agent call Claude through the `claude` CLI binary.

```bash
# Requires Node.js >= 18
npm install -g @anthropic-ai/claude-code

# Authenticate (one-time)
claude
```

### 4. Environment variables (optional)

Create a `.env` file at the project root to override defaults:

```dotenv
# Claude models
MODEL_MAIN=claude-sonnet-4-6          # prover, LLM CE finder, validation
MODEL_FAST=claude-haiku-4-5-20251001  # goal extraction, search

# Lean / Lake
LAKE_BINARY=lake                      # path to lake executable
POLIB_PATH=polib                      # path to Lean proof library

# Prover tuning
MAX_ROUNDS_PER_NODE=3                 # compile-fix iterations per proof node
MAX_NODE_RETRIES=4                    # per-node budget in the inline retry loop
COMPILE_TIMEOUT_SECONDS=180           # lake build timeout (seconds)
MAX_PARALLEL_NODES=6                  # parallel proof threads
CLAUDE_TIMEOUT=150                    # claude CLI timeout (s); retries escalate +60 s each

# Stage 2 enumeration bounds
CE_ENUM_F2_MAX=36                     # max total face count enumerated
CE_ENUM_KMAX=20                       # max face size enumerated
CE_ENUM_NLARGE_MAX=2                  # max number of faces with k >= 7
CE_ENUM_MAX_RESULTS=400               # cap on candidates kept
CE_ENUM_REALIZE_MAX=40                # 0 disables the constructor double check (otherwise every survivor gets one attempt)
CE_ENUM_REALIZE_TIMEOUT=90            # seconds per construction attempt
CE_ENUM_REALIZE_PARALLEL=4            # double-check pool size (candidates realized concurrently)

# plantri exhaustive tier
PLANTRI_AD=agent/orchestrator/tools/plantri/plantri_ad   # path to the plantri_ad binary
PLANTRI_F2_MAX=26                     # max f2 decided exhaustively, min-deg-3/4 (runtime grows fast)
PLANTRI_F2_MAX_M5=36                  # max f2 decided exhaustively, min-deg-5 (plantri_mf fast path)
PLANTRI_JOBS=0                        # res/mod splits per decision (0 = auto: cores / pool size)

# Stage 2 parallel-track thread + parallelism budget
RL_TORCH_THREADS=1                    # RL torch threads (1 is the measured optimum)
HOPPER_TORCH_THREADS=1                # Hopper torch threads (1 is the measured optimum)
LLM_CE_CHECK_PARALLEL=5               # LLM round tier-4 checks run concurrently (1 = serial)
LLM_CE_TIMEOUT=180                    # per-round claude CLI timeout (s); a round at low effort is ~8 s
LLM_CE_PREFLIGHT_TIMEOUT=60           # CLI health check before round 1 (dead CLI → LLM track disabled)
LLM_CE_EFFORT=low                     # extended-thinking effort for CE rounds (low/medium/high)
```

---

## Usage

```bash
# Autonomous evolution loop (generate → CE search → prove → feed back outcomes)
python -m run project
python -m run project --max-generations 5 --rl-episodes 300 --llm-rounds 10
python -m run project --no-llm-gen --g3-mode deep --generator-limit 12
python -m agent.orchestrator.evolution_loop --max-generations 3   # equivalent direct form

# Single conjecture — short numeric ID
python -m run 43          # matches name ending in _43
python -m run c43         # same (c/C prefix ignored)

# Single conjecture — full name
python -m run auto_20260310_142638_43

# Batch — all unsolved conjectures in conjectures/conjectures.json
python -m run

# Via orchestrator directly (more control)
python -m agent.orchestrator --name auto_20260310_142638_43
python -m agent.orchestrator --name auto_20260310_142638_43 --rl-episodes 1200 --llm-rounds 50
python -m agent.orchestrator --name auto_20260310_142638_43 --skip-ce   # prover only
python -m agent.orchestrator --batch --json conjectures/conjectures.json

# Generator alone (discover + register, no evaluation)
python -m agent.conjecture_generator

# Exhaustively decide ALL enumerated CE candidates of one conjecture (standalone,
# resumable, stops on the first realizable hit). This is how C2 was refuted.
python agent/orchestrator/tools/plantri/decide_ce_plantri.py --name auto_20260310_142638_43 --f2-max 24
```

---

## Adding New Conjectures

**Autonomous (preferred in v3.0)**: just run `python -m run project` — the generator discovers, dedups, and registers new conjectures itself, and the loop evaluates them.

**Manual**: edit `conjectures/conjectures.json` and add an entry to the `"unsolved"` array:

```json
{
  "name": "auto_20260310_142638_99",
  "formula": "if ((is_simple) and (f_2>=_20)), then p6 >= (-2*sum_pk_after_p6 + 4)"
}
```

Names must end with a unique integer suffix (used to derive the short ID `C99`). Run with `python -m run 99`.
