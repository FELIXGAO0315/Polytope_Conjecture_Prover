# Polytope Conjecture Prover — v2.6

An automated pipeline for deciding conjectures about simple convex 3-polytopes.
Given a conjecture in JSON formula format, the system either finds a **verified counterexample** (backed by an explicit witness polytope) or produces a **Lean 4 formalization** of the proof.

---

## What's New in v2.6

**Headline result: conjecture C2 (`auto_20260310_142638_2`) is REFUTED.** The counterexample `{3:1, 5:16, 6:4, 13:1}` (f2 = 22, p6 = 4 < RHS = 5) has exactly **2** realizations as a simple 3-polytope in the entire space — found and validated autonomously by the new pipeline in 31 seconds (`output/conjecture_with_ce/C2.json`, full witness edge list included). Notably, all five triangle-free candidates at f2 = 22 are exhaustively **non**-realizable; the unique counterexample family member needs exactly one triangle.

- **plantri exhaustive tier** (decisive, both directions): `PolytopeConstructor` now calls [plantri 5.8](https://users.cecs.anu.edu.au/~bdm/plantri/) (Brinkmann & McKay, `allowed_deg` plugin, bundled in `tools/plantri/`) as Strategy 3. plantri enumerates *all* sphere triangulations with the target degree multiset, isomorph-free, in parallel `res/mod` splits — so a candidate either yields an explicit witness graph (dual of the triangulation, face-traced from the embedding) or is **proven non-realizable by exhaustion**. Definitive rejections surface in the 4-Check output as `[Tier 4 plantri] exhaustively NON-realizable`.
- **Cross-run realizability cache** (`output/realizability_cache.json`): exhaustive verdicts (never timeouts) persist across runs, so retries skip already-decided candidates instantly.
- **Explicit witness validation**: the 4-Check Validator accepts a `witness_graph` — re-verified with graphcalc (never trusted), exact p-vector match required.
- **Hopper witness fix** (critical): Hopper used to discard its own dual-hull geometry and route validation through the chop constructor, self-rejecting every exotic CE it found. It now extracts the primal witness graph from the dual hull (`hull.neighbors` facet adjacency) and submits it for verification.
- **Dual-space perturbation search** (Strategy 3b): hill-climbing with annealing + cap seeding over point configurations on the unit sphere; reaches topologies chop search cannot.
- **A\* chop search gated on p3 ≥ 1** (provable): every chop's last triangle persists in the final graph, so triangle-free targets are unreachable by chopping — the budget goes to the dual-space strategies instead.
- **Standalone batch decider**: `python tools/plantri/decide_ce_plantri.py --name <conjecture>` exhaustively decides all enumerated candidates of a conjecture (cheapest-first, resumable, stops on the first realizable hit).
- RL-track caveat documented: its chop-only action space provably cannot reach p3 = 0 targets.

---

## What's New in v2.5

**Counterexample side**

- **Tier-4 realizability constructor revived**: a stale `graphcalc.graphs.polytopes` import (that path no longer exists in graphcalc ≥ 1.3) silently failed and permanently disabled the Tier-4 witness constructor — every CE candidate outside the known families was auto-rejected with `graphcalc_unavailable`. Fixed to top-level imports. **All "no CE found" verdicts produced before this fix are unreliable and should be re-run.**
- **Stage 1.5 — Boundary Enumeration** (new, no API, seconds): exhaustively enumerates *every* DS-valid p-vector within bounds that satisfies the hypotheses and violates the conclusion (the random walk only samples this space), then tries to realize the most constructible candidates via the 4-Check Validator.

**Prover side**

- **Inventory-entailment pre-check**: before Stage 3, the orchestrator searches for *countermodels* — p-vectors satisfying the per-map arithmetic content of every Inventory axiom while violating the conjecture's conclusion. If any exist, no honest Lean proof can be derived from the current Inventory; Stage 3 is skipped with an explicit verdict naming sample countermodels (override: `FORCE_PROVER=true`).
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
- **Improved terminal display**: Step numbering `[1/6]`–`[6/6]`, a new `[5/6] Checking formalization quality...` section, a `[fix]` log line before each fix attempt, and a `fix #N` counter that increments across all rounds.

---

## What's New in v2.3

- **Hopper CE Finder** (new track in Stage 2): dual-space hop algorithm adapted from Swirszcz et al. (2025), achieves ~96% valid-hop rate by working in the dual simplicial polytope representation. Runs online: a small neural network is trained from scratch during the search and improves hop quality over time.
- **True parallelism**: the RL and Hopper tracks now run as separate **OS processes** (`multiprocessing.Process`) instead of threads. This eliminates GIL contention and PyTorch thread-pool competition — all three CE tracks now run on independent CPU cores simultaneously.
- **Inventory.lean**: a foundational Lean 4 lemma library (`polib/Inventory.lean`) containing formalized constituents of Euler's formula, the Jučovič theorem, and the general-genus p₆ inequality. Replaces the previous monolithic `Polib.lean`.

---

## Quick Start

```bash
# Run a single conjecture by ID (e.g. conjecture 43)
python -m run 43

# Equivalently:
python -m run c43

# Run all conjectures in batch (parallel workers)
python -m run
```

The short form `43` or `c43` resolves to any conjecture whose name ends with `_43` in `conjectures/conjectures.json`.

---

## Pipeline Overview

```
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
                         │ YES ──► [ 4-Check Validator ] ──► PASS ──► output
                         │ NO
                         ▼
┌─────────────────────────────────────────────────────────────┐
│  Stage 1.5 — Boundary Enumeration  (no API, seconds)        │
│  Exhaustive sweep of ALL DS-valid violating p-vectors       │
│  within bounds → realize best 40 via 4-Check Validator      │
└────────────────────────┬────────────────────────────────────┘
                         │ CE realized?
                         │ YES ──► output
                         │ NO
                         ▼
┌─────────────────────────────────────────────────────────────┐
│  Stage 2 — LLM + RL + Hopper  (three independent processes) │
│  ┌───────────────┐  ┌──────────────────┐  ┌─────────────┐  │
│  │  LLM Track    │  │  RL Track        │  │Hopper Track │  │
│  │  main thread  │  │  own process     │  │ own process │  │
│  │  Claude       │  │  PPO + FiLM-GNN  │  │ dual-space  │  │
│  │  15–30 rounds │  │  600 episodes    │  │ hop + NN    │  │
│  └──────┬────────┘  └────────┬─────────┘  └──────┬──────┘  │
│         └───────────────────┬┴───────────────────┘         │
│                             ▼                               │
│                   [ 4-Check Validator ]                     │
│                   first PASS → stop all tracks              │
└────────────────────────┬────────────────────────────────────┘
                         │ CE found?
                         │ YES ──► output/conjecture_with_ce/{C<id>}.json
                         │ NO
                         ▼
            [ Inventory-entailment pre-check ]
                         │ countermodels exist?
                         │ YES ──► explicit verdict, Stage 3 skipped
                         │         (override: FORCE_PROVER=true)
                         │ NO
                         ▼
┌─────────────────────────────────────────────────────────────┐
│  Stage 3 — Lean 4 Prover                                    │
│  Blueprint decomposition + compile-fix loop                 │
│  Lemma search over Mathlib + polib/Inventory.lean           │
└────────────────────────┬────────────────────────────────────┘
                         ▼
              output/conjecture_without_ce/{id}.lean
```

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

This move changes two face counts while keeping the DS sum at exactly 12. The walk starts from a perturbed dodecahedron, runs for up to 200,000 steps per restart across 60 restarts, and greedily maximises the **violation gap** (how strongly the conclusion is broken). Any candidate with a positive gap is sent to the 4-Check Validator.

Terminal output:

```
[Stage 1] Starting random walk to find counterexamples...
Random walk exhausted, falling back to LLM + RL + Hopper...
```

---

## Stage 1.5 — Boundary Enumeration

The random walk *samples* the DS lattice; Stage 1.5 *exhausts* it within bounds.
It enumerates every p-vector that

- is non-negative with DS sum = 12,
- satisfies all conjecture hypotheses, and
- violates the conclusion,

over all large-face multisets (sizes 7..`CE_ENUM_KMAX`, at most
`CE_ENUM_NLARGE_MAX` faces ≥ 7) and total face counts up to `CE_ENUM_F2_MAX`.
Candidates are sorted for constructibility (small f₂, small max face, more
triangles) and the best `CE_ENUM_REALIZE_MAX` are sent to the 4-Check
Validator with `CE_ENUM_REALIZE_TIMEOUT` (default 90) seconds of constructor
budget each — enough for the plantri exhaustive tier to fully decide f₂ ≈ 22
candidates on a multicore machine.

```
[Stage 1.5] 374 arithmetic CE candidate(s) within bounds; trying to realize the 40 most constructible (90s each)...
[Stage 1.5] CE realized: {3: 1, 5: 16, 6: 4, 13: 1}
[Check p-vector] ✓ Realizability: [Tier 4 Constructor] plantri_exhaustive: witness graph with 40 vertices, ...
```

A realized candidate is a **verified counterexample** (`found_by:
"boundary_enumeration"`). This is exactly how C2 was refuted (31 s end-to-end).
If *no* arithmetic candidate exists at all, the conjecture is arithmetically
tight in this region — strong evidence for Stage 3.

---

## Stage 2 — LLM + RL + Hopper Parallel Search

Three tracks run in **true parallel** — each track is isolated from the others: the RL and Hopper tracks run as separate OS processes (`multiprocessing.Process`) so they have independent CPU cores and no GIL or PyTorch thread-pool contention. All three share a single `multiprocessing.Event` stop signal: the first track to produce a validated CE sets the event and causes the others to exit promptly.

```
[Stage 2] RL episodes: 600  |  LLM rounds: 15  |  Hopper: on
```

### LLM Track (main thread)

- Up to **15–30 rounds**, each asking Claude for 3–5 candidate p-vectors
- Each round's prompt includes: the conjecture statement, all previously tried candidates (up to 50), and the last 5 failures with reasons
- Candidates are hard-deduplicated across rounds via frozenset keys; the LLM cannot repeat a vector
- Passing candidates are sent to the 4-Check Validator

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
[validation check ce from rl] 1 CE candidate(s) found, running 4 checks
[validation check ce from rl] √ Dehn-Sommerville: DS sum = 12 ✓
[validation check ce from rl] √ Hypotheses: all satisfied
[validation check ce from rl] √ Conclusion: p6=5 < RHS=8.3 — violated by 3.3
[validation check ce from rl] √ Realizability: [RL agent] graph verified as simple 3-polytope by graphcalc
[validation check ce from rl] The ce candidate is valid, saved CE JSON → output/conjecture_with_ce/C43.json
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

When Hopper finds a violating p-vector, it extracts the **primal witness graph** directly from its dual hull (facet adjacency via `hull.neighbors`) and submits it to the 4-Check Validator's `witness_graph` path — the graph is re-verified with graphcalc, so exotic candidates no longer die at the chop constructor.

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
[validation check ce from hopper] CE candidate from Hopper, running 4 checks
[validation check ce from hopper] √ Dehn-Sommerville: DS sum = 12 ✓
[validation check ce from hopper] √ Hypotheses: all satisfied
[validation check ce from hopper] √ Conclusion: p6=0 < RHS=1.0 — violated
[validation check ce from hopper] √ Realizability: [Tier 2] prism family {4:7, 7:2}
[validation check ce from hopper] CE valid, saved CE JSON → output/conjecture_with_ce/C13.json
```

If Hopper exhausts all steps without a CE:

```
[Hopper ce finding] Stopped by stop_event
```

(or simply no output if another track already found a CE and set the stop event)

---

## The 4-Check Validator

Every CE candidate — from the random walk, the LLM, the RL agent, or Hopper — must pass all four checks. Failure at any check immediately rejects the candidate.

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
2. **plantri exhaustive decision** (for $f_2 \leq$ `PLANTRI_F2_MAX`, default 26): enumerates *all* dual triangulations with the target degree multiset in parallel splits — returns a witness graph, or **proves non-realizability by exhaustion** (verdict cached across runs in `output/realizability_cache.json`)
3. Dual-space perturbation search (annealed point-configuration search on the sphere; handles triangle-free and single-large-face targets)
4. A\* chop-search from dodecahedron / tetrahedron / $k_{max}$-gon prism — only attempted when the target has $p_3 \geq 1$ (chop results always contain a triangle, so triangle-free targets are provably unreachable)

After construction, `graphcalc` verifies the graph's p-vector matches the target exactly and confirms it is a valid simple polytope graph. **If all strategies fail, the CE is rejected with no fallback.** There is no "probably realizable" path — only an explicit verified graph is accepted. A plantri exhaustion verdict is stronger than a rejection: it *proves* the p-vector is not realizable.

CE finders that hold their own geometric witness (Hopper's dual hull) submit it via the validator's `witness_graph` parameter — the graph is re-verified with graphcalc, never trusted.

Check output format (all four checks printed for each candidate):

```
[validation check ce from rl] √ Dehn-Sommerville: DS sum = 12 ✓
[validation check ce from rl] √ Hypotheses: all satisfied
[validation check ce from rl] √ Conclusion: p6=5 < RHS=8.3 — violated by 3.3
[validation check ce from rl] √ Realizability: [RL agent] graph verified as simple 3-polytope by graphcalc
```

```
[validation check ce from hopper] √ Dehn-Sommerville: DS sum = 12 ✓
[validation check ce from hopper] √ Hypotheses: all satisfied
[validation check ce from hopper] √ Conclusion: p6=0 < RHS=1.0 — violated
[validation check ce from hopper] ✗ Realizability: [Tier 4 Constructor] all construction strategies exhausted — CE rejected
```

---

## Output

### Counterexample found → `output/conjecture_with_ce/C{id}.json`

```json
{
  "conjecture_id": "auto_20260310_142638_43",
  "conjecture_latex": "if ((is_simple) and (f_2>=_30)), then p6 >= ...",
  "hypotheses": ["(is_simple)", "(f_2>=_30)"],
  "conclusion": "p6 >= (-5*sum_pk_after_p6 + 10)",
  "status": "failed",
  "counterexample": {
    "p_vector": [38, 7, 6, 5, 2, 1, 3, 1, 1, 0, 0, 1],
    "p3": 38, "p4": 7, "p5": 6, "p6": 5,
    "f2": 70,
    "num_vertices": 136,
    "num_edges": 204
  },
  "found_by": "rl_agent",
  "found_at_round": 137,
  "violation_detail": "gap=0.0000, margin=-0.3415",
  "found_at": "2026-05-29T13:34:00+00:00",
  "other_candidates_not_checked": []
}
```

`found_by` is one of `"pvector_walk"`, `"boundary_enumeration"`, `"llm_agent"`, `"rl_agent"`, or `"hopper_agent"`. CE JSONs produced via an explicit witness include the full edge list and the reproduction command (see `output/conjecture_with_ce/C2.json`).

The output filename uses the **short ID** (`C43.json`) derived from the trailing number of the full conjecture name.

### No counterexample → `output/conjecture_without_ce/{id}.lean`

If all three tracks in Stage 2 exhaust their budgets, the conjecture goes through the **Inventory-entailment pre-check** and then (if it passes) to **ProverAgent** (Stage 3). See the [Stage 3](#stage-3--lean-4-prover) section below for the pre-check, the full 6-step pipeline, quality checker, inline retry loop, and cross-run failure memory.

> **Note on `sorry` placeholders:** Sub-goals that require planar graph geometry lemmas not yet present in Mathlib (Steinitz's theorem, Eberhard's theorem, face-counting for 3-polytopes) are left as `sorry`. The surrounding proof structure still type-checks and compiles.

---

## Stage 3 — Lean 4 Prover

When no counterexample is found, **ProverAgent** produces a Lean 4 formalization through a 6-step pipeline.

### Inventory-Entailment Pre-Check (gate before Stage 3)

Before any prover work, the orchestrator searches for **countermodels**: p-vectors that satisfy the per-map arithmetic content of every `Inventory.lean` axiom (Euler/handshake/regularity, occupation feasibility `3·p₃ ≤ Σ_{k≥4}⌊k/2⌋·p_k`, the Jučovič inequality when m ≥ 6) yet violate the conjecture's conclusion. If one exists, **no honest Lean proof can be derived from the current Inventory** — either the conjecture is false (the countermodels are unrealized CE candidates) or Inventory needs new geometric content. Stage 3 is skipped with an explicit verdict:

```
[Entailment pre-check] FAIL — conclusion is NOT entailed by Inventory.lean
  374 p-vector(s) within bounds satisfy every Inventory axiom (arithmetic content) yet violate the conclusion, e.g.:
    {5: 17, 6: 4, 11: 1}  (f2=22)
  Consequence: no honest Lean proof exists from the current Inventory.
  Skipping Stage 3. (set FORCE_PROVER=true to override)
```

### Soundness Guard

Generated proofs must work only with the `maps` parameter given in the theorem signature. Any construction of a `SimplyCon3ConnectedMap` instance — `.mk`, a structure literal `{ m := …, p_i := … }`, an ascribed anonymous constructor `⟨…⟩ : SimplyCon3ConnectedMap`, a `where`-definition, or a `{ maps with … }` copy-update — is rejected **before compilation** (error class `X`, fed back to the fix loop) and independently fails the quality check. Reason: the geometric axioms are sorried statements that hold only for maps of real polytopes; applied to fabricated data they yield `False` (e.g. v = 0, e = 0 ⟹ `euler_formula` gives `0 = 2`), from which any goal is "provable".

### The 6-Step Pipeline

| Step | Name | What it does |
|---|---|---|
| `[1/6]` | Parse conjecture | Reads the JSON formula and resolves the conjecture name |
| `[2/6]` | Extract & lock goal | Derives the root Lean theorem signature; caches it in `store.json` (keyed by formula hash) |
| `[3/6]` | Decompose blueprint | Calls Claude to decompose the root goal into a DAG of helper lemmas; computes topological order |
| `[4/6]` | Formalize nodes | For each node in topological order: search hints → generate Lean → compile → fix loop (up to `MAX_ROUNDS_PER_NODE` rounds) |
| `[5/6]` | Check quality | Semantic quality check for every node (see below) |
| `[6/6]` | Save output | Writes the complete `.lean` file to `output/conjecture_without_ce/` |

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
[1/6] Parsing conjecture...
      theorem: C2 (0 steps)
[2/6] Extracting & locking goal...
      [cache hit] goal loaded from store (key=f33f8...)
      signature: theorem C2 (maps : SimplyCon3ConnectedMap 0) ...
[3/6] Decomposing blueprint...
      nodes: ['C2_DomainConstraintsFromMap', 'C2_LowerDegreeFacesBound', 'C2_MainGoalConversion', 'C2']
      topo order: ['C2_DomainConstraintsFromMap', ...]
[4/6] Formalizing nodes...
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
[5/6] Checking formalization quality...
  [C2_DomainConstraintsFromMap] Quality: PASS (score=1.00)
    • Soundness guard: PASS — no instance construction
    • Sorry audit: PASS — 0 sorry
    • Formula faithfulness: N/A (intermediate helper node, not root theorem)
  [C2] Quality: PASS (score=0.90)
    • Soundness guard: PASS — no instance construction
    • Sorry audit: PASS — 0 sorry
    • Conclusion match: PASS
    • Hypotheses covered: PASS
    • No extra constraints: PASS
    • Overall faithfulness: PASS
    • Proof structure: PASS (12 tactic steps)
[5.5/6] Validating Polib...
  [polib-validate] Polib builds cleanly — no repairs needed
[6/6] Formalization saved → /home/.../output/conjecture_without_ce/c2.lean

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
| §4 — p₆ inequality (genus g) | `p6.tex` | Partial: edge-count equation proved; inequality sorry |
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
| `equality_family` | existence of infinite equality family |

Derived in §2 (proved, **not** an axiom):

| Lemma | Statement |
|---|---|
| `kgon_occupation_bound` | $\text{occ}(k) \leq \lfloor k/2 \rfloor \cdot p_k$ — proved from `occupation_bound` |

> **Soundness fix (2026-06)**: the former `kgon_occupation_bound` and `quad_occ_reduction` quantified over arbitrary `Finset ℕ` instead of the map's occupation data and were refutable inside Lean (e.g. occ = {0,1,2}, k = 4 gives 3 ≤ 2), making the axiom base inconsistent. `kgon_occupation_bound` is restated on `total_occ` and proved; `quad_occ_reduction` ("an $r$-gon adjacent to a quad occupies $\leq \lfloor r/2 \rfloor - 1$") is **removed** — its faithful statement needs face-adjacency data the structure does not carry (the same Mathlib gap that blocks `Juc_InequalityPart`).

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
├── run.py                              # CLI entry point (python -m run <id>)
├── conjectures/
│   └── conjectures.json               # All conjectures (unsolved / solved)
├── agent/
│   ├── config.py                       # Config (env vars, paths, model names)
│   ├── claude_sdk.py                   # Thin wrapper around the claude CLI binary
│   ├── conjectures.py                  # JSON loader + formula canonicalizer
│   ├── orchestrator/
│   │   ├── orchestrator.py             # Top-level pipeline (stages 1–3 + pre-check)
│   │   └── tools/
│   │       ├── check_pvector.py        # 4-Check Validator
│   │       ├── polytope_constructor.py # Witness graph builder (Tier 4)
│   │       ├── ce_enumerator.py        # Stage 1.5 enumeration + entailment pre-check
│   │       └── conjecture_parser.py    # Formula → ParsedConjecture
│   ├── rl_ce_finder/
│   │   └── agent.py                    # PPO + FiLM-GNN CE search
│   ├── llm_ce_finder/
│   │   └── agent.py                    # Claude-based CE search
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
├── tools/
│   └── plantri/
│       ├── plantri_ad                  # plantri 5.8 + allowed_deg plugin (patched)
│       ├── decide_ce_plantri.py        # standalone batch realizability decider
│       └── plantri-guide.txt           # upstream documentation (Apache 2.0)
├── output/
│   ├── conjecture_with_ce/             # C{id}.json — CE results (incl. witness edges)
│   ├── conjecture_without_ce/         # {id}.lean — Lean proofs
│   ├── realizability_cache.json        # cross-run exhaustive verdicts
│   └── plantri_verdicts_{id}.json      # batch decider results
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
FORCE_PROVER=false                    # run Stage 3 even if the entailment pre-check fails

# Stage 1.5 / entailment pre-check bounds
CE_ENUM_F2_MAX=36                     # max total face count enumerated
CE_ENUM_KMAX=20                       # max face size enumerated
CE_ENUM_NLARGE_MAX=2                  # max number of faces with k >= 7
CE_ENUM_MAX_RESULTS=400               # cap on candidates kept
CE_ENUM_REALIZE_MAX=40                # candidates sent to the witness constructor
CE_ENUM_REALIZE_TIMEOUT=90            # seconds per construction attempt

# plantri exhaustive tier
PLANTRI_AD=tools/plantri/plantri_ad   # path to the plantri_ad binary
PLANTRI_F2_MAX=26                     # max f2 decided exhaustively (runtime grows fast)
```

---

## Usage

```bash
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

# Exhaustively decide ALL enumerated CE candidates of one conjecture (standalone,
# resumable, stops on the first realizable hit). This is how C2 was refuted.
python tools/plantri/decide_ce_plantri.py --name auto_20260310_142638_43 --f2-max 24
```

---

## Adding New Conjectures

Edit `conjectures/conjectures.json` and add an entry to the `"unsolved"` array:

```json
{
  "name": "auto_20260310_142638_99",
  "formula": "if ((is_simple) and (f_2>=_20)), then p6 >= (-2*sum_pk_after_p6 + 4)"
}
```

Names must end with a unique integer suffix (used to derive the short ID `C99`). Run with `python -m run 99`.
