# Polytope Conjecture Prover — v2.4

An automated pipeline for deciding conjectures about simple convex 3-polytopes.
Given a conjecture in JSON formula format, the system either finds a **verified counterexample** (backed by an explicit witness polytope) or produces a **Lean 4 formalization** of the proof.

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

Physically builds a 3-connected 3-regular planar witness graph using a sequence of strategies (each within a 30 s shared timeout):

1. Direct construction for known shapes and prisms
2. A\* chop-search from dodecahedron (for $f_2 \leq 30$)
3. A\* chop-search from tetrahedron (for $f_2 \leq 20$)

After construction, `graphcalc` verifies the graph's p-vector matches the target exactly and confirms it is a valid simple polytope graph. **If all strategies fail, the CE is rejected with no fallback.** There is no "probably realizable" path — only an explicit verified graph is accepted.

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

`found_by` is one of `"pvector_walk"`, `"llm_agent"`, `"rl_agent"`, or `"hopper_agent"`.

The output filename uses the **short ID** (`C43.json`) derived from the trailing number of the full conjecture name.

### No counterexample → `output/conjecture_without_ce/{id}.lean`

If all three tracks in Stage 2 exhaust their budgets, the conjecture is passed to **ProverAgent** (Stage 3). See the [Stage 3](#stage-3--lean-4-prover) section below for the full 6-step pipeline, quality checker, auto-retry loop, and cross-run failure memory.

> **Note on `sorry` placeholders:** Sub-goals that require planar graph geometry lemmas not yet present in Mathlib (Steinitz's theorem, Eberhard's theorem, face-counting for 3-polytopes) are left as `sorry`. The surrounding proof structure still type-checks and compiles.

---

## Stage 3 — Lean 4 Prover

When no counterexample is found, **ProverAgent** produces a Lean 4 formalization through a 6-step pipeline.

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

### Auto-Retry Loop

The orchestrator runs up to **3 attempts** per conjecture. After each attempt, nodes that compiled successfully are recorded as proved in Polib. On the next attempt, proved nodes are loaded from Polib and skipped — only the nodes that failed are re-attempted. This means partial progress from earlier attempts is never discarded.

### Cross-Run Failure Memory

When a node fails to compile after all fix rounds, the last error message plus up to 1 200 characters of the failed Lean code are stored in `store.json` (up to 4 records per node). On the next attempt, `_generate_lean` reads these records and prepends a block to the Claude prompt:

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
[5/6] Checking formalization quality...
  [C2_DomainConstraintsFromMap] Quality: PASS (score=1.00)
    • Sorry audit: PASS — 0 sorry
    • Formula faithfulness: N/A (intermediate helper node, not root theorem)
  [C2] Quality: PASS (score=0.90)
    • Sorry audit: PASS — 0 sorry
    • Conclusion match: PASS
    • Hypotheses covered: PASS
    • No extra constraints: PASS
    • Overall faithfulness: PASS
    • Proof structure: PASS (12 tactic steps)
[5.5/6] Validating Polib...
  [polib-validate] Polib builds cleanly — no repairs needed
[6/6] Formalization saved → /home/.../output/conjecture_without_ce/c2.lean

[Stage 3] Attempt 1/3 result: partial
  Failed nodes: ['C2_MainGoalConversion', 'C2']
  → Will retry …

[Stage 3] Retrying C2 (attempt 2/3) — proved nodes reloaded from Polib, retrying failed nodes …
[4/6] Formalizing nodes...
  [skip] C2_DomainConstraintsFromMap (proved)
  [skip] C2_LowerDegreeFacesBound (proved)
  [hints] C2_MainGoalConversion: 9 (combined, verified)
  [gen] C2_MainGoalConversion — 9 hints (validated)   ← uses cross-run failure context
  [ok]  C2_MainGoalConversion compiled (round 0)
  [saved] C2_MainGoalConversion → polib (proved)
[5/6] Checking formalization quality...
  [C2_DomainConstraintsFromMap] Retrying... (loaded from Polib)
    Quality: PASS (score=1.00)
    • Sorry audit: PASS — 0 sorry
    • Formula faithfulness: N/A (intermediate helper node, not root theorem)
  [C2_LowerDegreeFacesBound] Retrying... (loaded from Polib)
    Quality: PASS (score=1.00)
    ...

[Stage 3] Attempt 2/3 result: success

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
| `kgon_occupation_bound` | a $k$-gon occupies at most $\lfloor k/2 \rfloor$ triangle-edges |
| `quad_occ_reduction` | when $p_4 > 0$, adjacent $r$-gon occupation drops by 1 |
| `p_range` | $p_k = 0$ for $k > m$ |
| `occupation_conservation` | $\sum_{k \geq 4} \text{occ}(k) = 3p_3$ |
| `occupation_bound` | $0 \leq \text{occ}(k) \leq \lfloor k/2 \rfloor \cdot p_k$ |
| `equality_family` | existence of infinite equality family |

### §3 — Jučovič Theorem (sphere, g = 0)

**Proved without sorry:**

- `Juc_KGonMaxOccupation` — $k$-gon occupies at most $\lfloor k/2 \rfloor$ triangle-edges
- `Juc_QuadAdjacencyConstraint` — when $p_4 > 0$, adjacent $r$-gon occupation $\leq \lfloor r/2 \rfloor - 1$
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
│   │   ├── orchestrator.py             # Top-level 3-stage pipeline
│   │   └── tools/
│   │       ├── check_pvector.py        # 4-Check Validator
│   │       ├── polytope_constructor.py # Witness graph builder (Tier 4)
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
├── output/
│   ├── conjecture_with_ce/             # C{id}.json — CE results
│   └── conjecture_without_ce/         # {id}.lean — Lean proofs
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
COMPILE_TIMEOUT_SECONDS=180           # lake build timeout (seconds)
MAX_PARALLEL_NODES=6                  # parallel proof threads
CLAUDE_TIMEOUT=150                    # claude CLI call timeout (seconds)
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
