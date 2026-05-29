# Polytope Conjecture Prover — v2.0

An automated pipeline for deciding conjectures about simple convex 3-polytopes.
Given a conjecture in JSON formula format, the system either finds a **verified counterexample** (backed by an explicit witness polytope) or produces a **Lean 4 formalization** of the proof.

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
┌─────────────────────────────────────────────────────────┐
│  Stage 1 — P-Vector Random Walk  (no API, <1 min)       │
│  DS-preserving lattice walk, 60 restarts × 200k steps   │
└──────────────────────┬──────────────────────────────────┘
                       │ CE candidate?
                       │ YES ──► [ 4-Check Validator ] ──► PASS ──► output
                       │ NO
                       ▼
┌─────────────────────────────────────────────────────────┐
│  Stage 2 — Parallel LLM + RL Search  (~10–30 min)       │
│  ┌──────────────────────┐  ┌──────────────────────────┐ │
│  │  LLM Track           │  │  RL Track (PPO + GNN)    │ │
│  │  Claude, 30 rounds   │  │  600 episodes            │ │
│  │  3–5 candidates each │  │  graph construction      │ │
│  └──────────┬───────────┘  └──────────┬───────────────┘ │
│             └──────────┬──────────────┘                  │
│                        ▼                                  │
│              [ 4-Check Validator ]                        │
│              first PASS → stop both tracks               │
└──────────────────────┬──────────────────────────────────┘
                       │ CE found?
                       │ YES ──► output/conjecture_with_ce/{C<id>}.json
                       │ NO
                       ▼
┌─────────────────────────────────────────────────────────┐
│  Stage 3 — Lean 4 Prover                                │
│  Blueprint decomposition + compile-fix loop             │
└──────────────────────┬──────────────────────────────────┘
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

---

## Stage 2 — LLM + RL Parallel Search

Two tracks run as concurrent threads. Both share a single `stop_event`: the first track to produce a validated CE sets the event and terminates the other. Both tracks also share a `PVectorCheckAgent` instance.

### LLM Track

- Up to **30 rounds**, each asking Claude for 3–5 candidate p-vectors
- Each round's prompt includes: the conjecture statement, the list of all previously tried candidates (up to 50), and the last 5 failures with reasons
- All candidates are hard-deduplicated across rounds via frozenset keys; the LLM cannot repeat a vector even if it ignores the prompt
- Candidates that parse successfully are sent to the 4-Check Validator

### RL Track (PPO + FiLM-GNN)

- A **PPO policy** with a FiLM-conditioned graph neural network learns to build cubic planar graphs via repeated **node-chop** operations (replace a degree-3 vertex with a triangle)
- The environment reward is: `polytopehood_bonus + 100 × max(0, violation_gap)`
- Any episode that produces a graph satisfying the hypotheses and violating the conclusion is extracted as a CE candidate and sent to the 4-Check Validator
- Trained for up to **600 episodes**; stops early if a CE is validated

Terminal output during Stage 2:

```
[Stage 2] RL episodes: 600  |  LLM rounds: 30
[rl ce finding] Episode 1/600
[LLM ce finding] Round 1/30: Asking LLM to find ces
[rl ce finding] Episode 100 | R: 22.62 | Len: 12.3 | ...
[rl ce finding] Episode 137 ce found! p_vector=[38, 7, 6, ...]
[LLM ce finding] Round 1/30: skipping (call aborted: stop_event set)
[LLM ce finding] Stopped and waiting ce candidate to be checked
[validation check ce from rl] 1 CE candidate(s) found, running 4 checks
```

---

## The 4-Check Validator

Every CE candidate — from the random walk, the LLM, or the RL agent — must pass all four checks. Failure at any check immediately rejects the candidate.

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

The output filename uses the **short ID** (`C43.json`) derived from the trailing number of the full conjecture name.

### No counterexample → `output/conjecture_without_ce/{id}.lean`

If both Stage 1 and Stage 2 exhaust their budgets, the conjecture is passed to **ProverAgent** which:

1. Decomposes the goal into a proof blueprint (sub-goals as a dependency graph)
2. Searches Mathlib4 (TF-IDF cosine similarity) and `polib/Polib.lean` (user proof library) for relevant lemmas
3. Generates Lean 4 tactics with Claude and compiles with `lake build` (up to 3 compile-fix rounds per node)
4. Writes the complete formalization to `output/conjecture_without_ce/{id}.lean`

> **Note on `sorry` placeholders:** Sub-goals that require planar graph geometry lemmas not yet present in Mathlib (Steinitz's theorem, Eberhard's theorem, face-counting for 3-polytopes) are left as `sorry`. The surrounding proof structure still type-checks and compiles. These stubs are explicit, locatable placeholders for future proofs.

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
│   └── prover/
│       ├── agent.py                    # Lean 4 formalization agent
│       └── tools/
│           ├── lean_compiler.py        # lake build wrapper
│           ├── search.py               # Mathlib + polib lemma search
│           ├── blueprint.py            # Proof decomposition
│           └── latex_parser.py         # LaTeX theorem parsing
├── output/
│   ├── conjecture_with_ce/             # C{id}.json — CE results
│   └── conjecture_without_ce/         # {id}.lean — Lean proofs
├── polib/
│   └── Polib.lean                      # Accumulated user-proved lemmas
└── requirements.txt
```

---

## Installation

### 1. Python dependencies

```bash
pip install -r requirements.txt
```

Key packages: `torch==2.12.0`, `graphcalc==1.3.1`, `networkx==3.5`, `scikit-learn==1.7.2`, `numpy==2.3.5`, `matplotlib==3.10.6`, `python-dotenv==1.1.0`, `tqdm==4.67.1`.

> **PyTorch CPU-only (recommended unless you have a CUDA GPU):**
> ```bash
> pip install torch==2.12.0 --index-url https://download.pytorch.org/whl/cpu
> ```

### 2. Lean 4 + Mathlib

```bash
# Install elan (Lean toolchain manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Fetch Mathlib cache and build (first time: ~30–60 min)
cd lean_project
lake exe cache get
lake build
```

### 3. Claude CLI

The LLM track and prover agent call Claude through the `claude` CLI binary (no `ANTHROPIC_API_KEY` needed in the environment — authentication is handled by the CLI's own OAuth session).

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

# RL search
# (RL episodes and LLM rounds are set per-run via CLI flags or defaults)

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
