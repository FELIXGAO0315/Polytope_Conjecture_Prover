# Polytope Conjecture Prover

An automated pipeline for deciding conjectures about simple convex 3-polytopes.
Given a conjecture in LaTeX, the system either finds a **verified counterexample** (with an explicit witness polytope graph) or produces a **Lean 4 formalization** of the conjecture.

---

## Overview

```
conjectures/individual/C*.tex
         │
         ▼
   [ Conjecture Parser ]
         │  ParsedConjecture (hypotheses, conclusion, IRIS scores)
         ▼
   [ P-Vector Random Walk ]  ──────────────────────────────────┐
         │                                                      │
         │  CE candidate found?                                 │
         │  YES ──► [ 4-Check Validator ] ──► PASS ──► output  │
         │                          │                           │
         │                          └── FAIL ──────────────────►│
         │  NO                                                   │
         ▼                                                       │
   [ LLM Track ]  +  [ RL Track ]  (run in parallel) ◄─────────┘
         │
         │  CE candidate found?
         │  YES ──► [ 4-Check Validator ] ──► PASS ──► output/conjecture_with_ce/{id}.json
         │                          │
         │                          └── FAIL ──► next candidate
         │  NO (all tracks exhausted)
         ▼
   [ Prover Agent ]
         │
         ▼
   output/conjecture_without_ce/{id}.lean
```

---

## Input Format

Each conjecture is a `.tex` file containing a single `theorem` environment:

```latex
\begin{theorem}[C10]
$\text{If }\;\text{simple} \;\wedge\; f_2 \geq 19,\;\text{then }\;
p_6 \geq - \tfrac{7}{2}\,\sum_{k \geq 7} p_k + 7$
\end{theorem}
```

- The theorem label (`C10`) becomes the conjecture ID.
- The system parses the hypothesis block and conclusion automatically.
- A directory of individual files (`conjectures/individual/C*.tex`) or a combined longtable file can be used.

**Run (single conjecture):**
```bash
python -m agent.orchestrator --id C10
```

**Run (batch — all conjectures in parallel):**
```bash
python -m agent.orchestrator --batch --tex conjectures/individual/
```

---

## Stage 1 — P-Vector Random Walk

Before launching the heavier LLM and RL machinery, a fast **Dehn-Sommerville lattice walk** explores the space of valid p-vectors directly (no graph construction, no API calls).

**How it works:**

Every valid simple 3-polytope p-vector satisfies:

$$\sum_{k \geq 3} (6-k)\, p_k = 12 \quad \text{(Dehn-Sommerville / Euler)}$$

The walk stays on this lattice by using DS-preserving moves: for a pair $(k_1 < 6,\; k_2 > 6)$, the move
$$p_{k_1} \mathrel{+}= (k_2 - 6), \quad p_{k_2} \mathrel{+}= (6 - k_1)$$
always keeps the DS sum at 12.

The walk starts from a perturbed dodecahedron, runs up to 200,000 steps across 60 restarts, and greedily maximises the violation gap (how much the conclusion is broken). Any candidate that achieves a positive gap is immediately sent to the **4-Check Validator**.

If the walk exhausts all restarts without a validated CE, the system falls through to Stage 2.

---

## Stage 2 — LLM + RL Counterexample Search (parallel)

Two search tracks run simultaneously, sharing a `stop_event` so that whichever finds a validated CE first terminates the other.

### LLM Track

Claude is prompted with the conjecture statement, its hypotheses, conclusion, and a list of previously failed candidates. It returns 3–5 candidate p-vectors per round (up to 30 rounds). Each candidate that passes a quick syntactic check is immediately sent to the 4-Check Validator.

### RL Track (PPO)

A graph neural network policy (FiLM-conditioned GNN + PPO) learns to build cubic planar graphs by repeatedly applying the **node-chop** operation (replace one degree-3 vertex with a triangle). The environment rewards graphs that:

- are valid simple polytopes (`graphcalc.simple_polytope_graph`)
- satisfy the conjecture's hypotheses
- violate the conjecture's conclusion

Graphs discovered during training that satisfy all three conditions are extracted as CE candidates and sent to the 4-Check Validator.

---

## Stage 3 — 4-Check Validator

**Every** CE candidate — from the random walk, the LLM, or the RL agent — must pass all four checks before it is accepted. Failure at any check causes the candidate to be silently discarded and the search to continue.

---

### Check 1 — Dehn-Sommerville + Euler Consistency

Verifies that the p-vector is arithmetically consistent with a simple convex 3-polytope:

| Condition | Formula | Why |
|---|---|---|
| Non-negativity | $p_k \geq 0$, all $k \geq 3$ | Face counts cannot be negative |
| Dehn-Sommerville | $\sum_k (6-k)\,p_k = 12$ | Euler's formula + 3-regularity of the vertex graph |
| Minimum size | $f_2 = \sum p_k \geq 4$ | Tetrahedron is the smallest simple polytope |
| Euler count | $V = 2(f_2-2) \geq 4$, $E = 3(f_2-2)$ | Follows from 3-regularity and $V-E+F=2$ |

A candidate failing this check is not a valid p-vector at all — it is rejected immediately without running the remaining checks.

---

### Check 2 — Hypotheses Satisfied

Evaluates each hypothesis of the conjecture against the candidate p-vector. Supported forms:

- `f_2 \geq N` / `f_2 \leq N`
- `p_k \geq N` / `p_k \leq N` / `p_k = N`
- `\text{simple}` (assumed structurally — always satisfied for cubic planar graphs)

All hypotheses must be satisfied simultaneously. If any hypothesis fails, the candidate is not in the domain of the conjecture and is rejected.

---

### Check 3 — Conclusion Violated

Evaluates the conjecture conclusion against the candidate p-vector and confirms it is genuinely violated. For conjectures of the form $p_6 \geq \text{RHS}$:

- Computes `RHS` by substituting the p-vector into the RHS expression (handling fractions, sums $\sum_{k \geq N} p_k$, etc.)
- Checks that $p_6 < \text{RHS}$ (strict violation)
- Computes the **violation margin** = $\text{RHS} - p_6$
- Issues a warning if the margin is $< 0.5$ (potential floating-point precision risk for fractional RHS expressions)

A candidate where the conclusion actually holds is not a counterexample and is rejected.

---

### Check 4 — Realizability (mandatory hard gate)

**This is the most critical check.** Passing Checks 1–3 proves the p-vector is arithmetically consistent and violates the conjecture, but DS = 12 is a *necessary* condition for realizability, not a *sufficient* one. A p-vector that satisfies DS = 12 does not automatically correspond to a real polytope.

Check 4 requires constructing an **explicit witness graph** — a 3-connected 3-regular planar graph whose face sizes match the candidate p-vector exactly. Without this, the CE is rejected regardless of how well it scores on the other checks.

The check proceeds through three tiers:

#### Tier 1 — Exact known polytopes

Constant-time lookup against a table of verified classical polytopes (each entry is confirmed DS = 12 by hand):

| p-vector | Name |
|---|---|
| `{3:4}` | Tetrahedron |
| `{4:6}` | Cube |
| `{5:12}` | Dodecahedron |
| `{3:2, 4:3}` | Triangular prism |
| `{4:5, 5:2}` | Pentagonal prism |
| `{3:4, 6:4}` | Truncated tetrahedron |
| `{4:6, 6:8}` | Truncated octahedron |

If the candidate matches any entry exactly → **ACCEPTED**.

#### Tier 2 — Proven infinite families

Checks membership in infinite families whose realizability is rigorously established:

- **Prism family** `{4:n, n:2}` for any $n \geq 7$: DS = $(6-4)n + (6-n)\cdot2 = 12$ ✓. Directly constructible for any $n$.
- **Fullerene family** `{5:12, 6:k}` for $k \geq 2$: DS = $12$ ✓. Infinite series of realizable polytopes. **Exception**: `{5:12, 6:1}` is a known *non-realizable* combination (Grünbaum 1967) — this specific case is **actively rejected** here rather than passed to Tier 4.

If the candidate matches a proven family → **ACCEPTED**. If it matches a known non-realizable pattern → **REJECTED immediately**.

> **Note on Eberhard's theorem:** The classic Eberhard interior criterion (which would fire when $\sum_{k \neq 6}(6-k)p_k < 12$) is provably unreachable here. Since $(6-6) = 0$, the $p_6$ term contributes nothing to the DS sum, so $\sum_{k \neq 6}(6-k)p_k = \text{DS} = 12$ always after Check 1 passes. There is no "interior" to reach; everything that survives Tier 1 and Tier 2 goes directly to Tier 4.

#### Tier 4 — PolytopeConstructor (mandatory)

If neither Tier 1 nor Tier 2 applies, the system attempts to **physically build a witness graph** using `PolytopeConstructor`. Strategies are tried in order:

1. **Exact known graphs** — O(1) construction for tetrahedron, cube, dodecahedron, prisms
2. **Prism direct construction** — O(n) edge list for any n-gonal prism
3. **A\* chop search from dodecahedron** — for targets with $f_2 \leq 30$; heuristic search using node-chop operations, guided by L1 p-vector distance
4. **A\* chop search from tetrahedron** — fallback for targets with $f_2 \leq 20$

Each strategy runs within a shared 30-second timeout. If any strategy produces a graph $G$:

- **P-vector verification**: `graphcalc` recomputes the p-vector of $G$ and confirms it matches the target exactly. A mismatch is treated as a construction failure.
- **Simple polytope check**: `graphcalc.simple_polytope_graph(G)` must confirm $G$ is a valid 3-connected cubic planar graph. If not, the CE is rejected.

**If all strategies are exhausted within the timeout, or if the constructor is unavailable, or if post-construction verification fails → the CE is REJECTED with `passed=False, critical=True`.**

This is a hard gate with no fallback. There is no "we couldn't construct it but it looks plausible" path. A CE is only accepted when there exists an explicit, verified, simple polytope graph whose p-vector matches the target.

---

## Stage 4 — Output

### Counterexample found

Written to `output/conjecture_with_ce/{id}.json`:

```json
{
  "conjecture_id": "C10",
  "status": "failed",
  "counterexample": {
    "p_vector": [0, 0, 14, 1, 0, 1],
    "p5": 14, "p6": 1, "p8": 1,
    "f2": 16, "num_vertices": 28, "num_edges": 42
  },
  "found_by": "llm_finder",
  "violation_detail": "p6=1.0 < RHS=2.0 (violation)"
}
```

### No counterexample found → Formalization

If both the random walk and the LLM + RL tracks exhaust their budgets without a validated CE, the conjecture is passed to **ProverAgent** for Lean 4 formalization.

ProverAgent:
1. Decomposes the conjecture into a blueprint of sub-goals
2. Searches Mathlib and an internal proof library (polib) for relevant lemmas
3. Generates Lean 4 proof code using Claude, iterating through a compile-fix loop with `lake build`
4. Writes the result to `output/conjecture_without_ce/{id}.lean`

#### Caveat: `sorry` placeholders

The formalized proofs currently compile with `sorry` in place of certain sub-goals. This is a deliberate, known limitation — not a bug:

> Lean 4's Mathlib represents graphs as `SimpleGraph` (an abstract combinatorial structure), but our conjectures concern **simple convex 3-polytopes**, which require a planar, 3-connected, 3-regular graph with a fixed embedding. The combinatorial geometry lemmas needed to connect these two representations (e.g., Steinitz's theorem, Eberhard's theorem, counting arguments over planar faces) are not yet available in Mathlib.

Rather than leaving the formalization entirely empty, `sorry` is used as a **placeholder** that:
- marks exactly which sub-goals remain unproven
- allows the surrounding proof structure to **type-check and compile** under `lean4`
- gives a complete, inspectable blueprint for a future human or automated proof

When Mathlib's coverage of planar graph theory matures, the `sorry` stubs can be replaced incrementally without restructuring the proof.

---

## Project Structure

```
agent/
  orchestrator.py              # Top-level pipeline: CE search → ProverAgent
  counterexample_finding_agent.py  # RL (PPO) CE search
  prover_agent.py              # Lean 4 formalization
  tools/
    check_pvector.py           # 4-Check Validator (the core CE gate)
    polytope_constructor.py    # Witness graph builder (Tier 4)
    conjecture_parser.py       # LaTeX → ParsedConjecture
    lean_compiler.py           # lake build wrapper
    blueprint.py               # Proof decomposition
    search.py                  # Mathlib / polib search
conjectures/
  individual/C*.tex            # One conjecture per file
output/
  conjecture_with_ce/          # CE JSON files
  conjecture_without_ce/       # Lean 4 proof files
```
