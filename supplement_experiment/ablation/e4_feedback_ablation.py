#!/usr/bin/env python3
"""E4: matched-budget controlled ablation of OUTCOME-DRIVEN FEEDBACK in the
generator.

Two arms, one generation each, SAME frozen registry state, SAME discovery table,
LLM OFF in both (isolates the non-LLM algorithmic feedback channels; avoids VPN):
  * ARM A (feedback ON) : Graffiti3 + stratified + dynamic-cells + mutations + miner
  * ARM B (feedback OFF): Graffiti3 + stratified + miner   (dynamic-cells/mutations stubbed)
All verification gates (full-pool consistency, shape-repeat tightness, LP-overfit,
trivial-RHS, semantic-dup) are IDENTICAL in both arms — only the proposal-side
outcome conditioning differs. Both arms run dry-run (no registry writes).

SAFETY: reconcile_from_artifacts (the one registry writer reachable in dry-run) is
neutralized; the registry file is checksummed before/after and must be unchanged.
READ-ONLY w.r.t. the registry.
"""
import os, re, json, random, hashlib, time, statistics, sys

SEED = int(sys.argv[1]) if len(sys.argv) > 1 else 0
random.seed(SEED)
try:
    import numpy as np; np.random.seed(SEED)
    _HAS_NP = True
except Exception:
    _HAS_NP = False

ROOT = "/home/felix_gao/Polytope_Conjecture_Prover"
os.chdir(ROOT)
sys.path.insert(0, ROOT)

from agent.conjecture_generator import agent as gen_mod
from agent.conjecture_generator.agent import ConjectureGenerator
from agent.conjecture_generator.tools.dataset import build_discovery_table
from agent.conjecture_generator.tools.iris_scoring import compute_iris

# ---- SAFETY: freeze registry (neutralize the only dry-run-reachable writer) ----
gen_mod.reconcile_from_artifacts = lambda *a, **k: None
REG = os.path.join(ROOT, "conjectures/conjectures.json")
reg_before = hashlib.md5(open(REG, "rb").read()).hexdigest()

# ---- shared scoring pool: one build, used to score BOTH arms identically ----
_, SCORE_POOL, _ = build_discovery_table()

def hyp_cell(formula: str) -> str:
    m = re.search(r"if\s*\((.*)\)\s*,?\s*then", formula)
    inner = m.group(1) if m else ""
    atoms = sorted(a.strip() for a in re.split(r"\band\b", inner)
                   if a.strip() and "is_simple" not in a)
    return " & ".join(atoms) or "(simple only)"

_CAPTURE = {}
def _wrap_capture(orig):
    def wrapped(self, accepted, *a, **k):
        kept, drops = orig(self, accepted, *a, **k)
        _CAPTURE["sources"] = [src for _, src in kept]
        return kept, drops
    return wrapped

def run_arm(no_feedback: bool):
    random.seed(SEED)
    if _HAS_NP: np.random.seed(SEED)
    orig_mut = gen_mod.generate_mutations
    orig_dyn = ConjectureGenerator._dynamic_cells
    orig_semdup = ConjectureGenerator._drop_semantic_dupes
    ConjectureGenerator._drop_semantic_dupes = _wrap_capture(orig_semdup)
    if no_feedback:
        gen_mod.generate_mutations = lambda *a, **k: []
        ConjectureGenerator._dynamic_cells = lambda self, *a, **k: []
    _CAPTURE.clear()
    t0 = time.time()
    try:
        specs = ConjectureGenerator(g3_mode="fast", dry_run=True).run()  # client=None
    finally:
        gen_mod.generate_mutations = orig_mut
        ConjectureGenerator._dynamic_cells = orig_dyn
        ConjectureGenerator._drop_semantic_dupes = orig_semdup
    wall = time.time() - t0
    srcs = _CAPTURE.get("sources", [])
    rows = []
    for i, s in enumerate(specs):
        iris = compute_iris(s, SCORE_POOL) or {}
        trl = (iris.get("sort_keys", {}) or {}).get("TRL", 0.0) or 0.0
        rows.append({"name": s.name, "formula": s.formula, "cell": hyp_cell(s.formula),
                     "src": srcs[i] if i < len(srcs) else "?",
                     "T": iris.get("T"), "R": iris.get("R"), "L": iris.get("L"), "TRL": trl})
    return rows, wall

print("\n" + "="*78)
print("RUN ARM A — feedback ON")
print("="*78)
armA, wallA = run_arm(False)
print("\n" + "="*78)
print("RUN ARM B — feedback OFF (dynamic-cells + mutations stubbed)")
print("="*78)
armB, wallB = run_arm(True)

# ---- SAFETY check ----
reg_after = hashlib.md5(open(REG, "rb").read()).hexdigest()
assert reg_before == reg_after, "!!! REGISTRY FILE CHANGED — abort, investigate !!!"
print("\n[safety] registry checksum unchanged — OK")

def avg(rows, key):
    v = [r[key] for r in rows if r[key] is not None]
    return statistics.mean(v) if v else 0.0

def summarize(name, rows, wall):
    n = len(rows)
    cells = len(set(r["cell"] for r in rows))
    tight = sum(1 for r in rows if (r["T"] or 0) >= 0.999)
    hiTRL = sum(1 for r in rows if r["TRL"] >= 1e-2)
    degen = sum(1 for r in rows if r["TRL"] < 1e-4)
    src = {}
    for r in rows:
        tag = r["src"].split(":")[0]
        src[tag] = src.get(tag, 0) + 1
    print(f"\n[{name}]  wall={wall:.1f}s")
    print(f"  accepted conjectures      : {n}")
    print(f"  distinct hypothesis cells : {cells}")
    print(f"  mean IRIS-T               : {avg(rows,'T'):.3f}")
    print(f"  mean IRIS-TRL             : {avg(rows,'TRL'):.4f}")
    print(f"  fully-tight (T>=0.999)    : {tight}")
    print(f"  high-TRL (>=1e-2)         : {hiTRL}")
    print(f"  degenerate (TRL<1e-4)     : {degen}")
    print(f"  source composition        : {src}")
    return {"n": n, "cells": cells, "meanT": avg(rows,'T'), "meanTRL": avg(rows,'TRL'),
            "tight": tight, "hiTRL": hiTRL, "degen": degen, "src": src, "wall": wall}

sA = summarize("ARM A  feedback ON", armA, wallA)
sB = summarize("ARM B  feedback OFF", armB, wallB)

# novelty: cells/conjectures ONLY feedback produced
cellsA = set(r["cell"] for r in armA); cellsB = set(r["cell"] for r in armB)
only_feedback_cells = cellsA - cellsB
print(f"\n[delta] hypothesis cells reached ONLY with feedback: {len(only_feedback_cells)}")
for c in sorted(only_feedback_cells)[:12]:
    print(f"    + {c}")

outp = os.path.join(ROOT, f"supplement_experiment/ablation/out/e4_feedback_ablation_seed{SEED}.json")
json.dump({"seed": SEED, "armA": armA, "armB": armB, "summaryA": sA, "summaryB": sB,
           "only_feedback_cells": sorted(only_feedback_cells)},
          open(outp, "w"), indent=1)
print(f"\nwrote {outp}")
