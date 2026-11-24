#!/usr/bin/env python3
"""Instantiate the "enumerate + fit" baseline and show it
is UNSOUND in this domain.

Baseline: "listing all realizable p-vectors [up to f2<=36]
and fitting the tightest linear bounds might already recover most of the reported
results."  We run exactly that:
  * INPUT  = every realizable p-vector in the plantri realizability cache
             (all have f2<=33, i.e. inside the f2<=36 box).
  * We fit the tightest linear bound on p6 the baseline can see.
  * OUT-OF-SAMPLE TEST = our 206 witness-verified refutation p-vectors, which
    include realizable polytopes with f2 up to 73.
If the fitted bound is violated out of sample, the baseline does not "recover the
results" -- it ASSERTS FALSE inequalities, which is precisely the unsoundness our
refutation channel exists to catch (arithmetic/bounded feasibility != realizability).
READ-ONLY.
"""
import json, os
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

def S_of(pv):   # high-order face count S = sum_{k>=7} p_k
    return sum(c for k, c in pv.items() if k >= 7)
def f2_of(pv):
    return sum(pv.values())
def p(pv, k):
    return pv.get(k, 0)

# ---- baseline input: realizable p-vectors from the cache (f2<=36) ----
cache = json.load(open(os.path.join(ROOT, "output/realizability_cache.json")))
def parse(key):
    return {int(a): int(b) for a, b in (t.split(":") for t in key.split(","))}
base = []
for key, v in cache.items():
    if v.get("verdict") == "realizable":
        pv = parse(key)
        if f2_of(pv) <= 36:
            base.append(pv)

# ---- out-of-sample: our witness-verified refutations (realizable, any f2) ----
lab = json.load(open(os.path.join(ROOT, "export/conjectures_labeled.json")))
wit = []
for e in lab:
    c = e.get("certificate") or {}
    if c.get("type") == "counterexample" and c.get("p_vector"):
        pv = {int(k): int(v) for k, v in c["p_vector"].items()}
        wit.append(pv)

print(f"baseline realizable set (f2<=36): {len(base)}  | f2 range "
      f"{min(f2_of(v) for v in base)}-{max(f2_of(v) for v in base)}")
print(f"out-of-sample witnesses:          {len(wit)} | f2 range "
      f"{min(f2_of(v) for v in wit)}-{max(f2_of(v) for v in wit)} "
      f"| with f2>36: {sum(1 for v in wit if f2_of(v)>36)}\n")

def analyze(cell_name, cell_pred):
    B = [v for v in base if cell_pred(v)]
    W = [v for v in wit if cell_pred(v)]
    if not B:
        print(f"[{cell_name}] no baseline points; skip"); return
    # per-S frontier the baseline observes
    bmin = defaultdict(lambda: 10**9); bmax = defaultdict(lambda: -10**9)
    for v in B:
        s = S_of(v); bmin[s] = min(bmin[s], p(v,6)); bmax[s] = max(bmax[s], p(v,6))
    base_p6_max = max(p(v,6) for v in B)
    base_f2_max = max(f2_of(v) for v in B)
    print(f"[{cell_name}]  baseline pts={len(B)} (f2<=36, max p6={base_p6_max}), "
          f"out-of-sample pts={len(W)}")
    # UPPER-bound unsoundness: witnesses whose p6 exceeds everything the baseline saw
    up = [v for v in W if p(v,6) > base_p6_max and f2_of(v) > base_f2_max]
    # per-S LOWER-bound unsoundness: witness p6 below baseline's observed min-at-that-S
    low = [v for v in W if S_of(v) in bmin and p(v,6) < bmin[S_of(v)]]
    print(f"    -> {len(up)} witnesses exceed the baseline's max observed p6 "
          f"({base_p6_max}); a fitted UPPER bound on p6 is false on them.")
    if up:
        ex = max(up, key=lambda v: p(v,6))
        print(f"       e.g. p-vec={dict(sorted(ex.items()))}  f2={f2_of(ex)} S={S_of(ex)} p6={p(ex,6)}")
    print(f"    -> {len(low)} witnesses fall BELOW the baseline's per-S min p6; "
          f"a fitted LOWER bound on p6 is false on them.")
    if low:
        ex = low[0]; s = S_of(ex)
        print(f"       e.g. p-vec={dict(sorted(ex.items()))}  f2={f2_of(ex)} S={s} "
              f"p6={p(ex,6)} < baseline min-p6-at-S={bmin[s]}")
    print()

analyze("ALL realizable", lambda v: True)
analyze("p4=p5=0 (Thm 2/3 cell)", lambda v: p(v,4)==0 and p(v,5)==0)
analyze("p4=0 (Thm 1 / OpenC3 cell)", lambda v: p(v,4)==0)
analyze("p3=0 (OpenC1 cell)", lambda v: p(v,3)==0)
