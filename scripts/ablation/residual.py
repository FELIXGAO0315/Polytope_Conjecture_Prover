#!/usr/bin/env python3
"""Task 4d: enumerate residual S=1 arithmetic candidates for C193 (p3=0) and
C198 (p4=0), f2 in [17,30], p6 in {0,1}; cross-check realizability cache.
READ-ONLY arithmetic enumeration + cache lookup. No plantri invocation."""
import json, os
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
cache = json.load(open(os.path.join(ROOT, "output/realizability_cache.json")))

def key_of(pv):
    return ",".join(f"{k}:{pv[k]}" for k in sorted(pv) if pv[k] > 0)

def eberhard_ok(pv):
    return sum((6 - k) * c for k, c in pv.items()) == 12

def f2(pv):
    return sum(pv.values())

# C193: p3=0, f2>=17, conclusion p6>=4-2S, S=sum_{k>=7}. Residual S=1 -> p6<=1.
# one large face of size K>=7 (count 1). Free: p4,p5,p6 in {0,1}.
# Eberhard: 2 p4 + p5 + (6-K)*1 = 12  (p3=0, p6 coeff 0)  => 2p4+p5 = 6+K
def enum_residual(fixzero, F2MAX=30):
    cands = []
    for K in range(7, F2MAX + 2):
        need = 6 + K  # = 2p4+p5 when fixzero='p3';  = 3p3+p5 when fixzero='p4'
        for p6 in (0, 1):
            # iterate feasible (a,b) for the two low faces
            # fixzero p3: vars p4,p5 with 2p4+p5=need
            # fixzero p4: vars p3,p5 with 3p3+p5=need
            if fixzero == "p3":
                for p4 in range(0, need // 2 + 1):
                    p5 = need - 2 * p4
                    if p5 < 0: continue
                    pv = {4: p4, 5: p5, 6: p6, K: 1}
                    pv = {k: v for k, v in pv.items() if v > 0}
                    if not eberhard_ok(pv): continue
                    if f2(pv) < 17 or f2(pv) > F2MAX: continue
                    cands.append(pv)
            else:  # fixzero p4 -> p4=0
                for p3 in range(0, need // 3 + 1):
                    p5 = need - 3 * p3
                    if p5 < 0: continue
                    pv = {3: p3, 5: p5, 6: p6, K: 1}
                    pv = {k: v for k, v in pv.items() if v > 0}
                    if not eberhard_ok(pv): continue
                    if f2(pv) < 17 or f2(pv) > F2MAX: continue
                    cands.append(pv)
    return cands

for name, fz in [("C193 (p3=0)", "p3"), ("C198 (p4=0)", "p4")]:
    cands = enum_residual(fz)
    # dedupe
    seen = set(); uniq = []
    for pv in cands:
        k = key_of(pv)
        if k in seen: continue
        seen.add(k); uniq.append(pv)
    verd = Counter()
    incache = 0
    realizable_hits = []
    for pv in uniq:
        k = key_of(pv)
        if k in cache:
            incache += 1
            v = cache[k]["verdict"]
            verd[v] += 1
            if v == "realizable":
                realizable_hits.append(k)
        else:
            verd["NOT_IN_CACHE"] += 1
    print(f"\n=== {name}, S=1, p6<=1, 17<=f2<=30 ===")
    print(f"  arithmetic residual candidates (unique): {len(uniq)}")
    print(f"  in realizability cache: {incache}")
    print(f"  verdict breakdown: {dict(verd)}")
    print(f"  REALIZABLE among residual (would refute!): {realizable_hits if realizable_hits else 'none'}")
    # examples
    print("  examples:", [key_of(pv) for pv in uniq[:6]])
