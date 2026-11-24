#!/usr/bin/env python3
"""Task 4c/4d: pure 2-face families {p3,p6},{p4,p6},{p5,p6} realizability;
residual cases for C195/C193/C198. READ-ONLY. Reads cache + witness pool."""
import json, glob, os, csv
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OUT = os.path.join(ROOT, "supplement_experiment/ablation/out")

cache = json.load(open(os.path.join(ROOT, "output/realizability_cache.json")))

def parse_key(k):
    d = {}
    for part in k.split(","):
        a, b = part.split(":")
        d[int(a)] = int(b)
    return d

# index cache by frozenset(support) and by exact dict
cache_parsed = {}
for k, v in cache.items():
    pv = parse_key(k)
    cache_parsed[k] = (pv, v.get("verdict"))

# witness pool p-vectors (realizable by construction) -> support
wit = []
for jf in glob.glob(os.path.join(ROOT, "output/conjecture_with_ce/*/*.json")):
    d = json.load(open(jf))
    ce = (d.get("counterexample") or {})
    pv = ce.get("p_vector")
    if not pv:
        continue
    # p_vector is a list indexed from 3 (p3,p4,p5,p6,p7,...)
    dd = {i + 3: c for i, c in enumerate(pv) if c}
    wit.append((os.path.basename(jf)[:-5], dd))

def support_set(pv):
    return frozenset(k for k, c in pv.items() if c > 0)

# Families: support exactly subset of {a,6} with a in {3,4,5}; includes degenerate {a}
def family(a):
    rows = []
    allowed = {a, 6}
    # from cache
    for k, (pv, verd) in cache_parsed.items():
        supp = support_set(pv)
        if supp and supp <= allowed:
            rows.append((pv.get(a, 0), pv.get(6, 0), verd, "cache", k))
    # from witnesses
    for cid, pv in wit:
        supp = support_set(pv)
        if supp and supp <= allowed:
            rows.append((pv.get(a, 0), pv.get(6, 0), "realizable(witness)", "witness:" + cid, ""))
    return rows

print("=== Eberhard forces the free coeff: {p3,p6}->p3=4 ; {p4,p6}->p4=6 ; {p5,p6}->p5=12 ===")
summary = {}
for a, fixed in [(3, 4), (4, 6), (5, 12)]:
    rows = family(a)
    byp6 = defaultdict(set)
    for va, p6, verd, src, k in rows:
        byp6[p6].add(verd.split("(")[0])
    print(f"\n--- family {{p{a},p6}} (expect p{a}={fixed}); {len(rows)} cache/witness hits ---")
    for p6 in sorted(byp6):
        print(f"   p6={p6}: verdicts={sorted(byp6[p6])}")
    summary[f"p{a}_p6"] = {str(p6): sorted(byp6[p6]) for p6 in sorted(byp6)}

# C195 residual: {4:6, 6:1}
print("\n=== C195 residual {p4:6, p6:1} ===")
for k, (pv, verd) in cache_parsed.items():
    if pv == {4: 6, 6: 1}:
        print(f"   cache key {k!r}: verdict={verd}  full={cache[k]}")

# also check neighbors {4:6} and {4:6,6:2}
for target in [{4:6}, {4:6,6:1}, {4:6,6:2}, {4:6,6:3}]:
    hit = [(k,verd) for k,(pv,verd) in cache_parsed.items() if pv==target]
    print(f"   {target}: {hit if hit else 'NOT IN CACHE'}")

json.dump(summary, open(os.path.join(OUT, "families.json"), "w"), indent=1)

# write per-member CSV
with open(os.path.join(OUT, "families.csv"), "w", newline="") as f:
    w = csv.writer(f)
    w.writerow(["family", "p_a", "p6", "verdict", "source", "cache_key"])
    for a in (3, 4, 5):
        for va, p6, verd, src, k in sorted(family(a)):
            w.writerow([f"p{a}_p6", va, p6, verd, src, k])
print("\nwrote families.json, families.csv")
