#!/usr/bin/env python3
"""Task 3a/3b: plantri-reachability of every refutation witness.
READ-ONLY. Bounds in effect for the whole recorded dataset (all conjectures
created >= 2026-06-18, after the 2026-06-12 min-deg-5 f2<=36 dispatch):
  - min-deg-5 class (p3==0 and p4==0): plantri_mf -m5, f2 <= 36
  - otherwise (has a 3- or 4-face):     plantri_ad,     f2 <= 26
  - max face size k must satisfy k <= f2-1 for realizability
ce_enumerator caps that gate what the screen actually generates:
  n_large (sum of counts for k>=7) <= 2 ; max face k <= 20 ; f2 <= 36 (bumped by hyp)."""
import json, glob, os, csv
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OUT = os.path.join(ROOT, "supplement_experiment/ablation/out")
F2_M5, F2_AD, KMAX_ENUM, NLARGE_ENUM = 36, 26, 20, 2

recs = {}
for jf in glob.glob(os.path.join(ROOT, "output/conjecture_with_ce/*/*.json")):
    cid = os.path.basename(jf)[:-5]
    d = json.load(open(jf))
    ce = d.get("counterexample") or {}
    pv = ce.get("p_vector")
    png = os.path.exists(jf.replace(".json", "_witness.png"))
    recs[cid] = {"d": d, "pv": pv, "png": png, "found_by": d.get("found_by")}

def track_cat(fb):
    if fb is None: return "UNKNOWN"
    if fb.startswith("witness_pool_replay"): return "cross_conjecture_witness_replay"
    return {"plantri ce finder":"plantri","llm ce finder":"llm","rl ce finder":"rl",
            "pvector_walk":"eberhard_walk","hopper ce finder":"hopper",
            "plantri_pool_replay":"plantri_pool_replay"}.get(fb,"OTHER")

def orig_track(cid, seen=None):
    """Trace a replay chain to the original discovering track."""
    seen = seen or set()
    if cid in seen or cid not in recs: return None
    seen.add(cid)
    fb = recs[cid]["found_by"]
    if fb and fb.startswith("witness_pool_replay") and "from " in fb:
        src = fb.split("from ",1)[1].rstrip(")")
        return orig_track(src, seen)
    return track_cat(fb)

rows = []
for cid, r in recs.items():
    pv = r["pv"] or []
    pm = {i+3: c for i, c in enumerate(pv) if c}
    p3 = pm.get(3, 0); p4 = pm.get(4, 0)
    f2 = sum(pm.values())
    supp = [k for k in pm if pm[k] > 0]
    mink = min(supp) if supp else 0
    maxk = max(supp) if supp else 0
    nlarge = sum(c for k, c in pm.items() if k >= 7)  # = S
    mindeg5 = (p3 == 0 and p4 == 0)
    if mindeg5:
        reach = (f2 <= F2_M5) and (maxk <= f2 - 1)
        regime = "m5(f2<=36)"
    else:
        reach = (f2 <= F2_AD) and (maxk <= f2 - 1)
        regime = "ad(f2<=26)"
    within_caps = (nlarge <= NLARGE_ENUM) and (maxk <= KMAX_ENUM) and (f2 <= 36)
    fb = r["found_by"]
    rows.append({
        "cid": cid, "qualifying": r["png"], "found_by": fb,
        "track": track_cat(fb), "orig_track": orig_track(cid),
        "f2": f2, "p3": p3, "p4": p4, "min_deg": mink, "max_k": maxk, "S_nlarge": nlarge,
        "regime": regime, "plantri_reachable_final": reach,
        "within_enumerator_caps": within_caps,
        "pvec": json.dumps(pm, sort_keys=True),
    })

rows.sort(key=lambda x: (not x["qualifying"], x["track"], x["cid"]))
with open(os.path.join(OUT, "reachability.csv"), "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)

qual = [r for r in rows if r["qualifying"]]
print(f"qualifying refutations: {len(qual)}")

# 3b: reachability over all 204, split original vs replay
orig_rows = [r for r in qual if r["track"] not in ("cross_conjecture_witness_replay","plantri_pool_replay")]
replay_rows = [r for r in qual if r["track"] in ("cross_conjecture_witness_replay","plantri_pool_replay")]
print(f"\n=== 3b: plantri-reachable (final bounds) over 204 ===")
print(f"  reachable (by f2 regime): {sum(r['plantri_reachable_final'] for r in qual)}/{len(qual)}")
print(f"  within enumerator caps (S<=2,k<=20,f2<=36): {sum(r['within_enumerator_caps'] for r in qual)}/{len(qual)}")
print(f"  ORIGINAL (101): reachable {sum(r['plantri_reachable_final'] for r in orig_rows)}/{len(orig_rows)}; "
      f"within caps {sum(r['within_enumerator_caps'] for r in orig_rows)}/{len(orig_rows)}")
print(f"  REPLAY (103):   reachable {sum(r['plantri_reachable_final'] for r in replay_rows)}/{len(replay_rows)}; "
      f"within caps {sum(r['within_enumerator_caps'] for r in replay_rows)}/{len(replay_rows)}")

print("\n=== reachability by discovering track (original only) ===")
bt = defaultdict(lambda: [0,0,0])
for r in orig_rows:
    bt[r["track"]][0]+=1
    bt[r["track"]][1]+=r["plantri_reachable_final"]
    bt[r["track"]][2]+=r["within_enumerator_caps"]
for t,(n,re,ca) in sorted(bt.items()):
    print(f"  {t}: n={n} reachable={re} within_caps={ca}")

print("\n=== replay originals traced to first-discovering track ===")
ot = Counter(r["orig_track"] for r in replay_rows)
for t,n in ot.most_common(): print(f"  {t}: {n}")

# 3a focus: the stochastic 41 (llm/rl/hopper) — reachable & within caps but NOT found by plantri
print("\n=== 3a: stochastic (llm/rl/hopper) refutations reachable+within caps (plantri 'should' have enumerated) ===")
stoch = [r for r in orig_rows if r["track"] in ("llm","rl","hopper")]
print(f"  stochastic originals: {len(stoch)}")
flagged = [r for r in stoch if r["plantri_reachable_final"] and r["within_enumerator_caps"]]
print(f"  reachable_final AND within_caps: {len(flagged)}")
for r in flagged:
    print(f"    {r['cid']} track={r['track']} f2={r['f2']} p3={r['p3']} p4={r['p4']} S={r['S_nlarge']} maxk={r['max_k']} pvec={r['pvec']}")
notreach = [r for r in stoch if not (r["plantri_reachable_final"] and r["within_enumerator_caps"])]
print(f"  explained by bounds/caps (f2 or S or k out of screen range): {len(notreach)}")
for r in notreach[:50]:
    why=[]
    if not r["plantri_reachable_final"]: why.append(f"f2={r['f2']}>{'36' if (r['p3']==0 and r['p4']==0) else '26'}")
    if r["S_nlarge"]>NLARGE_ENUM: why.append(f"S={r['S_nlarge']}>2")
    if r["max_k"]>KMAX_ENUM: why.append(f"maxk={r['max_k']}>20")
    print(f"    {r['cid']} track={r['track']} f2={r['f2']} p3={r['p3']} p4={r['p4']} S={r['S_nlarge']} maxk={r['max_k']} -> {','.join(why)}")
print("\nwrote reachability.csv")
