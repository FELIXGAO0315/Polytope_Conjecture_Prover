#!/usr/bin/env python3
"""Step 0(b)/(d) + Task 3b: reproduce headline counts, Table 3 provenance, write CSV.
READ-ONLY. No pipeline imports. Reads data files directly."""
import json, glob, os, csv, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OUT = os.path.join(ROOT, "supplement_experiment/ablation/out")
os.makedirs(OUT, exist_ok=True)

conj = json.load(open(os.path.join(ROOT, "conjectures/conjectures.json")))

def track_category(found_by):
    if found_by is None:
        return "UNKNOWN"
    if found_by.startswith("witness_pool_replay"):
        return "cross_conjecture_witness_replay"
    return {
        "plantri ce finder": "plantri_exhaustive_screen",
        "llm ce finder": "llm_constructor",
        "rl ce finder": "rl_policy",
        "pvector_walk": "eberhard_lattice_walk",
        "hopper ce finder": "hopper",
        "plantri_pool_replay": "plantri_pool_replay",
    }.get(found_by, "OTHER:" + found_by)

rows = []
for jf in sorted(glob.glob(os.path.join(ROOT, "output/conjecture_with_ce/*/*.json"))):
    cid = os.path.basename(jf)[:-5]
    d = json.load(open(jf))
    ce = d.get("counterexample") or {}
    pv = ce.get("p_vector")
    png = os.path.exists(jf.replace(".json", "_witness.png"))
    fb = d.get("found_by")
    replay_from = None
    if fb and fb.startswith("witness_pool_replay"):
        # pattern "witness_pool_replay (from C27)"
        replay_from = fb.split("from ", 1)[1].rstrip(")") if "from " in fb else None
    rows.append({
        "cid": cid,
        "found_by": fb,
        "track_category": track_category(fb),
        "is_replay": fb is not None and ("replay" in fb),
        "replay_from": replay_from or "",
        "qualifying_png": png,
        "has_witness_graph": bool(ce.get("witness_graph")),
        "f2": ce.get("f2"),
        "p_vector": json.dumps(pv),
        "found_at_round": d.get("found_at_round"),
        "n_other_candidates_not_checked": len(d.get("other_candidates_not_checked") or []),
    })

# write CSV
csvpath = os.path.join(OUT, "refutation_provenance.csv")
with open(csvpath, "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
    w.writeheader()
    w.writerows(rows)

qual = [r for r in rows if r["qualifying_png"]]
print(f"with_ce json files: {len(rows)} | qualifying (png present): {len(qual)}")

# Table 3 reproduction (qualifying only)
cat = collections.Counter(r["track_category"] for r in qual)
print("\n=== Table 3 reproduction (qualifying=204) ===")
order = ["plantri_exhaustive_screen","llm_constructor","rl_policy","eberhard_lattice_walk",
         "hopper","cross_conjecture_witness_replay","plantri_pool_replay"]
for k in order:
    print(f"  {k}: {cat.get(k,0)}")
print("  TOTAL:", sum(cat.values()))
orig = sum(cat.get(k,0) for k in order[:5])
reuse = sum(cat.get(k,0) for k in order[5:])
print(f"  original discovery = {orig}, reuse = {reuse}")

# non-qualifying
print("\n=== non-qualifying (no png) ===")
for r in rows:
    if not r["qualifying_png"]:
        print(f"  {r['cid']}: found_by={r['found_by']} has_wg={r['has_witness_graph']} pvec={r['p_vector']}")

# headline reconciliation vs registry buckets
print("\n=== registry bucket counts ===")
for b in ["unsolved","failed","proved"]:
    print(f"  {b}: {len(conj[b])}")

# cross-check: failed names vs with_ce dirs
failed_names = set(x["name"] for x in conj["failed"])
withce_dirs = set(os.path.basename(os.path.dirname(p)) for p in glob.glob(os.path.join(ROOT,"output/conjecture_with_ce/*/")))
print("\n=== failed-names vs with_ce-dirs ===")
print("  failed entries:", len(failed_names), "| with_ce dirs:", len(withce_dirs))
print("  in failed but no dir:", sorted(failed_names - withce_dirs))
print("  dir but not in failed:", sorted(withce_dirs - failed_names))
print(f"\nCSV written: {csvpath}")
