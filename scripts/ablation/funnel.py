#!/usr/bin/env python3
"""Task 2 funnel (generator gate from 9 recorded runs + terminal funnel from
registry) and Task 3c outcome provenance. READ-ONLY."""
import json, glob, os, csv
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OUT = os.path.join(ROOT, "scripts/ablation/out")

# --- generator gate over the 9 recorded run files ---
runs = sorted(glob.glob(os.path.join(ROOT, "output/conjecture_generator/run_*.json")))
acc_src = Counter(); rej_reason = Counter(); rej_src = Counter()
per_run = []
name_source = {}   # conjecture name -> generator source (from accepted lists)
for rf in runs:
    d = json.load(open(rf))
    a = d.get("accepted", []); r = d.get("rejected", [])
    for x in a:
        acc_src[x.get("source","?")] += 1
        if x.get("name"): name_source[x["name"]] = x.get("source")
    for x in r:
        reason = (x.get("reason","?").split(":")[0])
        rej_reason[reason] += 1
        rej_src[x.get("source","?").split(":")[0]] += 1
    per_run.append({"run": d.get("run_timestamp"), "rows": d.get("dataset_rows"),
                    "accepted": len(a), "rejected": len(r)})

print(f"=== GENERATOR GATE — {len(runs)} recorded runs (2026-07-02..07-05) [PARTIAL: late campaign only] ===")
print("accepted by source:")
for k,v in acc_src.most_common(): print(f"   {k}: {v}")
print(f"   TOTAL accepted (recorded runs): {sum(acc_src.values())}")
print("rejected by reason (gate):")
for k,v in rej_reason.most_common(): print(f"   {k}: {v}")
print(f"   TOTAL rejected (recorded runs): {sum(rej_reason.values())}")
print("per-run:")
for pr in per_run: print(f"   {pr['run']}: rows={pr['rows']} accepted={pr['accepted']} rejected={pr['rejected']}")

with open(os.path.join(OUT,"generator_gate_recorded_runs.csv"),"w",newline="") as f:
    w=csv.writer(f); w.writerow(["run","dataset_rows","accepted","rejected"])
    for pr in per_run: w.writerow([pr["run"],pr["rows"],pr["accepted"],pr["rejected"]])

# --- terminal funnel from registry (COMPLETE) ---
conj = json.load(open(os.path.join(ROOT,"conjectures/conjectures.json")))
total = sum(len(conj[b]) for b in conj)
refuted = conj["failed"]; proved = conj["proved"]; unsolved = conj["unsolved"]
# witness-qualified refutations
qual = 0
for x in refuted:
    cid = x["name"]
    # map auto-name to C-id via trailing int? witness dirs are C{n}. Use registry trailing int.
# count qualifying by png presence over with_ce
pngs = sum(1 for jf in glob.glob(os.path.join(ROOT,"output/conjecture_with_ce/*/*.json"))
           if os.path.exists(jf.replace(".json","_witness.png")))
print(f"\n=== TERMINAL FUNNEL (registry, COMPLETE) ===")
print(f"  registered conjectures (reached >=Stage2): {total}")
print(f"  refuted at Stage 2: {len(refuted)}  (witness-qualified: {pngs})")
us = Counter(x["status"] for x in unsolved)
print(f"  survived CE search -> entailment/prover: {len(proved)+len(unsolved)}")
print(f"     not_entailed (entailment pre-check blocked prover): {us.get('not_entailed',0)}")
print(f"     prover_failed: {us.get('prover_failed',0)}")
print(f"     proved: {len(proved)}")

# --- Task 3c: provenance of the 7 named + aggregate ---
named = {"C104":"auto_20260627_163213_104","C124":"auto_20260701_090555_124",
         "C201":"C201","C215":"C215","C193":"C193","C195":"C195","C198":"C198"}
print(f"\n=== Task 3c: proposal source of proved/open (from recorded run accepted lists) ===")
for disp, nm in named.items():
    src = name_source.get(nm) or name_source.get(disp)
    print(f"   {disp} (reg {nm}): source={src if src else 'NOT IN recorded runs (created before 2026-07-02)'}")
# aggregate refuted sources where known
ref_src = Counter()
for x in refuted:
    s = name_source.get(x["name"])
    ref_src[s if s else "NOT_IN_RECORDED_RUNS"] += 1
print("\n   refuted conjectures by generator source (where recorded):")
for k,v in ref_src.most_common(): print(f"     {k}: {v}")
