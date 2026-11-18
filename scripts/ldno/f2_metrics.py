#!/usr/bin/env python3
"""F2 metrics for one arm, computed against a pre-run baseline snapshot.
READ-ONLY over an isolated arm workspace (/home/felix_gao/ldno_exp/<arm>).
Usage: f2_metrics.py <arm_dir> <baseline.json> <out_checkpoint.json> <gen_label>
If baseline.json is missing, writes it (the pre-run frozen state) and exits."""
import sys, os, json, glob, re, csv
from collections import Counter

arm_dir, baseline_path, out_path, gen_label = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]

def hyp_cell(formula):
    m = re.search(r"if\s*\((.*)\)\s*,?\s*then", formula or "")
    inner = m.group(1) if m else ""
    atoms = sorted(a.strip() for a in re.split(r"\band\b", inner)
                   if a.strip() and "is_simple" not in a)
    return " & ".join(atoms) or "(simple only)"

def load_reg(arm):
    d = json.load(open(os.path.join(arm, "conjectures/conjectures.json")))
    return d

def reg_entries(d):
    return [(b, e) for b in d for e in d[b]]

# ---- baseline capture ----
if not os.path.exists(baseline_path):
    d = load_reg(arm_dir)
    ents = reg_entries(d)
    base = {"ce_dirs": sorted(os.path.basename(x.rstrip("/"))
                              for x in glob.glob(os.path.join(arm_dir, "output/conjecture_with_ce/*/"))),
            "reg_names": sorted(e["name"] for _, e in ents),
            "reg_cells": sorted(set(hyp_cell(e["formula"]) for _, e in ents)),
            "reg_formulas_by_cell": {},
            "run_files": sorted(glob.glob(os.path.join(arm_dir, "output/conjecture_generator/run_*.json")))}
    byc = {}
    for _, e in ents:
        byc.setdefault(hyp_cell(e["formula"]), []).append(e["formula"])
    base["reg_formulas_by_cell"] = byc
    json.dump(base, open(baseline_path, "w"), indent=1)
    print("baseline captured:", len(base["ce_dirs"]), "CE dirs,", len(base["reg_names"]), "reg entries,",
          len(base["reg_cells"]), "cells")
    sys.exit(0)

base = json.load(open(baseline_path))
base_ce = set(base["ce_dirs"]); base_names = set(base["reg_names"]); base_cells = set(base["reg_cells"])
base_byc = base["reg_formulas_by_cell"]

d = load_reg(arm_dir); ents = reg_entries(d)
# ---- new conjectures (accepted this run) ----
new_ents = [(b, e) for b, e in ents if e["name"] not in base_names]
# generator run files produced this run
new_runs = [f for f in glob.glob(os.path.join(arm_dir, "output/conjecture_generator/run_*.json"))
            if f not in set(base["run_files"])]
proposed = accepted = 0
run_detail = []
for rf in sorted(new_runs):
    rj = json.load(open(rf))
    a = len(rj.get("accepted", [])); r = len(rj.get("rejected", []))
    proposed += a + r; accepted += a
    run_detail.append({"file": os.path.basename(rf), "accepted": a, "rejected": r})

# ---- new hypothesis cells covered vs frozen registry ----
new_cells = sorted(set(hyp_cell(e["formula"]) for _, e in new_ents) - base_cells)

# ---- same-cell coefficient variants among accepted ----
def norm_nums(f):
    return re.sub(r"-?\d+\.?\d*", "#", f or "")
samecell_variant = 0
variant_examples = []
for _, e in new_ents:
    c = hyp_cell(e["formula"])
    # existing formulas in this cell (frozen + earlier-accepted)
    pool = list(base_byc.get(c, []))
    if any(norm_nums(e["formula"]) == norm_nums(pf) and e["formula"] != pf for pf in pool):
        samecell_variant += 1
        if len(variant_examples) < 8:
            variant_examples.append(e["name"])

# ---- validated refutations: new CE dirs vs baseline ----
cur_ce = sorted(os.path.basename(x.rstrip("/"))
                for x in glob.glob(os.path.join(arm_dir, "output/conjecture_with_ce/*/")))
new_ce = [c for c in cur_ce if c not in base_ce]
track = Counter(); replays = 0; first_finds = 0
for cid in new_ce:
    jf = os.path.join(arm_dir, f"output/conjecture_with_ce/{cid}/{cid}.json")
    if not os.path.exists(jf):
        cs = glob.glob(os.path.join(arm_dir, f"output/conjecture_with_ce/{cid}/*.json"))
        if not cs: continue
        jf = cs[0]
    fb = (json.load(open(jf)).get("found_by") or "unknown")
    if "replay" in fb:
        replays += 1; track["replay:" + fb.split(" (")[0]] += 1
    else:
        first_finds += 1; track[fb] += 1

# ---- survivors (prover disabled -> recorded as survivor) ----
survivors = 0; survivor_names = []
for b, e in new_ents:
    det = e.get("detail") or {}
    if (e.get("status") in ("prover_failed", "failed") and
            isinstance(det, dict) and det.get("outcome") == "survivor_prover_disabled"):
        survivors += 1; survivor_names.append(e["name"])
# fallback: count unsolved/failed new entries that are not refuted and not in new_ce
refuted_names = set()
for b, e in new_ents:
    if e.get("status") == "refuted":
        refuted_names.add(e["name"])

# ---- check-level validator rejections (from checklog) ----
clog = os.path.join(arm_dir, "f2_out/checklog.jsonl")
rej_by_check = Counter(); rej_by_track = Counter(); total_val = 0; passes = 0
check5_after_14 = 0
if os.path.exists(clog):
    for line in open(clog):
        try: r = json.loads(line)
        except Exception: continue
        total_val += 1
        if r.get("all_passed"): passes += 1
        else:
            ff = r.get("first_fail", 0)
            rej_by_check[ff] += 1
            rej_by_track[r.get("track", "unknown")] += 1
            if ff == 5: check5_after_14 += 1

out = {"arm": os.path.basename(arm_dir.rstrip("/")), "gen_label": gen_label,
       "generator": {"proposed_cumulative": proposed, "accepted_cumulative": accepted, "runs": run_detail},
       "new_hypothesis_cells_vs_frozen": {"count": len(new_cells), "cells": new_cells[:40]},
       "validated_refutations": {"total_new": len(new_ce), "first_finds": first_finds,
                                 "replays": replays, "by_track": dict(track)},
       "samecell_coeff_variants": {"count": samecell_variant, "of_accepted": len(new_ents),
                                   "examples": variant_examples},
       "survivors": {"count": survivors, "examples": survivor_names[:10]},
       "validator_checklevel": {"total_validations": total_val, "passed": passes,
                                "rejections_by_first_fail_check": dict(sorted(rej_by_check.items())),
                                "rejections_by_track": dict(rej_by_track),
                                "check5_rejected_candidate_passing_1to4": check5_after_14}}
json.dump(out, open(out_path, "w"), indent=1)
print(json.dumps(out, indent=1))
