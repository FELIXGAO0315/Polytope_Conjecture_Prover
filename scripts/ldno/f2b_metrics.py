#!/usr/bin/env python3
"""F2b per-arm metrics (READ-ONLY over one isolated arm workspace), computed
against the pre-run baseline.json snapshot. Emits every primary + secondary
metric from prereg.json. Usage: f2b_metrics.py <arm_dir> <baseline.json> [out.json]
"""
import sys, os, json, glob, re
from collections import Counter

SRC_FAMILIES = [
    ("graffiti3_full",       lambda s: s == "graffiti3"),
    ("graffiti3_stratified", lambda s: s.startswith("graffiti3:strat:")),
    ("dynamic_cells",        lambda s: s.startswith("graffiti3:cell:")),
    ("mutation_engine",      lambda s: s.startswith("mutate:")),
    ("support_miner",        lambda s: s.startswith("miner:")),
    ("llm_coproposer",       lambda s: s == "llm"),
]
TIER = {  # found_by  ->  prereg tier label
    "witness_pool_replay": "witness_pool_replay",
    "plantri_pool_replay": "plantri_pool_replay",
    "pvector_walk":        "lattice_stage1",
    "plantri ce finder":   "plantri_screen",
}


def famname(src):
    for n, f in SRC_FAMILIES:
        if f(src):
            return n
    return "OTHER:" + str(src)


def hyp_cell(formula):
    m = re.search(r"if\s*\((.*)\)\s*,?\s*then", formula or "")
    inner = m.group(1) if m else ""
    atoms = sorted(a.strip() for a in re.split(r"\band\b", inner)
                   if a.strip() and "is_simple" not in a)
    return " & ".join(atoms) or "(simple only)"


def tier_of(found_by):
    fb = found_by or "unknown"
    for key, lab in TIER.items():
        if fb.startswith(key):
            return lab
    return "other:" + fb.split(" (")[0]


def main():
    arm_dir, baseline_path = sys.argv[1], sys.argv[2]
    out_path = sys.argv[3] if len(sys.argv) > 3 else None
    base = json.load(open(baseline_path))
    base_names = set(base["reg_names"]); base_cells = set(base["reg_cells"])
    base_ce = set(base["ce_dirs"]); base_runs = set(base["run_files"])

    reg = json.load(open(os.path.join(arm_dir, "conjectures/conjectures.json")))
    ents = [(b, e) for b in reg for e in reg[b]]
    new_ents = [(b, e) for b, e in ents if e["name"] not in base_names]

    # ---- accepted conjectures (both generations together) ----
    acc_cells = set(hyp_cell(e["formula"]) for _, e in new_ents)
    novel_cells = sorted(acc_cells - base_cells)
    all_acc_cells = sorted(acc_cells)

    # ---- candidates by source (new run logs only) ----
    new_runs = sorted(f for f in glob.glob(os.path.join(arm_dir, "output/conjecture_generator/run_*.json"))
                      if f not in base_runs)
    by_src = {n: {"proposed_eval": 0, "accepted": 0, "rejected": 0} for n, _ in SRC_FAMILIES}
    llm_review_drops = 0
    tot_proposed = tot_accepted = 0
    per_run = []
    for rf in new_runs:
        j = json.load(open(rf))
        a = Counter(); r = Counter()
        for x in j.get("accepted", []):
            fam = famname(x.get("source", "?"));  by_src.setdefault(fam, {"proposed_eval":0,"accepted":0,"rejected":0})
            by_src[fam]["accepted"] += 1; by_src[fam]["proposed_eval"] += 1; a[fam]+=1
        for x in j.get("rejected", []):
            fam = famname(x.get("source", "?")); by_src.setdefault(fam, {"proposed_eval":0,"accepted":0,"rejected":0})
            by_src[fam]["rejected"] += 1; by_src[fam]["proposed_eval"] += 1; r[fam]+=1
            if str(x.get("reason", "")).startswith("llm_review_drop"):
                llm_review_drops += 1
        na = len(j.get("accepted", [])); nr = len(j.get("rejected", []))
        tot_accepted += na; tot_proposed += na + nr
        per_run.append({"file": os.path.basename(rf), "accepted": na, "evaluated": na+nr})

    # ---- refutations by tier (new CE dirs) ----
    cur_ce = sorted(os.path.basename(x.rstrip("/"))
                    for x in glob.glob(os.path.join(arm_dir, "output/conjecture_with_ce/*/")))
    new_ce = [c for c in cur_ce if c not in base_ce]
    by_tier = Counter()
    for cid in new_ce:
        jf = os.path.join(arm_dir, f"output/conjecture_with_ce/{cid}/{cid}.json")
        if not os.path.exists(jf):
            cs = glob.glob(os.path.join(arm_dir, f"output/conjecture_with_ce/{cid}/*.json"))
            if not cs:
                continue
            jf = cs[0]
        fb = (json.load(open(jf)).get("found_by") or "unknown")
        by_tier[tier_of(fb)] += 1

    # ---- survivors + refuted (from registry statuses of new entries) ----
    survivors = [e["name"] for _, e in new_ents
                 if (e.get("status") in ("prover_failed", "failed"))
                 and isinstance(e.get("status_detail") or e.get("detail"), dict)
                 and ((e.get("status_detail") or e.get("detail") or {}).get("outcome") == "survivor_prover_disabled")]
    refuted = [e["name"] for _, e in new_ents if e.get("status") == "refuted"]
    n_acc = len(new_ents)
    refuted_frac = (len(refuted) / n_acc) if n_acc else 0.0

    # ---- check-level validator rejections (downstream CE verification) ----
    clog = os.path.join(arm_dir, "f2_out/checklog.jsonl")
    total_val = passes = 0; rej_by_check = Counter()
    if os.path.exists(clog):
        for line in open(clog):
            try:
                rr = json.loads(line)
            except Exception:
                continue
            total_val += 1
            if rr.get("all_passed"):
                passes += 1
            else:
                rej_by_check[rr.get("first_fail", 0)] += 1

    out = {
        "arm": os.path.basename(arm_dir.rstrip("/")),
        "accepted_conjectures": n_acc,
        "proposed_candidates_total": tot_proposed,
        "primary__novel_hypothesis_cells_vs_frozen": len(novel_cells),
        "novel_cells_list": novel_cells,
        "sec__distinct_hypothesis_cells_accepted": len(all_acc_cells),
        "sec__candidates_by_source": by_src,
        "sec__refuted_by_tier": dict(by_tier),
        "sec__refuted_count": len(refuted),
        "sec__refuted_fraction": round(refuted_frac, 4),
        "sec__survivors": len(survivors),
        "sec__llm_review_drops": llm_review_drops,
        "sec__validator_checklevel": {"total_validations": total_val, "passed": passes,
                                      "rejections_by_first_fail_check": dict(sorted(rej_by_check.items()))},
        "per_run": per_run,
        "n_new_ce_dirs": len(new_ce),
    }
    if out_path:
        json.dump(out, open(out_path, "w"), indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
