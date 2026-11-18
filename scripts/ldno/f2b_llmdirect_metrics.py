#!/usr/bin/env python3
"""F2b-llm_direct metrics + comparison table (READ-ONLY).

For each seed whose llm_direct arm completed ('ARM COMPLETE' in driver.log):
  * run f2b_metrics.py (identical to F2b) against the arm's baseline.json to get
    novel hypothesis cells, distinct accepted cells, accepted, refuted, survivors,
    candidates-by-source, LLM-review drops, proposed-candidates total.
  * read the propose instrumentation log (f2_out/llm_invalid.jsonl) for invalid
    LLM outputs, per-gen shortfall, hint-emptiness, and the per-gen cap actually
    requested.
  * read the arm wall time from driver.log.

Then emit the per-seed comparison table (closed / open from the committed F2b
results at 314ed95 — NOT rerun — vs llm_direct), the means, the pre-registered
decision rule (closed beats llm_direct iff it has more novel cells in >= 3 of 5
seeds), and the self-checks (Graffiti3 + support miner produced zero candidates;
no hint block was non-empty; the cap matched the closed arm per seed+gen).

Usage: f2b_llmdirect_metrics.py <out_results.json>
"""
import sys, os, json, glob, subprocess, statistics

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = "/home/felix_gao/ldno_exp/f2b_llmdirect"
CAPS = json.load(open(os.path.join(HERE, "f2b_caps.json")))["caps"]
F2B = json.load(open(os.path.join(HERE, "out/f2b_results_314ed95.json")))
SEEDS = [41, 7, 123, 2024, 99]


def completed(arm_dir):
    try:
        return "ARM COMPLETE" in open(os.path.join(arm_dir, "f2_out/driver.log")).read()
    except Exception:
        return False


def wall_s(arm_dir):
    try:
        for line in open(os.path.join(arm_dir, "f2_out/driver.log")):
            if "ARM COMPLETE" in line and "total_wall=" in line:
                return float(line.split("total_wall=")[1].split("s")[0])
    except Exception:
        pass
    return None


def metrics(arm_dir):
    base = os.path.join(arm_dir, "f2_out/baseline.json")
    r = subprocess.run([sys.executable, os.path.join(HERE, "f2b_metrics.py"), arm_dir, base],
                       capture_output=True, text=True)
    return json.loads(r.stdout)


def propose_log(arm_dir):
    """Per-generation propose records (status ok), in order."""
    p = os.path.join(arm_dir, "f2_out/llm_invalid.jsonl")
    recs = []
    if os.path.exists(p):
        for line in open(p):
            line = line.strip()
            if line:
                recs.append(json.loads(line))
    return recs


def ms(xs):
    xs = [x for x in xs if x is not None]
    if not xs:
        return {"mean": None, "sd": None, "n": 0}
    return {"mean": round(statistics.mean(xs), 4),
            "sd": round(statistics.pstdev(xs), 4) if len(xs) > 1 else 0.0, "n": len(xs)}


def main():
    out_path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "out/llm_direct/results.json")
    per_seed = {}
    for s in SEEDS:
        arm = f"{ROOT}/seed{s}/llm_direct"
        done = completed(arm)
        entry = {"completed": done}
        if done and os.path.exists(f"{arm}/f2_out/baseline.json"):
            m = metrics(arm)
            recs = propose_log(arm)
            ok = [r for r in recs if r.get("status") == "ok"]
            infra = [r for r in recs if r.get("status") != "ok"]
            # per-gen propose summary (ok records in order == gen1, gen2)
            per_gen = []
            for g, r in enumerate(ok, start=1):
                per_gen.append({"gen": g, "cap_requested": r.get("n_requested"),
                                "n_returned": r.get("n_returned"), "n_valid": r.get("n_valid"),
                                "n_invalid": r.get("n_invalid"), "shortfall": r.get("shortfall"),
                                "hints_empty": r.get("hints_empty")})
            entry.update({
                "wall_s": wall_s(arm),
                "novel_cells": m["primary__novel_hypothesis_cells_vs_frozen"],
                "distinct_accepted_cells": m["sec__distinct_hypothesis_cells_accepted"],
                "accepted": m["accepted_conjectures"],
                "refuted": m["sec__refuted_count"],
                "survivors": m["sec__survivors"],
                "candidates_evaluated": m["proposed_candidates_total"],
                "llm_review_drops": m["sec__llm_review_drops"],
                "by_source": m["sec__candidates_by_source"],
                "refuted_by_tier": m["sec__refuted_by_tier"],
                "novel_cells_list": m["novel_cells_list"],
                "invalid_llm_outputs": sum(int(r.get("n_invalid") or 0) for r in ok),
                "shortfall_total": sum(int(r.get("shortfall") or 0) for r in ok),
                "propose_per_gen": per_gen,
                "infra_failures_in_this_run": len(infra),
            })
            # ---- self-checks ----
            g3f = (m["sec__candidates_by_source"].get("graffiti3_full", {}) or {}).get("proposed_eval", 0)
            g3s = (m["sec__candidates_by_source"].get("graffiti3_stratified", {}) or {}).get("proposed_eval", 0)
            cells = (m["sec__candidates_by_source"].get("dynamic_cells", {}) or {}).get("proposed_eval", 0)
            muta = (m["sec__candidates_by_source"].get("mutation_engine", {}) or {}).get("proposed_eval", 0)
            miner = (m["sec__candidates_by_source"].get("support_miner", {}) or {}).get("proposed_eval", 0)
            llm = (m["sec__candidates_by_source"].get("llm_coproposer", {}) or {}).get("proposed_eval", 0)
            cap_ok = all(pg["cap_requested"] == int(CAPS[str(s)][str(pg["gen"])]) for pg in per_gen)
            entry["self_checks"] = {
                "graffiti3_full_candidates": g3f, "graffiti3_stratified_candidates": g3s,
                "dynamic_cells_candidates": cells, "mutation_engine_candidates": muta,
                "support_miner_candidates": miner, "llm_candidates": llm,
                "nonllm_sources_all_zero": (g3f == g3s == cells == muta == miner == 0),
                "all_hints_empty": all(pg["hints_empty"] for pg in per_gen) and len(per_gen) > 0,
                "cap_matched_closed_per_gen": cap_ok,
                "cap_expected": {str(g): int(CAPS[str(s)][str(g)]) for g in (1, 2)},
            }
        per_seed[s] = entry

    def closed(s, key):
        return F2B["per_seed_metrics"][str(s)]["closed"][key]

    def openv(s, key):
        return F2B["per_seed_metrics"][str(s)]["open"][key]

    KEYMAP = {  # table column -> (committed-results key)
        "novel_cells": "primary__novel_hypothesis_cells_vs_frozen",
        "distinct_accepted_cells": "sec__distinct_hypothesis_cells_accepted",
        "accepted": "accepted_conjectures",
        "refuted": "sec__refuted_count",
        "candidates_evaluated": "proposed_candidates_total",
    }

    table = []
    agg_seeds = [s for s in SEEDS if per_seed[s].get("completed")]
    for s in SEEDS:
        row = {"seed": s}
        for arm, getter in (("closed", closed), ("open", openv)):
            row[arm] = {col: getter(s, k) for col, k in KEYMAP.items()}
            row[arm]["invalid_llm_outputs"] = None   # n/a for mixed-source arms
            row[arm]["wall_s"] = None
        ld = per_seed[s]
        if ld.get("completed"):
            row["llm_direct"] = {col: ld[col] for col in KEYMAP}
            row["llm_direct"]["invalid_llm_outputs"] = ld["invalid_llm_outputs"]
            row["llm_direct"]["wall_s"] = ld["wall_s"]
        else:
            row["llm_direct"] = {"incomplete": True}
        table.append(row)

    # ---- decision rule: closed beats llm_direct iff more novel cells in >=3 of 5 ----
    decided = [s for s in SEEDS if per_seed[s].get("completed")]
    signs = {"closed>llm_direct": 0, "closed=llm_direct": 0, "closed<llm_direct": 0}
    per_seed_novel = {}
    for s in decided:
        c = closed(s, "primary__novel_hypothesis_cells_vs_frozen")
        l = per_seed[s]["novel_cells"]
        per_seed_novel[s] = {"closed": c, "llm_direct": l, "diff_closed_minus_ld": c - l}
        if c > l:
            signs["closed>llm_direct"] += 1
        elif c == l:
            signs["closed=llm_direct"] += 1
        else:
            signs["closed<llm_direct"] += 1
    rule = {"n_seeds_completed": len(decided),
            "rule": "closed beats llm_direct iff novel cells(closed) > novel cells(llm_direct) in >= 3 of 5 seeds",
            "closed_wins": signs["closed>llm_direct"],
            "closed_beats_llm_direct": (signs["closed>llm_direct"] >= 3),
            "sign_count": signs, "per_seed_novel": per_seed_novel}

    means = {}
    for col, k in KEYMAP.items():
        means[col] = {
            "closed": ms([closed(s, k) for s in agg_seeds]),
            "open": ms([openv(s, k) for s in agg_seeds]),
            "llm_direct": ms([per_seed[s][col] for s in agg_seeds]),
        }
    means["invalid_llm_outputs"] = {"llm_direct": ms([per_seed[s]["invalid_llm_outputs"] for s in agg_seeds])}
    means["wall_s"] = {"llm_direct": ms([per_seed[s]["wall_s"] for s in agg_seeds])}

    out = {"seeds": SEEDS, "seeds_completed": agg_seeds,
           "comparison_source_commit": "314ed95 (F2b results; closed/open NOT rerun)",
           "metric_defs_and_baseline": "2999a6c (F2b prereg)",
           "per_seed_llm_direct": per_seed, "table": table, "means": means,
           "decision_rule": rule}
    json.dump(out, open(out_path, "w"), indent=1)

    # ---- human-readable print ----
    print(f"wrote {out_path}")
    print(f"seeds completed: {agg_seeds}")
    hdr = f"{'seed':>5} {'arm':>10} {'novel':>6} {'distAcc':>8} {'accept':>7} {'refut':>6} {'invLLM':>7} {'candEval':>9} {'wall_s':>8}"
    print(hdr)
    for row in table:
        for arm in ("closed", "open", "llm_direct"):
            a = row[arm]
            if a.get("incomplete"):
                print(f"{row['seed']:>5} {arm:>10}  INCOMPLETE")
                continue
            print(f"{row['seed']:>5} {arm:>10} {a['novel_cells']:>6} {a['distinct_accepted_cells']:>8} "
                  f"{a['accepted']:>7} {a['refuted']:>6} {str(a['invalid_llm_outputs']):>7} "
                  f"{a['candidates_evaluated']:>9} {str(round(a['wall_s'],1) if a['wall_s'] else '-'):>8}")
    print("\nDECISION RULE:", json.dumps(rule, indent=1))
    print("\nSELF-CHECKS per seed:")
    for s in agg_seeds:
        print(f"  seed {s}: {json.dumps(per_seed[s]['self_checks'])}")


if __name__ == "__main__":
    main()
