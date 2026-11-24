#!/usr/bin/env python3
"""E8: two downstream runs, sequential, local tracks only (LLM stubbed, prover off,
CE writes sandboxed so the real pool is untouched).
 RUN 1  no-feedback baseline (27 conjectures)  -> complete the feedback A/B.
 RUN 2  leave-one-out: the 41 stochastic-first-found CEs re-searched WITHOUT LLM
        (replay sandboxed/empty) -> which LOCAL track recovers each; LLM's unique share."""
if __name__ == "__main__":
    import os, sys, json, time, io, contextlib, pathlib
    ROOT="/home/felix_gao/Polytope_Conjecture_Prover"; os.chdir(ROOT); sys.path.insert(0,ROOT)
    import agent.orchestrator.orchestrator as O
    class _NoLLM:
        def __init__(self, **k): pass
        def run(self): return None
    O.LLMCEFinder = _NoLLM
    from agent.orchestrator.orchestrator import Orchestrator
    from agent.orchestrator.tools.conjecture_parser import ParsedConjecture
    from types import SimpleNamespace
    from collections import Counter

    SANDBOX=pathlib.Path("/tmp/claude-1000/-home-felix-gao-Polytope-Conjecture-Prover/9b1d48ec-d071-473f-9dad-ef162f74b3eb/scratchpad/ce_sandbox2")
    SANDBOX.mkdir(parents=True, exist_ok=True)
    RL_EP=int(os.environ.get("E8_RL_EP","200"))
    orch=Orchestrator(); orch._ce_dir=SANDBOX

    def run_group(gname, items, outfile):
        res=[]; print(f"\n##### {gname}: {len(items)} conjectures | RL={RL_EP}ep | LLM off #####", flush=True)
        for i,it in enumerate(items):
            pc=it["pc"]; t0=time.time(); ce=None; err=""
            try:
                with contextlib.redirect_stdout(io.StringIO()):
                    ce=orch._run_ce_search(pc, rl_episodes=RL_EP, llm_rounds=0)
            except Exception as e: err=str(e)[:100]
            dt=time.time()-t0
            fb=(ce.get("found_by") if isinstance(ce,dict) else None)
            track=(fb or "").split(" ce")[0].split(" (")[0].strip() if fb else None
            rec={"name":it["name"],"refuted":bool(ce),"found_by":fb,"track":track,"sec":round(dt,1),"err":err}
            if "orig_track" in it: rec["orig_track"]=it["orig_track"]
            res.append(rec)
            json.dump({"group":gname,"RL_EP":RL_EP,"results":res}, open(outfile,"w"), indent=1)
            tag=("REF:"+str(track)) if ce else ("ERR:"+err if err else "no-CE")
            extra=f" [orig={it.get('orig_track','')}]" if "orig_track" in it else ""
            print(f"[{gname[:4]} {i+1}/{len(items)}] {it['name']:6s}{extra} -> {tag} ({dt:.0f}s)", flush=True)
        nref=sum(1 for x in res if x["refuted"])
        print(f"=== {gname}: {nref}/{len(res)} refuted ===", flush=True)
        return res

    # ---- RUN 1: no-feedback baseline (formula-based) ----
    g=json.load(open("scripts/ablation/out/e7_groups.json"))
    nf=[]
    for r in g["nofeedback"]:
        try: pc=ParsedConjecture.from_conjecture_spec(SimpleNamespace(name=r["name"],formula=r["formula"]))
        except Exception: continue
        nf.append({"name":r["name"],"pc":pc})
    r1=run_group("nofeedback_baseline", nf, "scripts/ablation/out/e8_nofeedback_downstream.json")

    # ---- RUN 2: leave-one-out on 41 stochastic CEs (hyp+concl direct) ----
    st=json.load(open("scripts/ablation/out/e8_stochastic41.json"))
    lo=[{"name":x["name"],"orig_track":x["orig_track"],
         "pc":ParsedConjecture(conjecture_id=x["name"],statement_latex="",hypotheses=x["hypotheses"],conclusion=x["conclusion"])}
        for x in st]
    r2=run_group("stochastic41_leaveoneout", lo, "scripts/ablation/out/e8_leaveoneout.json")

    # ---- leave-one-out summary: of each orig track's CEs, how many recovered by a LOCAL track w/o LLM ----
    print("\n===== LEAVE-ONE-OUT SUMMARY (no-LLM recovery of stochastic CEs) =====", flush=True)
    for ot in ("llm_constructor","rl_policy","hopper"):
        grp=[x for x in r2 if x.get("orig_track")==ot]
        rec=sum(1 for x in grp if x["refuted"])
        by=Counter(x["track"] for x in grp if x["refuted"])
        print(f"  orig={ot}: {rec}/{len(grp)} recovered without LLM  by {dict(by)}", flush=True)
