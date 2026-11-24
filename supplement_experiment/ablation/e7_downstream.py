#!/usr/bin/env python3
"""E7: campaign-level DOWNSTREAM refutation of the 14 feedback-UNIQUE conjectures
(cells only feedback reaches). Runs the real local CE search (plantri screen +
constructor + RL + Hopper), LLM stubbed (zero API), prover NOT run. CE writes are
sandboxed to a temp dir so the real witness pool is untouched. Checkpoints after
each conjecture. Answers: do feedback's extra conjectures actually resolve downstream?"""
if __name__ == "__main__":
    import os, sys, json, time, io, contextlib, pathlib
    ROOT="/home/felix_gao/Polytope_Conjecture_Prover"; os.chdir(ROOT); sys.path.insert(0,ROOT)
    import agent.orchestrator.orchestrator as O
    class _NoLLM:          # guarantee zero API
        def __init__(self, **k): pass
        def run(self): return None
    O.LLMCEFinder = _NoLLM
    from agent.orchestrator.orchestrator import Orchestrator
    from agent.orchestrator.tools.conjecture_parser import ParsedConjecture
    from types import SimpleNamespace

    SANDBOX = pathlib.Path("/tmp/claude-1000/-home-felix-gao-Polytope-Conjecture-Prover/9b1d48ec-d071-473f-9dad-ef162f74b3eb/scratchpad/ce_sandbox")
    SANDBOX.mkdir(parents=True, exist_ok=True)
    groups = json.load(open("supplement_experiment/ablation/out/e7_groups.json"))
    conjs = groups["feedback_unique"]            # 14
    RL_EP = int(os.environ.get("E7_RL_EP","200"))
    RESULT = "supplement_experiment/ablation/out/e7_downstream_feedback_unique.json"

    orch = Orchestrator()
    orch._ce_dir = SANDBOX                        # sandbox CE writes + replay reads
    out=[]
    print(f"E7 downstream: {len(conjs)} feedback-unique conjectures | RL={RL_EP}ep | LLM off | prover off", flush=True)
    for i,r in enumerate(conjs):
        pc = ParsedConjecture.from_conjecture_spec(SimpleNamespace(name=r["name"], formula=r["formula"]))
        t0=time.time(); buf=io.StringIO(); ce=None; err=""
        try:
            with contextlib.redirect_stdout(buf):
                ce = orch._run_ce_search(pc, rl_episodes=RL_EP, llm_rounds=0)
        except Exception as e:
            err=str(e)[:100]
        dt=time.time()-t0
        fb = ce.get("found_by") if isinstance(ce,dict) else None
        rec={"name":r["name"],"cell":r["cell"],"refuted":bool(ce),"found_by":fb,"sec":round(dt,1),"err":err}
        out.append(rec)
        tag = ("REFUTED by "+str(fb)) if ce else ("ERR "+err if err else "no-CE")
        print(f"[{i+1}/{len(conjs)}] {r['name']} {r['cell'][:46]:46s} -> {tag} ({dt:.0f}s)", flush=True)
        json.dump({"group":"feedback_unique","RL_EP":RL_EP,"results":out}, open(RESULT,"w"), indent=1)
    nref=sum(1 for x in out if x["refuted"])
    byt={}
    for x in out:
        if x["refuted"]:
            k=(x["found_by"] or "").split()[0]; byt[k]=byt.get(k,0)+1
    print(f"\n=== DOWNSTREAM RESULT: {nref}/{len(out)} feedback-unique conjectures refuted by local tracks (no LLM) ===", flush=True)
    print(f"=== by track: {byt} ===", flush=True)
