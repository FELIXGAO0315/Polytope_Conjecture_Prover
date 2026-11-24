#!/usr/bin/env python3
"""E7 demo: campaign-level downstream refutation via witness-pool REPLAY only
(fully local, no LLM/RL). Replays the pre-existing C1..C216 witness pool against
each arm's generated conjectures (C217+), so the pool PREDATES them (non-circular).
Measures: how many conjectures each arm (feedback ON vs OFF) yields that a prior
witness already refutes -> a real downstream-outcome signal for the closed loop."""
import os, sys, json, time, io, contextlib
from types import SimpleNamespace
ROOT="/home/felix_gao/Polytope_Conjecture_Prover"; os.chdir(ROOT); sys.path.insert(0,ROOT)
import networkx as nx
from agent.orchestrator.tools.conjecture_parser import ParsedConjecture
from agent.orchestrator.tools.check_pvector import PVectorCheckAgent
from agent.orchestrator.tools.pvec_eval import _eval_conclusion_violated

# ---- load pre-existing witness pool (C1..C216): p_vec + witness graph ----
from pathlib import Path
pool=[]
for jf in sorted(Path("output/conjecture_with_ce").glob("*/*.json")):
    try: data=json.loads(jf.read_text())
    except Exception: continue
    ce=data.get("counterexample") or {}
    edges=(ce.get("witness_graph") or {}).get("edges") or []
    pvec={int(k[1:]):v for k,v in ce.items() if k.startswith("p") and k[1:].isdigit() and isinstance(v,int) and v>0}
    if edges and pvec:
        try: G=nx.Graph((int(u),int(v)) for u,v in edges)
        except Exception: continue
        pool.append((jf.parent.name, pvec, G))
print(f"pool witnesses loaded: {len(pool)}  (sources C1..C216)")

checker=PVectorCheckAgent()
def replay_refute(pc):
    """Return source name of first pool witness that refutes pc, else None."""
    for src,pvec,G in pool:
        # cheap arithmetic pre-filter: must violate the conclusion
        viol,_=_eval_conclusion_violated(pc.conclusion, pvec)
        if not viol: continue
        rep=checker.run_silent(pvec, pc, constructor_timeout=2.0, witness_graph=G)
        if rep.all_passed:
            return src
    return None

d=json.load(open("scripts/ablation/out/e4_feedback_ablation.json"))
def run_arm(name, rows):
    seen=set(); refuted=0; details=[]; t0=time.time()
    for r in rows:
        key=r["formula"]
        if key in seen: continue
        seen.add(key)
        try: pc=ParsedConjecture.from_conjecture_spec(SimpleNamespace(name=r["name"],formula=r["formula"]))
        except Exception: continue
        src=replay_refute(pc)
        if src: refuted+=1; details.append((r["name"],r["cell"],src))
    dt=time.time()-t0
    print(f"\n[{name}] distinct conjectures={len(seen)}  REFUTED-by-prior-pool={refuted}  ({dt:.1f}s)")
    for nm,cell,src in details[:12]:
        print(f"    {nm:6s} {cell:34s}  <- witness from {src}")
    return len(seen), refuted

print("\n"+"="*70+"\nARM A = feedback ON   |   ARM B = feedback OFF\n"+"="*70)
nA,rA=run_arm("ARM A feedback ON",  d["armA"])
nB,rB=run_arm("ARM B feedback OFF", d["armB"])
print("\n"+"="*70)
print(f"RESULT  A(feedback): {rA}/{nA} refuted by prior pool   |   B(no-feedback): {rB}/{nB}")
print(f"        feedback's downstream delta: +{rA-rB} refutations, +{nA-nB} conjectures")
json.dump({"armA":{"n":nA,"refuted":rA},"armB":{"n":nB,"refuted":rB}},
          open("scripts/ablation/out/e7_campaign_replay_demo.json","w"),indent=1)
