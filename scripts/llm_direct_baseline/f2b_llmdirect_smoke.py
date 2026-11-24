#!/usr/bin/env python3
"""F2b-llm_direct SMOKE CHECK (step 4b). ONE standalone propose call at the cap,
only to confirm the response is not truncated at the candidate cap with
max_tokens=32000 (CLAUDE_CODE_MAX_OUTPUT_TOKENS) and timeout=600s.

Runs the real patched generation path in dry_run mode (nothing is registered, no
downstream, no metric is computed from the output) on a FRESH patched copy in a
temp dir OUTSIDE every experiment workspace. Prints the propose instrumentation
record and the elapsed time.

Exit codes: 0 = response parsed in full (no truncation) within 600s;
            2 = truncation / infra failure (RuntimeError from patched _llm_propose);
            4 = completed but call exceeded 600s (raise the timeout once per protocol).

Usage: python3 f2b_llmdirect_smoke.py [--n 128]
"""
import os, sys, time, json, argparse

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from f2b_llmdirect_setup import prepare_arm  # noqa: E402

SMOKE_ARM = "/home/felix_gao/llm_direct_exp/f2b_llmdirect_smoke/arm"      # outside seed workspaces
INVALID_LOG = "/home/felix_gao/llm_direct_exp/f2b_llmdirect_smoke/llm_invalid.jsonl"
PROMPT_LOG = "/home/felix_gao/llm_direct_exp/f2b_llmdirect_smoke/propose_prompt.txt"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=128,
                    help="propose cap to smoke-test (default 128 = the largest per-gen cap)")
    args = ap.parse_args()

    print(f"[smoke] preparing fresh patched arm at {SMOKE_ARM} …", flush=True)
    prepare_arm(SMOKE_ARM)
    for p in (INVALID_LOG, PROMPT_LOG):
        if os.path.exists(p):
            os.remove(p)

    # Budget plumb exactly as the real run: max_tokens via CLAUDE_CODE_MAX_OUTPUT_TOKENS
    # (forwarded by _query_once through os.environ); timeout 600 is in the patch.
    os.environ["CLAUDE_CODE_MAX_OUTPUT_TOKENS"] = "32000"
    os.environ["F2_LLM_INVALID_LOG"] = INVALID_LOG
    os.environ["F2_PROMPT_LOG"] = PROMPT_LOG
    # thread hygiene (match run env)
    for k in ("OMP_NUM_THREADS", "MKL_NUM_THREADS", "OPENBLAS_NUM_THREADS"):
        os.environ.setdefault(k, "1")

    os.chdir(SMOKE_ARM)
    sys.path.insert(0, SMOKE_ARM)
    from agent.conjecture_generator import ConjectureGenerator
    from agent.orchestrator.orchestrator import Orchestrator

    orch = Orchestrator()
    gen = ConjectureGenerator(
        client=orch.client,
        limit=0,
        g3_mode="fast",
        llm_propose_n=args.n,                    # cap under test
        propose_model=orch.config.model_fast,
        review_model=orch.config.model_main,
        dry_run=True,                            # register nothing; no downstream
    )
    print(f"[smoke] running dry generation, llm_propose_n={args.n}, "
          f"max_tokens=32000, timeout=600 …", flush=True)
    t0 = time.time()
    status = 0
    try:
        gen.run()
    except RuntimeError as exc:
        print(f"[smoke] PROPOSE RAISED (truncation/infra): {exc}", flush=True)
        status = 2
    elapsed = time.time() - t0
    print(f"[smoke] elapsed={elapsed:.1f}s", flush=True)

    rec = None
    if os.path.exists(INVALID_LOG):
        lines = [l for l in open(INVALID_LOG) if l.strip()]
        if lines:
            rec = json.loads(lines[-1])
    print(f"[smoke] propose record: {json.dumps(rec, indent=1) if rec else 'NONE'}",
          flush=True)

    if status == 0 and rec and rec.get("status") == "ok":
        print(f"[smoke] OK — response parsed in full: n_returned={rec.get('n_returned')}, "
              f"n_valid={rec.get('n_valid')}, n_invalid={rec.get('n_invalid')}, "
              f"hints_empty={rec.get('hints_empty')}", flush=True)
        if elapsed > 600:
            print("[smoke] WARNING call exceeded 600s — raise timeout once per protocol",
                  flush=True)
            status = 4
    elif status == 0:
        print("[smoke] UNEXPECTED — no ok record found", flush=True)
        status = 2
    sys.exit(status)


if __name__ == "__main__":
    main()
