#!/usr/bin/env python3
"""F2b-llm_direct: build an isolated arm workspace from the a1eab93 snapshot and
apply the open-arm F2b patches VERBATIM plus the llm_direct-only changes.

The llm_direct arm = the F2b OPEN arm with every non-LLM Stage-1 source turned
off, so the LLM co-proposer is the only conjecture source. Everything else
(syntax/entailment/shape-repeat gates, LP-overfit/trivial/semantic-dup filters,
advisory LLM review, deterministic downstream B, prover disabled, 2 generations,
no outcome feedback between generations) is byte-for-byte the open arm.

Patches applied (in order), all on a FRESH copy of /tmp/ldno_snap_a1eab93
(verified byte-identical to commit a1eab93):

  1. patch_validator  — check-level logging in check_pvector.py (additive; VERBATIM
                        from the original F2b f2b_setup.py).
  2. patch_prover     — prover DISABLED in evolution_loop.py (VERBATIM from F2b).
  3. patch_openloop   — signals/dynamic-cells/mutations withheld (VERBATIM from F2b
                        open arm; empties the propose/review hint blocks).
  4. patch_llmdirect_sources — Graffiti3 full + Graffiti3 stratified + support miner
                        turned OFF (dynamic cells + mutation engine are already off
                        from patch_openloop). LLM co-proposer is the only source.
  5. patch_llmdirect_budget  — propose call timeout 60s -> 600s (max_attempts stays
                        1; max_tokens is set out-of-band via CLAUDE_CODE_MAX_OUTPUT_TOKENS
                        which _query_once already forwards through os.environ).
  6. patch_llmdirect_logging — additive instrumentation in _llm_propose: records
                        n_requested / n_valid / n_invalid / shortfall / hint-emptiness
                        to F2_LLM_INVALID_LOG and the full prompt to F2_PROMPT_LOG;
                        an API error / rate-limit / timeout / empty-or-truncated
                        response RAISES (treated as a crash -> rerun the seed), while
                        a valid response with fewer than the cap is recorded as
                        shortfall (NOT a crash). Model/effort/prompt are unchanged.

Writes NOTHING into the repo/main tree and never touches the F2b closed/open
workspaces. Usage:
  python3 f2b_llmdirect_setup.py <seed_int>     # -> /home/felix_gao/ldno_exp/f2b_llmdirect/seed<seed>/llm_direct
  (library)  prepare_arm(dest)                  # used by the smoke check on a temp dir
"""
import os, shutil, subprocess, sys

SNAP = "/tmp/ldno_snap_a1eab93"
ROOT = "/home/felix_gao/ldno_exp/f2b_llmdirect"

# ── 1. validator check-level logging (VERBATIM from original f2b_setup.py) ──
LOG_HELPER = '''

# ── [F2 check-level logging] additive; reads already-computed results only ──
import os as _f2_os, json as _f2_json
def _f2_check_log(report, p_vec):
    path = _f2_os.environ.get("F2_CHECK_LOG")
    if not path:
        return
    try:
        res = report.results
        first_fail = next((i + 1 for i, r in enumerate(res) if not r.passed), 0)
        rec = {"pid": _f2_os.getpid(),
               "track": _f2_os.environ.get("F2_TRACK", "unknown"),
               "pvec": {str(k): v for k, v in (p_vec or {}).items()},
               "checks": [bool(r.passed) for r in res],
               "first_fail": first_fail,
               "all_passed": bool(report.all_passed)}
        with open(path, "a") as f:
            f.write(_f2_json.dumps(rec) + "\\n")
            f.flush()
    except Exception:
        pass
'''

PROVER_OLD = '''        try:
            outcome = self.orch._run_prover(c)
        except Exception as exc:
            print(f"[Evolution] prover error for {c.conjecture_id}: {exc}",
                  flush=True)
            outcome = "failed"'''
PROVER_NEW = '''        # [F2] PROVER DISABLED (search-level loop ablation): no Lean prover and
        # no entailment precheck; a no-CE conjecture is recorded as a survivor.
        set_conjecture_status(spec.name, "prover_failed",
                              detail={"outcome": "survivor_prover_disabled"})
        return "survivor"'''

# ── llm_direct: additive propose-call instrumentation helper injected into agent.py
LLMD_HELPER = '''

# ── [llm_direct] propose-call instrumentation (invalid outputs / shortfall /
#    hint-emptiness) — additive; writes a JSONL record per propose call. ──
import os as _f2_os, json as _f2_json
def _llmd_log(rec):
    _p = _f2_os.environ.get("F2_LLM_INVALID_LOG")
    if not _p:
        return
    try:
        rec = dict(rec)
        rec["pid"] = _f2_os.getpid()
        with open(_p, "a") as _f:
            _f.write(_f2_json.dumps(rec) + "\\n")
            _f.flush()
    except Exception:
        pass
'''

# anchors inside _llm_propose
PROPOSE_TIMEOUT_OLD = '''            text = self.client._call(prompt, model=propose_model,
                                     system=CONJ_GEN_SYSTEM, timeout=60,
                                     max_attempts=1, effort="low")'''
PROPOSE_TIMEOUT_NEW = '''            text = self.client._call(prompt, model=propose_model,
                                     system=CONJ_GEN_SYSTEM, timeout=600,
                                     max_attempts=1, effort="low")'''

PROPOSE_TAIL_OLD = '''        except Exception as exc:
            print(f"[conjecture generator] LLM propose skipped ({exc})", flush=True)
            return []
        data = _extract_json_from_text(text) or {}
        out: list[str] = []
        for f in data.get("conjectures", []):
            if isinstance(f, str) and f.strip().lower().startswith("if"):
                out.append(canonicalize_formula(f.strip()))
        print(f"[conjecture generator] LLM proposed {len(out)} candidate(s)",
              flush=True)
        return out'''
PROPOSE_TAIL_NEW = '''        except Exception as exc:
            # [llm_direct] API error / rate-limit / timeout: the LLM is the only
            # source, so this zeros the generation. Treat as a crash (rerun seed);
            # NOT counted as shortfall.
            _llmd_log({"status": "infra_error", "stage": "call",
                       "n_requested": self.llm_propose_n, "error": str(exc)[:300]})
            raise RuntimeError(f"llm_direct infra failure in propose: {exc}")
        # [llm_direct] evidence: dump the full propose prompt (for the hint-block
        # self-check) and record hint-emptiness.
        _lp = _f2_os.environ.get("F2_PROMPT_LOG")
        if _lp:
            try:
                with open(_lp, "a") as _pf:
                    _pf.write("\\n\\n===== PROPOSE PROMPT (n_requested="
                              + str(self.llm_propose_n) + ") =====\\n" + prompt)
            except Exception:
                pass
        _hints_empty = (not signals.get("proved") and not signals.get("refuted")
                        and not signals.get("prover_stuck")
                        and not signals.get("survivor")
                        and str(focus_block).strip().startswith("(none"))
        data = _extract_json_from_text(text) or {}
        raw = data.get("conjectures", []) if isinstance(data, dict) else []
        out: list[str] = []
        invalids: list = []
        for f in raw:
            if isinstance(f, str) and f.strip().lower().startswith("if"):
                out.append(canonicalize_formula(f.strip()))
            else:
                invalids.append(f)
        n_valid_raw = len(out)
        if (not isinstance(data, dict)) or ("conjectures" not in data) or (n_valid_raw == 0):
            # [llm_direct] parse failure / truncation / zero valid formulas -> the
            # generation is zeroed. Treat as a crash (rerun seed); NOT shortfall.
            _llmd_log({"status": "empty_or_truncated",
                       "n_requested": self.llm_propose_n,
                       "n_returned": len(raw), "n_valid_raw": n_valid_raw,
                       "n_invalid": len(invalids), "hints_empty": bool(_hints_empty)})
            raise RuntimeError("llm_direct empty/truncated/zero-valid propose response")
        # [llm_direct] enforce the candidate cap: the LLM may return a few more
        # than requested; never let more than n_requested candidates reach the
        # gates (keeps candidates-evaluated <= the closed-arm count).
        if n_valid_raw > self.llm_propose_n:
            out = out[:self.llm_propose_n]
        _llmd_log({"status": "ok", "n_requested": self.llm_propose_n,
                   "n_returned": len(raw), "n_valid_raw": n_valid_raw,
                   "n_entered": len(out), "n_invalid": len(invalids),
                   "hints_empty": bool(_hints_empty),
                   "shortfall": max(0, self.llm_propose_n - n_valid_raw),
                   "overflow_trimmed": max(0, n_valid_raw - self.llm_propose_n),
                   "invalid_samples": [str(x)[:120] for x in invalids[:5]]})
        print(f"[conjecture generator] LLM proposed {len(out)} candidate(s) "
              f"(requested {self.llm_propose_n}, returned {len(raw)}, "
              f"valid {n_valid_raw}, entered {len(out)}, invalid {len(invalids)})",
              flush=True)
        return out'''

# llm_direct source-off anchors
G3_FULL_OLD = '''        discovered = self._discover(table) or []
        if not discovered:
            core = [c for c in ["is_simple"] + NUMERIC_COLS if c in table.columns]
            print(f"[conjecture generator] 0 raw conjectures; retrying with core "
                  f"columns only ({core})", flush=True)
            discovered = self._discover(table[core]) or []'''
G3_FULL_NEW = '''        discovered = []  # [llm_direct] Graffiti3 full-table pass OFF (both passes)'''

G3_STRAT_OLD = '''        stratified_formulas = self._discover_stratified(table)'''
G3_STRAT_NEW = '''        stratified_formulas = []  # [llm_direct] Graffiti3 stratified OFF'''

MINER_OLD = '''        mined = mine_support_bounds(gate_pvecs, known_formulas)'''
MINER_NEW = '''        mined = []  # [llm_direct] support-function miner OFF'''


def patch_validator(arm_dir):
    p = f"{arm_dir}/agent/orchestrator/tools/check_pvector.py"
    s = open(p).read()
    assert "_f2_check_log" not in s
    s = s.replace("def worker_setpgrp(", LOG_HELPER.strip() + "\n\n\ndef worker_setpgrp(", 1)
    idx = s.index("report.witness_edges"); ret = s.index("        return report", idx)
    s = s[:ret] + "        _f2_check_log(report, p_vec)\n" + s[ret:]
    open(p, "w").write(s)


def patch_prover(arm_dir):
    p = f"{arm_dir}/agent/orchestrator/evolution_loop.py"
    s = open(p).read(); assert PROVER_OLD in s, "prover anchor missing"
    open(p, "w").write(s.replace(PROVER_OLD, PROVER_NEW, 1))


def patch_openloop(arm_dir):
    p = f"{arm_dir}/agent/conjecture_generator/agent.py"
    s = open(p).read()
    for old, new in [
        ('        signals = derive_signals()',
         '        signals = {"proved": [], "refuted": [], "prover_stuck": [], "survivor": []}  # [F2 open-loop] ALL outcome signals withheld (incl. LLM hint block)'),
        ('        focus_cells = self._dynamic_cells(alive_specs, table,\n                                          seed=len(existing_all))',
         '        focus_cells = []  # [F2 open-loop] dynamic cells (outcome-driven) withheld'),
        ('        mutated = generate_mutations(signals, gate_pvecs)',
         '        mutated = []  # [F2 open-loop] mutation engine (outcome-built) withheld')]:
        assert old in s, "openloop anchor missing: " + old[:40]
        s = s.replace(old, new, 1)
    open(p, "w").write(s)


def patch_llmdirect_sources(arm_dir):
    p = f"{arm_dir}/agent/conjecture_generator/agent.py"
    s = open(p).read()
    for old, new in [(G3_FULL_OLD, G3_FULL_NEW), (G3_STRAT_OLD, G3_STRAT_NEW),
                     (MINER_OLD, MINER_NEW)]:
        assert old in s, "llm_direct source anchor missing: " + old[:50]
        assert new not in s
        s = s.replace(old, new, 1)
    open(p, "w").write(s)


def patch_llmdirect_budget(arm_dir):
    p = f"{arm_dir}/agent/conjecture_generator/agent.py"
    s = open(p).read()
    assert PROPOSE_TIMEOUT_OLD in s, "propose timeout anchor missing"
    s = s.replace(PROPOSE_TIMEOUT_OLD, PROPOSE_TIMEOUT_NEW, 1)
    open(p, "w").write(s)


def patch_llmdirect_logging(arm_dir):
    p = f"{arm_dir}/agent/conjecture_generator/agent.py"
    s = open(p).read()
    assert "_llmd_log" not in s
    anchor = "from agent.llm_ce_finder.agent import _extract_json_from_text"
    assert anchor in s, "llmd helper anchor missing"
    s = s.replace(anchor, anchor + "\n" + LLMD_HELPER.rstrip() + "\n", 1)
    assert PROPOSE_TAIL_OLD in s, "propose tail anchor missing"
    s = s.replace(PROPOSE_TAIL_OLD, PROPOSE_TAIL_NEW, 1)
    open(p, "w").write(s)


def prepare_arm(dest):
    """Fresh snapshot copy at `dest` with all patches applied. Idempotent reset."""
    if os.path.exists(dest):
        shutil.rmtree(dest)
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    shutil.copytree(SNAP, dest)
    patch_validator(dest)
    patch_prover(dest)
    patch_openloop(dest)
    patch_llmdirect_sources(dest)
    patch_llmdirect_budget(dest)
    patch_llmdirect_logging(dest)
    os.makedirs(f"{dest}/f2_out", exist_ok=True)
    for f in ["agent/orchestrator/tools/check_pvector.py",
              "agent/orchestrator/evolution_loop.py",
              "agent/conjecture_generator/agent.py"]:
        subprocess.run([sys.executable, "-c",
                        f"import ast;ast.parse(open('{dest}/{f}').read())"], check=True)
    return dest


def main():
    if len(sys.argv) != 2:
        print("usage: f2b_llmdirect_setup.py <seed_int>", file=sys.stderr); sys.exit(2)
    seed = int(sys.argv[1])
    dest = f"{ROOT}/seed{seed}/llm_direct"
    prepare_arm(dest)
    pr = os.path.realpath(f"{dest}/agent/orchestrator/orchestrator.py").rsplit("/agent", 1)[0]
    assert pr == dest, pr
    print(f"seed{seed}/llm_direct: fresh copy + patches applied, syntax OK, "
          f"isolation verified (_PROJECT_ROOT resolves to the arm)")


if __name__ == "__main__":
    main()
