#!/usr/bin/env bash
# F2b-llm_direct runner: 5 seeds (41 7 123 2024 99), single llm_direct arm each,
# K=2 generations, deterministic downstream B, prover disabled. The closed/open
# arms are NOT rerun — they come from the committed F2b results (314ed95).
#
# Concurrency: <= 2 seeds at a time (recorded in this log). Each seed is a FRESH
# patched copy of the a1eab93 snapshot under
#   /home/felix_gao/ldno_exp/f2b_llmdirect/seed<seed>/llm_direct
# Infra failures (driver exit 3: API error / rate-limit / timeout / empty-or-
# truncated propose response) rerun the seed from scratch (unchanged settings),
# up to MAX_ATTEMPTS; every occurrence is logged. Budget: timeout 600s /
# max_attempts 1 / max_tokens 32000 (CLAUDE_CODE_MAX_OUTPUT_TOKENS). Hard stop
# 2026-11-18 23:00 America/New_York — nothing starts or runs past it.
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SETUP="$HERE/f2b_llmdirect_setup.py"
DRIVER="$HERE/f2b_llmdirect_driver.py"
METRICS="$HERE/f2_metrics.py"
CAPS="$HERE/f2b_caps.json"
ROOT=/home/felix_gao/ldno_exp/f2b_llmdirect
SEEDS=(41 7 123 2024 99)
K=2
MAX_ATTEMPTS=3
CONCURRENCY=2
DEADLINE_EPOCH=$(date -d "2026-11-18 23:00:00" +%s)   # box TZ is America/New_York

export OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
export CE_PLANTRI_PARALLEL=3 CE_PLANTRI_PARALLEL_DEEP=1
export CLAUDE_CODE_MAX_OUTPUT_TOKENS=32000   # arm-isolated output-token cap (<= Opus 4.7 128K)

log(){ echo "[run_llmdirect $(date +%T)] $*"; }
mkdir -p "$ROOT"

# ---- kill leftover experiment processes (not this run / not Claude Code) ----
log "killing leftover experiment processes (if any) …"
for pat in f2b_llmdirect_driver.py f2b_llmdirect_smoke.py f2b_driver.py f2_driver.py f2b_smoke_gen.py; do
  pids=$(pgrep -f "$pat" || true)
  [ -n "$pids" ] && { log "  killing $pat: $pids"; pkill -9 -f "$pat" || true; }
done
sleep 2
log "remaining python processes on box:"; pgrep -af python | grep -v run_f2b_llmdirect || true

run_seed(){
  local s=$1 AD="$ROOT/seed$s/llm_direct" attempt=1 rc
  while [ $attempt -le $MAX_ATTEMPTS ]; do
    now=$(date +%s)
    if [ "$now" -ge "$DEADLINE_EPOCH" ]; then log "seed $s: HARD STOP reached — not (re)starting"; return 9; fi
    log "seed $s: attempt $attempt/$MAX_ATTEMPTS — fresh setup"
    python3 "$SETUP" "$s" >> "$ROOT/seed${s}_setup.log" 2>&1 || { log "seed $s setup FAILED (attempt $attempt)"; attempt=$((attempt+1)); continue; }
    mkdir -p "$AD/f2_out"
    # baseline snapshot BEFORE the run (frozen registry cells), via f2_metrics baseline mode
    python3 "$METRICS" "$AD" "$AD/f2_out/baseline.json" /dev/null baseline \
        > "$AD/f2_out/baseline.stdout" 2>&1 || true
    remain=$(( DEADLINE_EPOCH - $(date +%s) )); [ "$remain" -lt 1 ] && remain=1
    log "seed $s: launch driver (deadline budget ${remain}s)"
    ( cd "$AD" && \
        F2_CHECK_LOG="$AD/f2_out/checklog.jsonl" F2_TRACK="downstream" \
        F2_LLM_INVALID_LOG="$AD/f2_out/llm_invalid.jsonl" \
        F2_PROMPT_LOG="$AD/f2_out/propose_prompts.txt" \
        PYTHONHASHSEED="$s" CE_CONSTRUCT_SEED="$s" \
        CLAUDE_CODE_MAX_OUTPUT_TOKENS=32000 \
        timeout "$remain" nice -n 19 python3 -u "$DRIVER" --seed "$s" --k $K --caps "$CAPS" \
    ) > "$AD/f2_out/driver.log" 2>&1
    rc=$?
    if grep -q "ARM COMPLETE" "$AD/f2_out/driver.log" 2>/dev/null; then
      log "seed $s: ARM COMPLETE (attempt $attempt, rc=$rc)"; return 0
    fi
    log "seed $s: attempt $attempt did NOT complete (rc=$rc) — recording infra/crash occurrence"
    { echo "=== seed $s attempt $attempt FAILED rc=$rc @ $(date -Is) ==="; tail -n 25 "$AD/f2_out/driver.log"; } \
        >> "$ROOT/seed${s}_failures.log" 2>&1
    attempt=$((attempt+1))
  done
  log "seed $s: EXHAUSTED $MAX_ATTEMPTS attempts — reported as incomplete"; return 1
}

log "START 5 seeds, concurrency=$CONCURRENCY, K=$K, downstream=B, deadline=$(date -d @$DEADLINE_EPOCH +%T)"
i=0
while [ $i -lt ${#SEEDS[@]} ]; do
  wave=(); pids=()
  for j in $(seq 0 $((CONCURRENCY-1))); do
    idx=$((i+j)); [ $idx -ge ${#SEEDS[@]} ] && break
    wave+=("${SEEDS[$idx]}")
  done
  log "WAVE: seeds ${wave[*]} (concurrency=${#wave[@]})"
  for s in "${wave[@]}"; do run_seed "$s" & pids+=($!); done
  wait "${pids[@]}"
  log "wave done"
  i=$((i+CONCURRENCY))
done
log "F2b-llm_direct RUNNER COMPLETE"
