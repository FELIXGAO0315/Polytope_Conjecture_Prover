"""
agent/conjecture_generator/tools/signals.py — generation signal derivation.

Every signal the generator's LLM prompts consume is DERIVED fresh from the
canonical stores at generation time — nothing is cached in a side file
(the old hints.json store rotted the moment a prover run bypassed the
evolution loop; a derived view cannot rot):

  proved       — conjectures.json `proved` bucket. Lean-verified theorems,
                 the strongest guide for what to propose next.
  refuted      — conjectures.json `failed` bucket. Gatekeeper: same shape
                 with shifted constants is still refuted territory.
  prover_stuck — unsolved entries with status='prover_failed'. These beat
                 every CE search (so they are PROBABLY TRUE) but the Lean
                 prover could not close them from the current Inventory.
                 Structure worth mimicking — NOT a gatekeeper.
  survivor     — unsolved entries with >= SURVIVOR_THRESHOLD CE attempts
                 in registry.json. Weaker form of the same signal.

Refuted reasons prefer the entry's own ``status_detail`` (written by the
evolution loop and the artifact reconcile); entries whose status predates
detail-writing fall back to reading the CE artifact under
output/conjecture_with_ce/.

Signals feed ONLY the generator (LLM propose/review prompts). They never
touch CE finding or any verification gate.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

_PROJECT_ROOT = Path(__file__).resolve().parents[3]
_CE_DIR = _PROJECT_ROOT / "output" / "conjecture_with_ce"

SURVIVOR_THRESHOLD = 20  # registry's `increment_attempt` threshold

_TRAILING_NUM_RE = re.compile(r"(\d+)$")


def _num(name: str) -> int | None:
    """Trailing number shared by every naming scheme in this repo:
    `auto_20260627_163213_104`, `C104`, artifact stems `c104`/`C104` → 104.
    The generator continues one global suffix across all schemes, so the
    number identifies a conjecture uniquely."""
    m = _TRAILING_NUM_RE.search(name or "")
    return int(m.group(1)) if m else None


def _pvec_str(vec) -> str:
    """[1, 0, 13, …] (index 0 = p3) → '{3:1, 5:13, …}' — the CE rendering
    used across the repo's logs."""
    pv = {}
    for i, v in enumerate(vec or []):
        try:
            n = int(v or 0)
        except (TypeError, ValueError):
            n = 0
        if n:
            pv[i + 3] = n
    return "{" + ", ".join(f"{k}:{v}" for k, v in sorted(pv.items())) + "}"


def _ce_artifact_reasons() -> dict[int, str]:
    """{trailing-number: reason} for every CE artifact on disk — fallback
    for `failed` entries whose status_detail was never written."""
    out: dict[int, str] = {}
    if not _CE_DIR.is_dir():
        return out
    for jf in _CE_DIR.glob("*/*.json"):
        num = _num(jf.stem)
        if num is None or num in out:
            continue
        try:
            payload = json.loads(jf.read_text())
        except Exception:
            continue
        ce = payload.get("counterexample") or {}
        detail = payload.get("violation_detail") or ""
        if ce.get("p_vector"):
            out[num] = (f"refuted by CE {_pvec_str(ce['p_vector'])}"
                        + (f" ({detail})" if detail else ""))
        elif detail:
            out[num] = f"refuted ({detail})"
    return out


def _sort_key(entry: dict) -> int:
    """Oldest first, so format_hint_block's tail == most recent."""
    return int(entry.get("status_at") or entry.get("created_at") or 0)


def derive_signals(source=None) -> dict[str, list[dict]]:
    """Return the four signal lists, each [{formula, reason}, …] oldest
    first. Tolerates a missing/empty dataset by returning empty lists."""
    from agent.conjectures import _load_raw_dataset, load_registry  # no cycle at call time

    signals: dict[str, list[dict]] = {
        "proved": [], "refuted": [], "prover_stuck": [], "survivor": [],
    }
    try:
        data = _load_raw_dataset(source)
    except Exception:
        return signals

    # ── proved ────────────────────────────────────────────────────────────
    # Vacuous truths stay in the dataset as records but are NOT templates
    # worth mimicking, so they are excluded from the PROVED prompt block:
    #   touch == 0  — the bound is never tight anywhere on the verified
    #                 pool (C137: hypothesis forces RHS < 0 ≤ p6);
    #   p6 >= K, K ≤ 0 — the constant flavour (legacy C1 `p6 >= 0`).
    # Feeding these to the LLM teaches it that empty bounds "win".
    for e in sorted(data.get("proved", []), key=_sort_key):
        if not e.get("formula"):
            continue
        iris = e.get("iris") or {}
        if iris.get("touch") == 0:
            continue
        m = re.search(r"then\s+p6\s*>=\s*\(?\s*(-?\d+(?:\.\d+)?)\s*\)?\s*$",
                      e["formula"])
        if m and float(m.group(1)) <= 0:
            continue
        proof = (e.get("status_detail") or {}).get("proof")
        signals["proved"].append({
            "formula": e["formula"],
            "reason": f"Lean-proved, 0 sorry ({proof})" if proof
                      else "Lean-proved, 0 sorry",
        })

    # ── refuted ───────────────────────────────────────────────────────────
    artifact_reasons: dict[int, str] | None = None  # lazy — one glob, only if needed
    for e in sorted(data.get("failed", []), key=_sort_key):
        if not e.get("formula"):
            continue
        detail = e.get("status_detail") or {}
        pv, violation = detail.get("ce_p_vector"), detail.get("violation", "")
        if isinstance(pv, dict) and pv:
            body = "{" + ", ".join(f"{k}:{v}" for k, v in
                                   sorted(pv.items(), key=lambda kv: int(kv[0]))) + "}"
            reason = f"refuted by CE {body}" + (f" ({violation})" if violation else "")
        else:
            if artifact_reasons is None:
                artifact_reasons = _ce_artifact_reasons()
            num = _num(e.get("name") or "")
            reason = artifact_reasons.get(num) if num is not None else None
            reason = reason or "refuted (CE on file)"
        signals["refuted"].append({"formula": e["formula"], "reason": reason})

    # ── prover_stuck / survivor (both live in `unsolved`) ─────────────────
    try:
        reg = load_registry(source if isinstance(source, str) else None)
    except Exception:
        reg = {}
    for e in sorted(data.get("unsolved", []), key=_sort_key):
        if not e.get("formula") or not e.get("name"):
            continue
        if e.get("status") == "prover_failed":
            outcome = (e.get("status_detail") or {}).get("outcome")
            signals["prover_stuck"].append({
                "formula": e["formula"],
                "reason": ("survived CE search but the prover could not close "
                           "it from the current Inventory"
                           + (f" (outcome: {outcome})" if outcome else "")),
            })
            continue
        attempts = int((reg.get(e["name"]) or {}).get("attempts_without_ce", 0) or 0)
        if attempts >= SURVIVOR_THRESHOLD:
            signals["survivor"].append({
                "formula": e["formula"],
                "reason": f"survived {attempts} CE attempts (potentially_valid)",
            })

    return signals


def format_hint_block(entries: list[dict], max_entries: int = 15) -> str:
    """Render signal entries for prompt embedding (most recent last)."""
    if not entries:
        return "  (none yet)"
    lines = [f"  - {e.get('formula')}\n      ↳ {e.get('reason', '')}"
             for e in entries[-max_entries:]]
    return "\n".join(lines)
