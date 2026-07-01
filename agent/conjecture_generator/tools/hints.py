"""
agent/conjecture_generator/tools/hints.py — generation hint store.

Package-local hints.json holds the evolution loop's accumulated knowledge:
  success — conjectures the Lean prover PROVED (primary guide for generation)
  failure — conjectures refuted by a CE or failed by the prover (gatekeeper)

Hints feed ONLY the generator (LLM propose/review prompts). They never touch
CE finding or any verification gate.
"""
from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path

HINTS_PATH = Path(__file__).resolve().parents[1] / "hints.json"

_EMPTY = {"success": [], "failure": []}


def load_hints() -> dict:
    if not HINTS_PATH.is_file():
        return {"success": [], "failure": []}
    try:
        data = json.loads(HINTS_PATH.read_text())
    except Exception:
        return {"success": [], "failure": []}
    return {
        "success": [e for e in data.get("success", []) if isinstance(e, dict)],
        "failure": [e for e in data.get("failure", []) if isinstance(e, dict)],
    }


def _save(hints: dict) -> None:
    tmp = HINTS_PATH.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(hints, indent=2, ensure_ascii=False))
    tmp.replace(HINTS_PATH)


def _add(kind: str, formula: str, reason: str) -> None:
    hints = load_hints()
    entries = hints[kind]
    for e in entries:
        if e.get("formula") == formula:
            e["reason"] = reason
            e["at"] = datetime.now(timezone.utc).isoformat()
            _save(hints)
            return
    entries.append({
        "formula": formula,
        "reason": reason,
        "at": datetime.now(timezone.utc).isoformat(),
    })
    _save(hints)


def add_success_hint(formula: str, reason: str) -> None:
    """reason: e.g. proof file path / prover summary."""
    _add("success", formula, reason)


def add_failure_hint(formula: str, reason: str) -> None:
    """reason: e.g. 'refuted by CE {3: 4, 6: 18} (p6=18 < RHS=20)' or
    'prover failed: nodes [...]'."""
    _add("failure", formula, reason)


def format_hint_block(entries: list[dict], max_entries: int = 15) -> str:
    """Render hint entries for prompt embedding (most recent last)."""
    if not entries:
        return "  (none yet)"
    lines = [f"  - {e.get('formula')}\n      ↳ {e.get('reason', '')}"
             for e in entries[-max_entries:]]
    return "\n".join(lines)


# ── survivor hints ─────────────────────────────────────────────────────────────
# A "survivor" is an unsolved conjecture that has weathered many RL CE attempts
# without being refuted. That's a strong (though weaker than Lean) signal that
# the bound is probably valid and its STRUCTURE is worth mimicking — far ahead
# of waiting for the prover to produce a real success hint.

SURVIVOR_THRESHOLD = 20  # registry's `increment_attempt` threshold


def enrich_hints_with_survivors(hints: dict,
                                source: str | None = None,
                                threshold: int = SURVIVOR_THRESHOLD,
                                max_entries: int = 20) -> dict:
    """Mutate `hints` in place, adding `hints['survivor']` populated from
    registry + conjectures.json. Picks unsolved entries with
    `attempts_without_ce >= threshold`. Does NOT persist (transient signal —
    a future CE attempt could refute the survivor at any time)."""
    from agent.conjectures import (   # local import to dodge cycle
        load_registry,
        _load_raw_dataset,
    )
    hints.setdefault("survivor", [])
    try:
        reg = load_registry(source)
        raw = _load_raw_dataset(source)
    except Exception:
        return hints

    name_to_formula = {e.get("name"): e.get("formula")
                       for e in raw["unsolved"] + raw["solved"]
                       if e.get("name") and e.get("formula")}

    candidates = []
    for name, rec in reg.items():
        if not isinstance(rec, dict):
            continue
        if rec.get("status") != "unsolved":
            continue
        attempts = int(rec.get("attempts_without_ce", 0) or 0)
        if attempts < threshold:
            continue
        formula = name_to_formula.get(name)
        if not formula:
            continue
        candidates.append((attempts, name, formula))

    # most-survived first; keep up to max_entries
    candidates.sort(reverse=True)
    for attempts, name, formula in candidates[:max_entries]:
        hints["survivor"].append({
            "formula": formula,
            "reason": f"survived {attempts} CE attempts (potentially_valid)",
        })
    return hints
