"""
agent/conjecture_generator/tools/dataset.py — discovery dataset assembly.

Base rows come from the package-local data/polytopes.csv (p-vectors of
verified simple 3-polytopes). The table is augmented with every p-vector
this repo's own pipeline has PROVEN realizable, AND with the exhaustive
plantri pool harvested offline:

  - verified counterexamples   (output/conjecture_with_ce/*/<Cx>.json)
  - 'realizable' verdicts      (output/realizability_cache.json)
  - plantri pool harvest       (output/conjecture_generator/plantri_pool.json)

so each new generation of conjectures is fitted against everything already
proven realizable AND every simple 3-polytope plantri can enumerate at
f_2 ≤ 28. This kills the "few-hundred-row LP overfit" failure mode where
Graffiti3 emitted coefficients like 0.6428571429 that broke on the first
out-of-pool polytope.
"""
from __future__ import annotations

import json
import os
from ast import literal_eval
from pathlib import Path

import pandas as pd

_PROJECT_ROOT = Path(__file__).resolve().parents[3]
_PACKAGE_ROOT = Path(__file__).resolve().parents[1]
DATASET_CSV = _PACKAGE_ROOT / "data" / "polytopes.csv"
CE_DIR = _PROJECT_ROOT / "output" / "conjecture_with_ce"
REALIZABILITY_CACHE = _PROJECT_ROOT / "output" / "realizability_cache.json"

# Derived hypothesis-column ranges (same as the upstream conjecture agent)
SUM_PK_MIN_J, SUM_PK_MAX_J = 1, 11
# F2_MIN bumped from 5 → 7 because `(f_2>=_5)` and `(f_2>=_6)` are tautologies
# on the actual data (only 3 of ~1550 rows have f_2 ≤ 6). Keeping those
# columns lets the LP pick them as filler predicates that look meaningful but
# carry no information; the resulting conjectures inherit `(f_2>=_5)` as
# clause noise. Starting at 7 leaves morgan_filter free to still pick the
# smallest tight threshold without that floor.
F2_MIN, F2_MAX = 7, 49

NUMERIC_COLS = ["p_3", "p_4", "p_5", "p_6", "sum_pk_k>=7"]


def pvec_from_list(vec) -> dict[int, int]:
    """[p3, p4, …] (index 0 = triangles) → {k: count}, zero entries dropped."""
    out: dict[int, int] = {}
    for i, v in enumerate(vec or []):
        try:
            n = int(v or 0)
        except (TypeError, ValueError):
            n = 0
        if n > 0:
            out[i + 3] = n
    return out


def _pvec_from_cache_key(key: str) -> dict[int, int]:
    """'3:1,5:16,6:4,13:1' → {3: 1, 5: 16, 6: 4, 13: 1}"""
    out: dict[int, int] = {}
    for part in key.split(","):
        k, v = part.split(":")
        out[int(k)] = int(v)
    return out


def load_verified_pvecs() -> list[dict]:
    """Every p-vector the pipeline has proven realizable, with provenance."""
    rows: list[dict] = []
    if CE_DIR.is_dir():
        for jf in sorted(CE_DIR.glob("*/*.json")):
            try:
                ce = json.loads(jf.read_text()).get("counterexample", {})
                pv = pvec_from_list(ce.get("p_vector"))
                if pv:
                    rows.append({"p_vec": pv, "source": f"verified_ce:{jf.stem}"})
            except Exception:
                continue
    if REALIZABILITY_CACHE.is_file():
        try:
            cache = json.loads(REALIZABILITY_CACHE.read_text())
        except Exception:
            cache = {}
        for key, rec in cache.items():
            if isinstance(rec, dict) and rec.get("verdict") == "realizable":
                try:
                    rows.append({"p_vec": _pvec_from_cache_key(key),
                                 "source": "realizability_cache"})
                except Exception:
                    continue
    # Plantri harvest is the dominant source — strictly realizable simple
    # 3-polytopes enumerated by plantri's exhaustive generator. The cache is
    # produced offline by `python -m agent.conjecture_generator.tools.plantri_harvest`.
    try:
        from agent.conjecture_generator.tools.plantri_harvest import load_plantri_pool
        for entry in load_plantri_pool():
            try:
                pv = {int(k): int(v) for k, v in entry["p_vec"].items()}
                rows.append({"p_vec": pv,
                             "source": entry.get("source", "plantri_pool")})
            except Exception:
                continue
    except Exception:
        pass
    return rows


def _row_from_pvec(pv: dict[int, int], source: str) -> dict:
    kmax = max(pv)
    return {
        "is_simple": True,
        "p_vector": [pv.get(k, 0) for k in range(3, kmax + 1)],
        "p_3": pv.get(3, 0),
        "p_4": pv.get(4, 0),
        "p_5": pv.get(5, 0),
        "p_6": pv.get(6, 0),
        "sum_pk_k>=7": sum(v for k, v in pv.items() if k >= 7),
        "polytope_id": "",
        "source": source,
    }


def _stratify_augmentation(extra: list[dict], per_f2_cap: int = 60) -> list[dict]:
    """Cap per-f_2 augmentation rows so Graffiti3 LP cost stays bounded.

    Within each f_2 bucket we keep the row first if it's a "structural extreme"
    on one of the canonical axes (max p3, max p4, max p5, max p6, max
    sum_pk_k>=7), then fill the rest by signature-spread sampling. Cap defaults
    to 60 per bucket; overridable via CONJ_GEN_PER_F2_CAP env var. Empirically:
    491 + ~1500 stratified rows ≈ 2000 row LP that Graffiti3 fast-mode solves
    in under a minute.
    """
    if not extra:
        return extra

    def _f2(row) -> int:
        return int(sum(int(x or 0) for x in row.get("p_vector") or []))

    def _pk(row, k: int) -> int:
        v = row.get("p_vector") or []
        return int(v[k - 3]) if k - 3 < len(v) else 0

    def _sum7(row) -> int:
        v = row.get("p_vector") or []
        return sum(int(x or 0) for x in v[4:])  # indices 4+ → p7+

    def _sig(row) -> tuple:
        return (_pk(row, 3), _pk(row, 4), _pk(row, 5), _pk(row, 6), _sum7(row))

    by_f2: dict[int, list[dict]] = {}
    for row in extra:
        by_f2.setdefault(_f2(row), []).append(row)

    kept: list[dict] = []
    for f2, rows in sorted(by_f2.items()):
        if len(rows) <= per_f2_cap:
            kept.extend(rows)
            continue
        picked: list[dict] = []
        picked_sigs: set[tuple] = set()
        # 1. extremes — broad structural coverage first
        for key_fn in (
            lambda r: _pk(r, 3), lambda r: _pk(r, 4), lambda r: _pk(r, 5),
            lambda r: _pk(r, 6), _sum7, lambda r: max(int(x or 0) for x in
                                                       (r.get("p_vector") or [0])),
        ):
            best = max(rows, key=key_fn)
            s = _sig(best)
            if s not in picked_sigs:
                picked.append(best); picked_sigs.add(s)
        # 2. farthest-point spread on the structural signature axes
        for row in rows:
            if len(picked) >= per_f2_cap:
                break
            s = _sig(row)
            if s in picked_sigs:
                continue
            if all(any(abs(s[i] - t[i]) >= 1 for i in range(5)) for t in [_sig(p) for p in picked[-8:]]):
                picked.append(row); picked_sigs.add(s)
        # 3. fill remainder with any unseen-signature rows
        for row in rows:
            if len(picked) >= per_f2_cap:
                break
            s = _sig(row)
            if s in picked_sigs:
                continue
            picked.append(row); picked_sigs.add(s)
        kept.extend(picked)
    return kept


def select_representative_pvecs(
    row_pvecs: list[dict[int, int]],
    per_bucket: int = 1,
    extra_signatures: int = 6,
    total_cap: int = 20,
) -> list[dict[int, int]]:
    """Pick a small, diverse sample of the verified pool for prompt injection.

    Strategy: bucket by f_2 stepped through (4-16 every 1; 18-32 every 2; >32
    every 4), keep `per_bucket` polytopes per bucket via signature-spread
    sampling, then add `extra_signatures` more drawn from the extremal tails
    (max p3, max p4, max p6, max sum_pk_k>=7, max k, max f_2). Total capped
    so the prompt stays under ~3 KB.

    The sample is what the LLM sees as ground truth in propose/review prompts;
    a 24k-row pool can't be inlined, but a hand-picked ~40-row witness is
    enough for the LLM to do real counterexample checks instead of pattern
    matching against hints alone.
    """
    if not row_pvecs:
        return []

    def _sig(pv: dict[int, int]) -> tuple:
        return (pv.get(3, 0), pv.get(4, 0), pv.get(5, 0), pv.get(6, 0),
                sum(v for k, v in pv.items() if k >= 7))

    buckets: dict[int, list[dict[int, int]]] = {}
    for pv in row_pvecs:
        buckets.setdefault(sum(pv.values()), []).append(pv)

    def _bucket_step(f2: int) -> int:
        if f2 <= 16:
            return 1
        if f2 <= 32:
            return 2
        return 4

    sampled_f2 = sorted(b for b in buckets
                        if b == 4 or (b - 4) % _bucket_step(b) == 0)

    picked: list[dict[int, int]] = []
    picked_sigs: set[tuple] = set()

    for f2 in sampled_f2:
        pool = buckets[f2]
        if len(pool) <= per_bucket:
            chosen = pool
        else:
            # Pick `per_bucket` by maximising L∞ distance from already-picked
            # in the signature space — greedy farthest-point sampling.
            chosen: list[dict[int, int]] = [pool[0]]
            sigs = [_sig(pool[0])]
            for pv in pool[1:]:
                if len(chosen) >= per_bucket:
                    break
                s = _sig(pv)
                if any(s == t for t in sigs):
                    continue
                # accept if it adds a new corner of the local signature space
                if all(any(abs(s[i] - t[i]) >= 1 for i in range(5)) for t in sigs):
                    chosen.append(pv)
                    sigs.append(s)
        for pv in chosen:
            sig = _sig(pv)
            if sig not in picked_sigs:
                picked.append(pv)
                picked_sigs.add(sig)

    # Hard cap before extremals so the prompt budget stays predictable.
    if len(picked) > total_cap - extra_signatures:
        picked = picked[: total_cap - extra_signatures]
        picked_sigs = {_sig(pv) for pv in picked}

    # Extremal additions across the full pool (maximise individual axes).
    axes = [
        ("max_p3", lambda pv: pv.get(3, 0)),
        ("max_p4", lambda pv: pv.get(4, 0)),
        ("max_p5", lambda pv: pv.get(5, 0)),
        ("max_p6", lambda pv: pv.get(6, 0)),
        ("max_sum7", lambda pv: sum(v for k, v in pv.items() if k >= 7)),
        ("max_kmax", lambda pv: max(pv) if pv else 0),
        ("max_f2",   lambda pv: sum(pv.values())),
        ("max_simple_p6", lambda pv: pv.get(6, 0) if not any(k > 6 for k in pv) else 0),
    ]
    for _, key in axes:
        if len(picked) >= len(picked_sigs) + extra_signatures:
            break
        try:
            best = max(row_pvecs, key=key)
        except ValueError:
            continue
        sig = _sig(best)
        if sig not in picked_sigs:
            picked.append(best)
            picked_sigs.add(sig)
    return picked


def format_pvec_for_prompt(pv: dict[int, int]) -> str:
    """One-line p-vector rendering used in LLM prompts.

    Form: {3:1, 5:10, 6:33, 7:1}  | f_2=45 | sum_pk_k>=7=1
    so the LLM can read the structural axes without recomputing them.
    """
    body = "{" + ", ".join(f"{k}:{v}" for k, v in sorted(pv.items())) + "}"
    f2 = sum(pv.values())
    sum7 = sum(v for k, v in pv.items() if k >= 7)
    return f"{body}  | f_2={f2} | sum_pk_k>=7={sum7}"


def build_discovery_table() -> tuple[pd.DataFrame, list[dict[int, int]], list[str]]:
    """Return (table, row_pvecs, hypothesis_cols).

    table:     boolean hypothesis columns + numeric p-columns for Graffiti3.
    row_pvecs: one {k: count} dict per table row — used for the post-discovery
               consistency check with the repo's exact-fraction evaluators.
    """
    if not DATASET_CSV.is_file():
        raise FileNotFoundError(f"dataset not found: {DATASET_CSV}")
    df = pd.read_csv(DATASET_CSV, converters={"p_vector": literal_eval})

    seen = {tuple(v or []) for v in df["p_vector"]}
    extra: list[dict] = []
    for rec in load_verified_pvecs():
        row = _row_from_pvec(rec["p_vec"], rec["source"])
        key = tuple(row["p_vector"])
        if key in seen:
            continue
        seen.add(key)
        extra.append(row)
    # The plantri pool can be >20k rows. Graffiti3's LP cost scales with the
    # row count and grows un-economic past a few thousand rows — we stratify
    # the augmentation by f_2 bucket and structural signature so the LP fits
    # against a diverse cross-section, not a low-f_2-saturated mass.
    if extra:
        extra = _stratify_augmentation(extra,
                                       per_f2_cap=int(os.environ.get(
                                           "CONJ_GEN_PER_F2_CAP", "60")))
        df = pd.concat([df, pd.DataFrame(extra)], ignore_index=True)
        print(f"[conjecture generator] dataset augmented with {len(extra)} "
              f"pipeline-verified p-vector(s) → {len(df)} rows", flush=True)

    valid = df["p_vector"].apply(
        lambda v: isinstance(v, list) and len(v) > 3
        and any(int(x or 0) != 0 for x in v[:4])
    )
    dropped = int((~valid).sum())
    if dropped:
        print(f"[conjecture generator] dropping {dropped} row(s) with invalid p_vector",
              flush=True)
    df = df.loc[valid].copy()

    row_pvecs = [pvec_from_list(v) for v in df["p_vector"]]

    f2 = df["p_vector"].apply(lambda v: int(sum(int(x or 0) for x in v)))
    sum7 = pd.to_numeric(df["sum_pk_k>=7"], errors="coerce").fillna(0)

    p3 = pd.to_numeric(df["p_3"], errors="coerce").fillna(0).astype(int)
    p4 = pd.to_numeric(df["p_4"], errors="coerce").fillna(0).astype(int)
    p5 = pd.to_numeric(df["p_5"], errors="coerce").fillna(0).astype(int)

    table = pd.DataFrame(index=df.index)
    table["is_simple"] = df["is_simple"].where(df["is_simple"].notna(), True).astype(bool)
    for j in range(SUM_PK_MIN_J, SUM_PK_MAX_J + 1):
        table[f"sum_pk_k>=7_at_least_{j}"] = (sum7 >= j)
    for j in range(F2_MIN, F2_MAX + 1):
        table[f"f_2>=_{j}"] = (f2 >= j)

    # Structural predicates (Eberhard / Jučovič / Grünbaum families).
    # Naming rule: p<k>_eq_<n> / p<k>_le_<n> — canonicalize_hypothesis_tokens
    # translates these back to the DSL forms `p_<k> = <n>` / `p_<k> <= <n>`
    # at render and evaluation time. pvec_eval._compile_hypothesis already
    # handles those forms (regex at pvec_eval.py:266), so no evaluator work
    # is needed.
    #
    # Without these columns the LP can only describe `f_2 >= N`-style
    # hypotheses and is structurally blind to the classical sub-classes
    # mathematicians actually study (triangle-free, quadrilateral-free,
    # fullerene-shaped, …). With them, Graffiti3 can finally pick conditional
    # bounds whose hypotheses are sharp on whole structural strata of the
    # plantri pool rather than just on f_2 thresholds.
    table["p3_eq_0"] = (p3 == 0)
    table["p4_eq_0"] = (p4 == 0)
    table["p5_eq_0"] = (p5 == 0)
    table["p3_eq_0_and_p4_eq_0"] = (p3 == 0) & (p4 == 0)  # fullerene-shaped (5- and 6-gons + tail)
    table["p4_eq_0_and_p5_eq_0"] = (p4 == 0) & (p5 == 0)  # triangles + 6+ only
    table["p3_le_2"] = (p3 <= 2)                          # Grünbaum "few triangles"
    table["p4_le_2"] = (p4 <= 2)
    table["p5_le_2"] = (p5 <= 2)

    hyp_cols = [c for c in table.columns if table[c].any()]
    table = table[hyp_cols].copy()
    for col in NUMERIC_COLS:
        table[col] = pd.to_numeric(df[col], errors="coerce").fillna(0)
    return table.reset_index(drop=True), row_pvecs, hyp_cols
