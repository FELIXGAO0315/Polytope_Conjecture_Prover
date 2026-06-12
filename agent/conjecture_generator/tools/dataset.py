"""
agent/conjecture_generator/tools/dataset.py — discovery dataset assembly.

Base rows come from the package-local data/polytopes.csv (p-vectors of
verified simple 3-polytopes). The table is augmented with every p-vector
this repo's own pipeline has PROVEN realizable:
  - verified counterexamples   (output/conjecture_with_ce/*/<Cx>.json)
  - 'realizable' verdicts      (output/realizability_cache.json)

so each new generation of conjectures is fitted against everything already
learned and cannot contradict a known polytope.
"""
from __future__ import annotations

import json
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
F2_MIN, F2_MAX = 5, 49

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
    if extra:
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

    table = pd.DataFrame(index=df.index)
    table["is_simple"] = df["is_simple"].where(df["is_simple"].notna(), True).astype(bool)
    for j in range(SUM_PK_MIN_J, SUM_PK_MAX_J + 1):
        table[f"sum_pk_k>=7_at_least_{j}"] = (sum7 >= j)
    for j in range(F2_MIN, F2_MAX + 1):
        table[f"f_2>=_{j}"] = (f2 >= j)
    hyp_cols = [c for c in table.columns if table[c].any()]
    table = table[hyp_cols].copy()
    for col in NUMERIC_COLS:
        table[col] = pd.to_numeric(df[col], errors="coerce").fillna(0)
    return table.reset_index(drop=True), row_pvecs, hyp_cols
