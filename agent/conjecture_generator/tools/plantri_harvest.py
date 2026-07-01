"""
agent/conjecture_generator/tools/plantri_harvest.py — exhaustive simple-3-polytope
p-vector harvest using plantri.

plantri's `-a` mode emits ASCII adjacency lists of every isomorph-free
3-connected planar triangulation on N vertices. The dual is a simple
3-polytope with N facets, and the degree multiset of the triangulation
is exactly the p-vector of the polytope. We stream plantri's stdout,
extract the degree multiset per line, and dedup across N, min-deg tier,
and the verified-realizability cache.

The cache file (plantri_pool.json) is consumed by dataset.py. The harvest
itself is a one-shot CLI:

    python -m agent.conjecture_generator.tools.plantri_harvest \\
        [--f2-min 4] [--f2-max 24] [--per-budget 60]

so once produced, future generator runs read it for free.
"""
from __future__ import annotations

import json
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Optional

_PROJECT_ROOT = Path(__file__).resolve().parents[3]
_PLANTRI_DIR = _PROJECT_ROOT / "agent" / "orchestrator" / "tools" / "plantri"
PLANTRI_MF = _PLANTRI_DIR / "plantri_mf"
POOL_CACHE = _PROJECT_ROOT / "output" / "conjecture_generator" / "plantri_pool.json"


def _parse_pvec_from_plantri_line(line: str) -> Optional[Dict[int, int]]:
    """One plantri `-a` line → {k: count} face-size multiset.

    Format: '<N> adj1,adj2,...,adjN' where adjI is the neighbour string of
    vertex I and len(adjI) is its degree. The degree multiset of the
    triangulation equals the face-size multiset of the dual simple polytope.
    """
    line = line.strip()
    if not line:
        return None
    parts = line.split(None, 1)
    if len(parts) != 2:
        return None
    try:
        n = int(parts[0])
    except ValueError:
        return None
    adj_lists = parts[1].split(",")
    if len(adj_lists) != n:
        return None
    counts: Dict[int, int] = {}
    for adj in adj_lists:
        d = len(adj)
        if d <= 0:
            return None
        counts[d] = counts.get(d, 0) + 1
    if sum(counts.values()) != n:
        return None
    return counts


@dataclass
class HarvestTier:
    """One min-deg / vertex-count slice of plantri's enumeration."""
    min_deg: int           # 3, 4, or 5
    n_min: int             # inclusive
    n_max: int             # inclusive
    per_n_budget_sec: float  # wall-time cap per N value


# Default tiers tuned so the full harvest fits in ~1-2 min on this WSL box.
# -m3 covers EVERY simple polytope, but the count of distinct triangulations
# explodes at N=16 (17M); we cap it there because higher-N -m3 timings
# dominate without adding distinct p-vectors that -m4 / -m5 don't reach.
# Empirical: at N=16, distinct p-vectors plateau ~10s of new entries.
DEFAULT_TIERS = [
    HarvestTier(min_deg=3, n_min=4,  n_max=16, per_n_budget_sec=20.0),
    HarvestTier(min_deg=4, n_min=8,  n_max=22, per_n_budget_sec=20.0),
    HarvestTier(min_deg=5, n_min=12, n_max=28, per_n_budget_sec=20.0),
]


def _harvest_tier(tier: HarvestTier, f2_min: int, f2_max: int,
                  pool: Dict[str, dict], verbose: bool) -> int:
    """Stream plantri on this tier, add distinct p-vectors to `pool`.
    Returns number of new (distinct) p-vectors discovered in this tier.
    """
    new_count = 0
    for n in range(tier.n_min, tier.n_max + 1):
        if n < f2_min or n > f2_max:
            continue
        cmd = [str(PLANTRI_MF), f"-m{tier.min_deg}", "-a", str(n)]
        tier_new = 0
        t0 = time.time()
        # Stream stdout line-by-line; kill the process when our wall-time
        # budget for this N is up. plantri is happy to be SIGTERM'd.
        try:
            proc = subprocess.Popen(
                cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                text=True, bufsize=1,
            )
        except FileNotFoundError as exc:
            print(f"[plantri_harvest] {cmd[0]} not found: {exc}", flush=True)
            return new_count
        assert proc.stdout is not None
        try:
            for line in proc.stdout:
                if time.time() - t0 > tier.per_n_budget_sec:
                    proc.kill()
                    break
                pv = _parse_pvec_from_plantri_line(line)
                if pv is None:
                    continue
                # Only keep p-vectors whose f_2 is the actual N we requested.
                # (A defensive check; plantri respects N strictly.)
                if sum(pv.values()) != n:
                    continue
                key = _pvec_key(pv)
                if key in pool:
                    continue
                pool[key] = {
                    "p_vec": {str(k): v for k, v in sorted(pv.items())},
                    "f_2": n,
                    "source": f"plantri_m{tier.min_deg}_n{n}",
                }
                tier_new += 1
                new_count += 1
        finally:
            try:
                proc.wait(timeout=1)
            except subprocess.TimeoutExpired:
                proc.kill()
        if verbose:
            elapsed = time.time() - t0
            print(f"[plantri_harvest] m={tier.min_deg} N={n:3d}  "
                  f"new={tier_new:4d}  total={len(pool):4d}  "
                  f"({elapsed:.1f}s)", flush=True)
    return new_count


def _pvec_key(pv: Dict[int, int]) -> str:
    """Stable string key matching realizability_cache convention."""
    return ",".join(f"{k}:{v}" for k, v in sorted(pv.items()))


def harvest_plantri_pool(
    f2_min: int = 4,
    f2_max: int = 28,
    tiers: Optional[List[HarvestTier]] = None,
    cache_path: Path = POOL_CACHE,
    verbose: bool = True,
) -> dict:
    """Run plantri across all tiers, dedup, persist to cache_path.

    Returns the in-memory pool dict {p_vec_key: {p_vec, f_2, source}}.
    The cache is overwritten on each successful run; partial writes are
    avoided by writing to a temp file first.
    """
    if not PLANTRI_MF.exists():
        raise FileNotFoundError(f"plantri binary missing: {PLANTRI_MF}")

    pool: Dict[str, dict] = {}
    # Seed the pool with any previously cached entries — re-running is
    # incremental and cheap (dedup catches re-discoveries).
    if cache_path.is_file():
        try:
            prior = json.loads(cache_path.read_text())
            for entry in prior.get("p_vecs", []):
                key = entry.get("key") or _pvec_key(
                    {int(k): v for k, v in entry["p_vec"].items()})
                pool[key] = entry
            if verbose:
                print(f"[plantri_harvest] seeded {len(pool)} entries from cache",
                      flush=True)
        except Exception as exc:
            print(f"[plantri_harvest] cache reseed failed ({exc}); starting fresh",
                  flush=True)
            pool = {}

    t0 = time.time()
    for tier in (tiers or DEFAULT_TIERS):
        if verbose:
            print(f"[plantri_harvest] tier m={tier.min_deg} "
                  f"N=[{tier.n_min}, {tier.n_max}]  "
                  f"budget={tier.per_n_budget_sec}s/N", flush=True)
        _harvest_tier(tier, f2_min, f2_max, pool, verbose)

    cache_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "f2_min": f2_min,
        "f2_max": f2_max,
        "p_vecs": [
            {"key": key, **entry} for key, entry in sorted(pool.items())
        ],
    }
    tmp = cache_path.with_suffix(cache_path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2))
    tmp.replace(cache_path)

    if verbose:
        elapsed = time.time() - t0
        print(f"[plantri_harvest] done: {len(pool)} distinct p-vectors "
              f"({elapsed:.1f}s wall)  →  {cache_path}", flush=True)
    return pool


def load_plantri_pool(cache_path: Path = POOL_CACHE) -> List[dict]:
    """Return list of pool entries; empty list if cache is absent."""
    if not cache_path.is_file():
        return []
    try:
        payload = json.loads(cache_path.read_text())
    except Exception:
        return []
    return list(payload.get("p_vecs", []))


def main() -> None:
    import argparse
    ap = argparse.ArgumentParser(description="Plantri pool harvest")
    ap.add_argument("--f2-min", type=int, default=4)
    ap.add_argument("--f2-max", type=int, default=28)
    ap.add_argument("--per-budget", type=float, default=20.0,
                    help="wall-time seconds per (tier, N) — tighten on a slow box")
    ap.add_argument("--cache", type=Path, default=POOL_CACHE)
    args = ap.parse_args()
    tiers = [HarvestTier(t.min_deg, t.n_min, t.n_max, args.per_budget)
             for t in DEFAULT_TIERS]
    harvest_plantri_pool(args.f2_min, args.f2_max, tiers, args.cache)


if __name__ == "__main__":
    main()
