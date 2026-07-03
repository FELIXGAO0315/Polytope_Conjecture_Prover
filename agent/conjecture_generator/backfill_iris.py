"""One-off: compute IRIS T/R/L for existing conjectures.json entries that
lack an `iris` field, and refresh the registry so the RL CE finder's
`--iris-sort` sees them.

Usage:
    python -m agent.conjecture_generator.backfill_iris            # default conjectures.json
    python -m agent.conjecture_generator.backfill_iris --dry-run
    python -m agent.conjecture_generator.backfill_iris --recompute  # rescore all, not just missing
"""
from __future__ import annotations

import argparse
import sys

from agent.conjectures import (
    ConjectureSpec,
    _load_raw_dataset,
    _write_raw_dataset,
)
from agent.conjecture_generator.tools.dataset import build_discovery_table
from agent.conjecture_generator.tools.iris_scoring import compute_iris


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source", default=None,
                    help="path to conjectures.json (default: project default)")
    ap.add_argument("--dry-run", action="store_true",
                    help="print scores but don't write")
    ap.add_argument("--recompute", action="store_true",
                    help="rescore entries that already have iris")
    args = ap.parse_args()

    print("[backfill] loading verified pool …", flush=True)
    _, row_pvecs, _ = build_discovery_table()
    print(f"[backfill] verified pool: {len(row_pvecs)} p-vector(s)", flush=True)

    data = _load_raw_dataset(args.source)
    scored = 0
    skipped_have = 0
    failed = 0
    for bucket in ("unsolved", "failed", "proved"):
        for entry in data.get(bucket, []):
            name = entry.get("name")
            formula = entry.get("formula")
            if not (name and formula):
                continue
            if entry.get("iris") and not args.recompute:
                skipped_have += 1
                continue
            iris = compute_iris(ConjectureSpec(name=name, formula=formula),
                                row_pvecs)
            if iris is None:
                failed += 1
                continue
            print(f"[backfill] {name}: T={iris['T']:.3f} R={iris['R']:.3f} "
                  f"L={iris['L']:.3f}  TRL={iris['sort_keys']['TRL']:.4f}  "
                  f"support={iris['support']} touch={iris['touch']}", flush=True)
            entry["iris"] = iris
            scored += 1

    print(f"\n[backfill] scored {scored}, skipped {skipped_have} (already had "
          f"iris), failed {failed}", flush=True)

    if args.dry_run:
        print("[backfill] dry-run: not writing")
        return 0

    if scored:
        _write_raw_dataset(data, args.source)
        print("[backfill] wrote conjectures.json")
    return 0


if __name__ == "__main__":
    sys.exit(main())
