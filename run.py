"""
Entry point shortcut.

  python -m run              # batch: all conjectures in conjectures/conjectures.json
  python -m run 2            # single: conjecture whose name ends with '_2'
  python -m run c2           # same  (c prefix is optional, case-insensitive)
  python -m run auto_xxx_42  # single: exact name match
  python -m run C2 C3 C4 …   # sequential: run each named conjecture in order
  python -m run C104-122     # range: expands to C104 C105 … C122
  python -m run project      # evolution loop: generate → CE search → prover;
                             # outcomes feed the next generation via
                             # conjectures.json (extra flags are forwarded,
                             # e.g. python -m run project --rl-episodes 50)
"""
import re
import sys

# When stdout is a pipe (e.g. `python -m run 1 | tee log`), Python switches to
# 8KB block buffering: finder-process prints sit invisible in the buffer until
# the process exits. Force line buffering before any child process is forked.
sys.stdout.reconfigure(line_buffering=True)
sys.stderr.reconfigure(line_buffering=True)

from agent.orchestrator.orchestrator import Orchestrator, _PROJECT_ROOT
from agent.conjectures import load_conjectures, reconcile_from_artifacts


_RANGE_RE = re.compile(r"^[cC]?(\d+)\s*-\s*[cC]?(\d+)$")


def _expand_range(token: str) -> list[str]:
    """Expand a range token like 'C104-122' or '5-9' into a list of single
    tokens. Returns [token] if not a range."""
    m = _RANGE_RE.match(token)
    if not m:
        return [token]
    lo, hi = int(m.group(1)), int(m.group(2))
    if lo > hi:
        lo, hi = hi, lo
    return [f"C{i}" for i in range(lo, hi + 1)]


def _resolve_name(token: str) -> str:
    """Resolve a short token (e.g. '2', 'c2') to a full conjecture name."""
    specs = load_conjectures(str(_PROJECT_ROOT / "conjectures" / "conjectures.json"))
    names = [s.name for s in specs]

    # exact match first
    if token in names:
        return token

    # strip leading 'c'/'C' to get the numeric suffix
    suffix = token.lstrip("cC")

    # match legacy `auto_…_<suffix>` names AND the new bare `C<suffix>` shape
    candidates = [n for n in names
                  if n.endswith(f"_{suffix}") or n.lower() == f"c{suffix}"]
    if len(candidates) == 1:
        return candidates[0]
    if len(candidates) > 1:
        print(f"Ambiguous token {token!r} matches: {candidates}")
        print("Please use the full name.")
        sys.exit(1)

    print(f"No conjecture found for {token!r}.")
    print(f"Available names: {names[:5]} ...")
    sys.exit(1)


def _reconcile() -> None:
    """Fold on-disk CE/proof artifacts into conjectures.json — the single
    shared implementation (same one the conjecture generator runs before
    deriving its prompt signals). Wrapped so a sync failure never kills a
    batch."""
    try:
        reconcile_from_artifacts()
    except Exception as exc:
        print(f"[run] warning: status reconcile failed: {exc}")
    # End-of-run scratch cleanup: Lake's content-cache only helps within a
    # run's fix loops; leftover _Temp sources + oleans are pure disk weight.
    try:
        from agent.prover.tools.lean_compiler import wipe_temp_scratch
        n = wipe_temp_scratch()
        if n:
            print(f"[run] wiped {n} Polib/_Temp scratch file(s)")
    except Exception as exc:
        print(f"[run] warning: scratch cleanup failed: {exc}")


def main() -> None:
    if len(sys.argv) > 1 and sys.argv[1].lower() in ("project", "loop"):
        from agent.orchestrator.evolution_loop import main as loop_main
        sys.argv = [sys.argv[0]] + sys.argv[2:]   # forward remaining flags
        loop_main()
        return

    orch = Orchestrator()

    if len(sys.argv) == 1:
        try:
            orch.run_batch()
        finally:
            _reconcile()
        return

    # Expand range tokens (e.g. C104-122 → C104 C105 … C122) before resolving.
    raw_tokens = sys.argv[1:]
    tokens: list[str] = []
    for t in raw_tokens:
        expanded = _expand_range(t)
        if len(expanded) > 1:
            print(f"[run] expanded range {t!r} → {expanded[0]}..{expanded[-1]} "
                  f"({len(expanded)} conjectures)")
        tokens.extend(expanded)

    names = [_resolve_name(t) for t in tokens]
    print(f"[run] Resolved {len(tokens)} token(s): {list(zip(tokens, names))}")

    processed = []  # (name, ParsedConjecture) — for the cleanup sweep
    try:
        for idx, (token, name) in enumerate(zip(tokens, names), start=1):
            print(f"\n[run] ({idx}/{len(names)}) {token!r} → {name!r}")
            try:
                conjecture = orch._load_conjecture(name)
                orch.run(conjecture)
                processed.append((name, conjecture))
            except KeyboardInterrupt:
                print(f"[run] Interrupted on {name!r}; aborting remaining batch.")
                raise
            except Exception as exc:
                print(f"[run] {name!r} failed: {type(exc).__name__}: {exc}")
                print(f"[run] continuing with next conjecture …")

        # Witness pool re-sweep over the run's still-undecided conjectures:
        # any CE persisted later in this run may refute one that failed
        # earlier. Cheap (≤1 s/conjecture, same 5-check gate). Skipped for
        # single-conjecture runs.
        if len(processed) >= 2:
            undecided = [c for _, c in processed
                         if not (orch._ce_dir / c.short_id / f"{c.short_id}.json").exists()]
            if undecided:
                orch._witness_pool_resweep(undecided, tag="[run]")
    finally:
        # One reconcile covers every outcome above (including re-sweep CEs
        # and a Ctrl-C mid-batch) — artifacts on disk are the truth source.
        _reconcile()


if __name__ == "__main__":
    main()
