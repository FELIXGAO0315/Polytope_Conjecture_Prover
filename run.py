"""
Entry point shortcut.

  python -m run              # batch: all conjectures in conjectures/conjectures.json
  python -m run 2            # single: conjecture whose name ends with '_2'
  python -m run c2           # same  (c prefix is optional, case-insensitive)
  python -m run auto_xxx_42  # single: exact name match
  python -m run project      # evolution loop: generate → CE search → prover,
                             # hints feed the next generation (extra flags are
                             # forwarded, e.g. python -m run project --rl-episodes 50)
"""
import sys

# When stdout is a pipe (e.g. `python -m run 1 | tee log`), Python switches to
# 8KB block buffering: finder-process prints sit invisible in the buffer until
# the process exits. Force line buffering before any child process is forked.
sys.stdout.reconfigure(line_buffering=True)
sys.stderr.reconfigure(line_buffering=True)

from agent.orchestrator.orchestrator import Orchestrator, _PROJECT_ROOT
from agent.conjectures import load_conjectures


def _resolve_name(token: str) -> str:
    """Resolve a short token (e.g. '2', 'c2') to a full conjecture name."""
    specs = load_conjectures(str(_PROJECT_ROOT / "conjectures" / "conjectures.json"))
    names = [s.name for s in specs]

    # exact match first
    if token in names:
        return token

    # strip leading 'c'/'C' to get the numeric suffix
    suffix = token.lstrip("cC")

    # match names ending with '_<suffix>'
    candidates = [n for n in names if n.endswith(f"_{suffix}")]
    if len(candidates) == 1:
        return candidates[0]
    if len(candidates) > 1:
        print(f"Ambiguous token {token!r} matches: {candidates}")
        print("Please use the full name.")
        sys.exit(1)

    print(f"No conjecture found for {token!r}.")
    print(f"Available names: {names[:5]} ...")
    sys.exit(1)


def main() -> None:
    if len(sys.argv) > 1 and sys.argv[1].lower() in ("project", "loop"):
        from agent.orchestrator.evolution_loop import main as loop_main
        sys.argv = [sys.argv[0]] + sys.argv[2:]   # forward remaining flags
        loop_main()
        return

    orch = Orchestrator()

    if len(sys.argv) == 1:
        orch.run_batch()
    else:
        token = sys.argv[1]
        name = _resolve_name(token)
        print(f"[run] Resolved {token!r} → {name!r}")
        orch.run_from_name(name)


if __name__ == "__main__":
    main()
