"""CLI entry:  python -m agent.conjecture_generator [options]"""
import argparse

from agent.conjecture_generator.agent import ConjectureGenerator


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Discover new conjectures with Graffiti3 and register them "
                    "into conjectures/conjectures.json (deduplicated).")
    ap.add_argument("--limit", type=int, default=0,
                    help="max conjectures to accept (0 = keep all)")
    ap.add_argument("--mode", default="fast", choices=["fast", "standard", "deep"],
                    help="Graffiti3 mode (default: fast)")
    ap.add_argument("--no-quick", action="store_true",
                    help="disable Graffiti3 quick mode")
    ap.add_argument("--nonlinear", action="store_true",
                    help="also enable nonlinear stages (sqrt/log/poly/…)")
    ap.add_argument("--enable-sophie", action="store_true",
                    help="enable Sophie mining in Graffiti3")
    ap.add_argument("--dry-run", action="store_true",
                    help="discover and filter, but write nothing")
    args = ap.parse_args()

    ConjectureGenerator(
        limit=args.limit,
        g3_mode=args.mode,
        quick=not args.no_quick,
        linear_only=not args.nonlinear,
        enable_sophie=args.enable_sophie,
        dry_run=args.dry_run,
    ).run()


if __name__ == "__main__":
    main()
