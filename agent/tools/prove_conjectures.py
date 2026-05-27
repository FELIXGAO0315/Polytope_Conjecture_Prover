#!/usr/bin/env python3
"""Tool: prove a single conjecture (or a batch) with ProverAgent.

Usage
-----
# Prove one conjecture by ID from the IRIS file:
python prove_conjectures.py --tex conjectures/conjectures_without_ce.tex --id C2

# Prove a conjecture from a raw LaTeX statement (no tex file needed):
python prove_conjectures.py --statement '$p_6 \\geq 12 - 2p_4 - 3p_5$' --id C2

# Prove multiple IDs from a file:
python prove_conjectures.py --tex conjectures/conjectures_without_ce.tex --ids C2 C4 C7

# Prove multiple conjectures in parallel (max 3):
python prove_conjectures.py --tex conjectures/conjectures_without_ce.tex --ids C2 C4 C7 --workers 3

# Dry run — list parsed conjectures without proving:
python prove_conjectures.py --tex conjectures/conjectures_without_ce.tex --dry-run
"""
from __future__ import annotations

import argparse
import concurrent.futures
import sys
import threading
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent))

from agent.config import Config
from agent.prover_agent import ProverAgent
from agent.tools.conjecture_parser import ConjectureParser, ParsedConjecture

_print_lock = threading.Lock()


def _fmt_scores(c: ParsedConjecture) -> str:
    s = c.iris_scores
    if not s:
        return ""
    return f"T={s.get('T',0):.3f} R={s.get('R',0):.3f} L={s.get('L',0):.3f} IRIS={s.get('IRIS',0):.3f}"


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="Prove IRIS conjectures with ProverAgent.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )

    src = p.add_mutually_exclusive_group()
    src.add_argument(
        "--tex",
        metavar="PATH",
        help="LaTeX file containing the conjecture table.",
    )
    src.add_argument(
        "--statement",
        metavar="LATEX",
        help="Prove a single conjecture from a raw LaTeX statement string "
             "(requires --id to name it).",
    )

    p.add_argument(
        "--id",
        metavar="ID",
        help="Conjecture ID when using --statement, or shorthand for --ids with one value.",
    )
    p.add_argument(
        "--ids",
        nargs="+",
        metavar="ID",
        help="Prove only these conjecture IDs from the tex file (e.g. C2 C4 C7).",
    )
    p.add_argument(
        "--sort-iris",
        action="store_true",
        help="Sort conjectures by IRIS score (descending) before proving.",
    )
    p.add_argument(
        "--dry-run",
        action="store_true",
        help="List parsed conjectures and exit without proving.",
    )
    p.add_argument(
        "--category",
        default="Polytope",
        help="Polib category for proved lemmas (default: Polytope).",
    )
    p.add_argument(
        "--quiet",
        action="store_true",
        help="Suppress per-step verbose output from the agent.",
    )
    p.add_argument(
        "--workers",
        type=int,
        default=1,
        metavar="N",
        help="Number of conjectures to prove in parallel (default: 1, max: 3). "
             "Verbose output is suppressed when N > 1.",
    )

    args = p.parse_args()

    if args.workers > 3:
        p.error("--workers cannot exceed 3 (session-file conflicts above this limit)")
    if args.statement is None and args.tex is None:
        p.error("one of --tex or --statement is required")
    if args.statement is not None and args.id is None:
        p.error("--id is required when using --statement")
    if args.id and args.ids:
        p.error("--id and --ids are mutually exclusive")

    # Normalise: always use args.ids as the canonical list
    if args.id and not args.ids:
        args.ids = [args.id]

    return args


def _load_conjectures(args: argparse.Namespace) -> list[ParsedConjecture]:
    """Return the list of ParsedConjecture objects based on CLI args."""
    if args.statement:
        parser = ConjectureParser()
        conj = parser.parse_statement(args.statement, args.ids[0])
        return [conj]

    tex_path = Path(args.tex)
    if not tex_path.exists():
        print(f"[error] tex file not found: {tex_path}", file=sys.stderr)
        sys.exit(1)

    tex_source = tex_path.read_text(encoding="utf-8")
    parser = ConjectureParser()
    all_conjectures = parser.parse_file(tex_source)

    if not all_conjectures:
        print("[warn] No conjectures found in the file. Check the table format.")
        sys.exit(0)

    if args.ids:
        requested = set(args.ids)
        conjectures = [c for c in all_conjectures if c.conjecture_id in requested]
        missing = requested - {c.conjecture_id for c in conjectures}
        if missing:
            print(f"[warn] IDs not found in file: {sorted(missing)}", file=sys.stderr)
    else:
        conjectures = all_conjectures

    if args.sort_iris:
        conjectures = sorted(
            conjectures,
            key=lambda c: c.iris_scores.get("IRIS", 0.0),
            reverse=True,
        )

    return conjectures


def _prove_one(
    config: Config,
    conjecture: ParsedConjecture,
    category: str,
    index: int,
    total: int,
    verbose: bool,
) -> tuple[ParsedConjecture, object, float]:
    import random
    from agent.formalizer_agent import FormalizationResult

    time.sleep(index * 1.5 + random.uniform(0, 1.0))

    agent = ProverAgent(config)
    t0 = time.perf_counter()
    try:
        result = agent.prove_conjecture(conjecture, category=category, verbose=verbose)
    except Exception as exc:
        result = FormalizationResult(
            theorem_name=conjecture.conjecture_id,
            status="failed",
            nodes_proved=[],
            nodes_partial=[],
            nodes_failed=[],
            total_sorry_count=0,
            error=str(exc),
            dep_graph_path="",
            session_state_path="",
        )
    elapsed = time.perf_counter() - t0

    status_icon = {"success": "✓", "partial": "~", "failed": "✗"}.get(result.status, "?")
    with _print_lock:
        sep = "=" * 60
        print(f"\n{sep}")
        print(f"[{index}/{total}] {conjecture.conjecture_id}  {_fmt_scores(conjecture)}")
        print(f"  {conjecture.statement_latex[:120]}")
        print()
        print(f"  {status_icon} {result.status.upper()}  ({elapsed:.1f}s)")
        print(f"    proved : {result.nodes_proved}")
        print(f"    partial: {result.nodes_partial}")
        print(f"    failed : {result.nodes_failed}")
        print(f"    sorrys : {result.total_sorry_count}")
        if result.error:
            print(f"    error  : {result.error[:200]}")

    return conjecture, result, elapsed


def main() -> None:
    args = parse_args()
    conjectures = _load_conjectures(args)

    workers = max(1, args.workers)
    if args.statement:
        print(f"[info] mode     : single statement")
        print(f"[info] id       : {conjectures[0].conjecture_id}")
    else:
        print(f"[info] tex file : {args.tex}")
        print(f"[info] to prove : {len(conjectures)}")
    if workers > 1:
        print(f"[info] workers  : {workers} (parallel)")
    print()

    if args.dry_run:
        for c in conjectures:
            print(f"  {c.conjecture_id:6s}  {_fmt_scores(c)}")
            print(f"         hypotheses : {c.hypotheses}")
            print(f"         conclusion : {c.conclusion[:100]}")
        return

    config = Config.from_env()
    verbose = (not args.quiet) and (workers == 1)

    results: list[tuple[ParsedConjecture, object]] = []
    proved, partial, failed = 0, 0, 0

    if workers == 1:
        for i, conjecture in enumerate(conjectures, 1):
            sep = "=" * 60
            print(f"\n{sep}")
            print(f"[{i}/{len(conjectures)}] {conjecture.conjecture_id}  {_fmt_scores(conjecture)}")
            print(f"  {conjecture.statement_latex[:120]}")
            print()

            _, result, elapsed = _prove_one(
                config, conjecture, args.category, i, len(conjectures), verbose
            )
            results.append((conjecture, result))

            if result.status == "success":
                proved += 1
            elif result.status == "partial":
                partial += 1
            else:
                failed += 1
    else:
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
            future_to_conj = {
                pool.submit(
                    _prove_one,
                    config, c, args.category, i + 1, len(conjectures), False,
                ): c
                for i, c in enumerate(conjectures)
            }
            ids_running = [c.conjecture_id for c in conjectures]
            batch_size = min(workers, len(ids_running))
            print(f"[running] first batch: {', '.join(ids_running[:batch_size])} (waiting for results...)\n")
            completed = 0
            for future in concurrent.futures.as_completed(future_to_conj):
                conjecture, result, _ = future.result()
                completed += 1
                results.append((conjecture, result))
                if result.status == "success":
                    proved += 1
                elif result.status == "partial":
                    partial += 1
                else:
                    failed += 1
                remaining = len(conjectures) - completed
                if remaining > 0:
                    with _print_lock:
                        print(f"  [progress] {completed}/{len(conjectures)} done, {remaining} still running...")

    if len(conjectures) > 1:
        print(f"\n{'=' * 60}")
        print("SUMMARY")
        print(f"  proved : {proved}")
        print(f"  partial: {partial}")
        print(f"  failed : {failed}")
        print(f"  total  : {len(results)}")
        print()
        if proved + partial > 0:
            print("Conjectures with at least partial proof:")
            id_to_result = {c.conjecture_id: r for c, r in results}
            for c in conjectures:
                r = id_to_result.get(c.conjecture_id)
                if r and r.status in ("success", "partial"):
                    icon = "✓" if r.status == "success" else "~"
                    print(f"  {icon} {c.conjecture_id}  ({r.status})")


if __name__ == "__main__":
    main()
