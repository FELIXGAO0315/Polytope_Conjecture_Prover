"""End-to-end prover runner for a single conjecture.

This is the **prover-side dispatcher** — given a ``ParsedConjecture``, it
wires up everything needed to actually invoke the prover and returns the
final status string.  Wraps:

1. Ensure Polib's ``.olean`` cache is built (one-shot ``lake build`` if
   missing).  All downstream lake calls in the pipeline assume the cache
   exists.
2. Construct ``ProverAgent`` from a Config.
3. Override ``_proof_subdir`` so the output file lands in
   ``output/conjecture_without_ce/`` (the conjecture-mode convention)
   instead of ``output/complete_proof/`` (LaTeX-mode default).
4. Call ``agent.prove_conjecture(conjecture)`` which runs the 8-stage
   pipeline (see ``agent/prover/pipeline.py``).
5. Print a one-line summary and return ``"proved"`` / ``"failed"``.

Shared by two callers:

* ``formalize.py`` (project root) — the ``python -m formalize`` CLI for
  running the prover directly on a conjecture, **skipping** CE search.
* ``Orchestrator._run_prover`` — Stage 3 of the full ``python -m run``
  pipeline, called only after CE search has come up empty.

Both routes converge here so the prover-invocation logic exists in
exactly one place.
"""
from __future__ import annotations

import subprocess
from pathlib import Path
from typing import TYPE_CHECKING

from agent.config import Config

if TYPE_CHECKING:
    from agent.orchestrator.tools.conjecture_parser import ParsedConjecture


def ensure_polib_built(config: Config) -> None:
    """Pre-build the ``Polib`` lake target so its ``.olean`` cache is on disk.

    Fast no-op when the cache already exists.  Required before any prover
    run because every per-node compile in the pipeline does ``lake build``
    against Polib — a cold cache would force a full rebuild on the first
    node and timeout.
    """
    polib_path = Path(config.polib_path)
    olean = polib_path / ".lake" / "build" / "lib" / "lean" / "Polib.olean"
    if olean.exists():
        return
    print("[Prover] Building Polib cache (first-time setup) …")
    try:
        from agent.procutil import set_pdeathsig
    except ImportError:
        set_pdeathsig = None
    result = subprocess.run(
        [config.lake_binary, "build", "Polib"],
        cwd=polib_path,
        capture_output=False,
        timeout=600,
        preexec_fn=set_pdeathsig if set_pdeathsig else None,
    )
    if result.returncode == 0:
        print("[Prover] Polib cache ready.")
    else:
        print(f"[Prover] Warning: lake build Polib exited {result.returncode}")


def formalize_conjecture(
    conjecture: "ParsedConjecture",
    config: Config | None = None,
    tag: str = "[Prover]",
) -> str:
    """Run the prover end-to-end on a single ``ParsedConjecture``.

    Returns ``"proved"`` if the conjecture was fully formalized with zero
    sorry, ``"failed"`` otherwise.

    Side effects:

    * Writes the assembled proof to
      ``output/conjecture_without_ce/{conjecture_id}.lean`` (success path).
    * Appends node sections to ``polib/Polib.lean`` and updates
      ``store.json`` as nodes are proved.

    ``tag`` lets callers tag log lines (e.g. ``"[Orchestrator]"`` when
    invoked from Stage 3 of the full pipeline).  Defaults to ``"[Prover]"``.
    """
    from agent.prover.agent import ProverAgent

    config = config or Config.from_env()
    ensure_polib_built(config)

    agent = ProverAgent(config)
    agent._proof_subdir = "conjecture_without_ce"

    print(f"\n{tag} starting for {conjecture.conjecture_id} …")
    try:
        result = agent.prove_conjecture(conjecture)
    except Exception as exc:
        print(f"{tag} raised: {exc}")
        raise

    if result.nodes_failed:
        print(f"  Failed nodes: {result.nodes_failed}")
    # Surface ProverAgent's internal error (caught by ``except Exception`` in
    # prove_conjecture).  Without this, silent failures during blueprint
    # decomposition or other early-stage exceptions are invisible.
    if getattr(result, "error", None):
        print(f"  [internal error] {result.error}")
    print(f"\n{tag} Done. Result: {result.status}")
    return "proved" if result.status == "success" else "failed"
