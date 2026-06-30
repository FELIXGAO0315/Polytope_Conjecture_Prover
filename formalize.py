"""Shim — keeps the short `python -m formalize C104` invocation working.

Real implementation lives in ``agent/prover/formalize.py`` alongside the
rest of the prover module.  This file just re-exposes ``main`` so the
top-level module name ``formalize`` resolves.
"""
from agent.prover.formalize import main

if __name__ == "__main__":
    main()
