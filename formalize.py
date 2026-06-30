"""Direct prover entry — go straight to the prover, skipping CE search.

Use this when you want to formalize a conjecture without running the full
``python -m run`` pipeline (which spends time on witness pool replay,
plantri enumeration, RL/Hopper/LLM counterexample search, etc).

Examples
--------
  python -m formalize C104              # single conjecture
  python -m formalize C1 C2 C3          # batch (sequential)
  python -m formalize C100-110          # range (inclusive)
  python -m formalize 104               # 'C' prefix is optional
  python -m formalize auto_..._104      # exact conjecture name

What this script does *not* do
------------------------------
Skips every CE-search stage of ``run.py``:

  • Stage 0  — witness pool / plantri pool replay
  • Stage 1  — random-walk CE search
  • Stage 2  — plantri exhaustive screen + parallel RL / Hopper / LLM tracks
  • Stage 2.5 — Inventory-LP entailment precheck (which can itself refute)

If you suspect a conjecture might be refutable, use ``python -m run``
instead — it will try CE search first and only fall through to the prover
if no CE is found.
"""
import re
import sys
from pathlib import Path

# Force line buffering so the prover's parallel-thread prints appear in
# real time (matches run.py's behaviour).
sys.stdout.reconfigure(line_buffering=True)
sys.stderr.reconfigure(line_buffering=True)

from agent.config import Config
from agent.conjectures import load_conjectures
from agent.orchestrator.tools.conjecture_parser import ParsedConjecture
from agent.prover.runner import formalize_conjecture


_PROJECT_ROOT = Path(__file__).resolve().parent
_CONJECTURES_JSON = _PROJECT_ROOT / "conjectures" / "conjectures.json"
_RANGE_RE = re.compile(r"^[cC]?(\d+)\s*-\s*[cC]?(\d+)$")


def _expand_range(token: str) -> list[str]:
    """``"C104-106"`` → ``["C104","C105","C106"]``.  Returns ``[token]`` if
    the token isn't a range."""
    m = _RANGE_RE.match(token)
    if not m:
        return [token]
    lo, hi = int(m.group(1)), int(m.group(2))
    if lo > hi:
        lo, hi = hi, lo
    return [f"C{i}" for i in range(lo, hi + 1)]


def _resolve_name(token: str, all_specs) -> str:
    """Resolve a short token (``"2"`` / ``"c2"``) to the full conjecture
    name (``"auto_20260310_142638_2"``) by matching the numeric suffix."""
    names = [s.name for s in all_specs]
    if token in names:
        return token
    suffix = token.lstrip("cC")
    candidates = [n for n in names if n.endswith(f"_{suffix}")]
    if len(candidates) == 1:
        return candidates[0]
    if len(candidates) > 1:
        print(f"Ambiguous token {token!r} matches: {candidates}")
        print("Please use the full name.")
        sys.exit(1)
    print(f"No conjecture found for {token!r}.")
    print(f"Available names: {names[:5]} …")
    sys.exit(1)


def main() -> None:
    if len(sys.argv) == 1:
        print(__doc__)
        sys.exit(0)

    raw_tokens = sys.argv[1:]
    tokens: list[str] = []
    for t in raw_tokens:
        expanded = _expand_range(t)
        if len(expanded) > 1:
            print(f"[formalize] expanded {t!r} → {expanded[0]}..{expanded[-1]} "
                  f"({len(expanded)} conjectures)")
        tokens.extend(expanded)

    specs = load_conjectures(str(_CONJECTURES_JSON))
    name_to_spec = {s.name: s for s in specs}

    names = [_resolve_name(t, specs) for t in tokens]
    print(f"[formalize] resolved {len(names)} conjecture(s): {list(zip(tokens, names))}")

    config = Config()
    failures: list[str] = []

    for idx, (token, name) in enumerate(zip(tokens, names), start=1):
        spec = name_to_spec[name]
        conjecture = ParsedConjecture.from_conjecture_spec(spec)
        print(f"\n[formalize] ({idx}/{len(names)}) {token!r} → {name!r}")
        try:
            status = formalize_conjecture(conjecture, config, tag="[formalize]")
            if status != "proved":
                failures.append(conjecture.conjecture_id)
        except KeyboardInterrupt:
            print(f"\n[formalize] interrupted on {name!r}; aborting batch.")
            raise
        except Exception as exc:
            print(f"[formalize] {name!r} raised {type(exc).__name__}: {exc}")
            failures.append(conjecture.conjecture_id)

    print()
    if failures:
        print(f"[formalize] {len(failures)}/{len(names)} did NOT reach 'proved': {failures}")
        sys.exit(1)
    print(f"[formalize] all {len(names)} conjecture(s) proved.")


if __name__ == "__main__":
    main()
