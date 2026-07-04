"""Pure Lean-source utility functions.

Extracted from FormalizerAgent's @staticmethods so they can be tested in
isolation and so agent.py shrinks.  Nothing here touches ``self``; if you
need agent state, this is the wrong module.

v3.5-plus cleanup: the declaration-manipulation / markdown-stripping /
error-formatting helpers that served the legacy ``_generate_lean`` fix loop
were deleted with zero external references; ``has_sorry`` and
``face_count_tokens`` are the surviving API.
"""
from __future__ import annotations

import re

_SORRY_RE = re.compile(r"\bsorry\b")


def has_sorry(code: str) -> bool:
    """Return True if code contains any sorry tactic (not in comments)."""
    for line in code.splitlines():
        if line.strip().startswith("--"):
            continue
        if _SORRY_RE.search(line):
            return True
    return False


def face_count_tokens(name: str) -> set[str]:
    """Extract face-count references like P3, P4, P5, P6 from a node_id.

    Used as a fuzzy-match discriminator: if planner's ``C104_P6HigherFacesBound``
    TF-IDF-matches ``C104_P3LowerBound`` (because the planner's description
    literally mentions the proved lemma name), the cosine score is high but
    they're SEMANTICALLY DIFFERENT — one bounds p_6, the other bounds p_3.
    Comparing the ``{P3, P4, ...}`` token sets catches this:
    ``{P6} ∩ {P3} = ∅`` → reject the false alias.  Returns empty set for
    structural names like "Equality" or "Combine" (no face-count tokens) —
    those cases skip this check.
    """
    tokens: set[str] = set()
    for piece in name.split("_"):
        m = re.match(r"P(\d{1,2})(?=[A-Z]|$)", piece)
        if m and 3 <= int(m.group(1)) <= 12:
            tokens.add(f"P{m.group(1)}")
    return tokens
