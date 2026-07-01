from __future__ import annotations

import hashlib
from dataclasses import dataclass


@dataclass
class ParsedTheorem:
    """JSON-conjecture view consumed by the prover pipeline.

    ``content_hash`` is the cache key for goal/blueprint stores — a sha256
    of ``name + hypotheses + conclusion``.
    """
    name: str
    hypotheses: list[str]
    conclusion: str
    content_hash: str

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "hypotheses": self.hypotheses,
            "conclusion": self.conclusion,
            "content_hash": self.content_hash,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "ParsedTheorem":
        return cls(
            name=d["name"],
            hypotheses=d["hypotheses"],
            conclusion=d["conclusion"],
            content_hash=d["content_hash"],
        )


def _sha256(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()
