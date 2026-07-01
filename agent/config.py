from __future__ import annotations

import os
from dataclasses import dataclass, field
from pathlib import Path

from dotenv import load_dotenv

# Project root = directory containing this config.py's package (agent/), i.e. the repo root.
_PROJECT_ROOT = Path(__file__).resolve().parent.parent

# Load .env from the project root so it works regardless of CWD.
load_dotenv(_PROJECT_ROOT / ".env")


def _resolve_polib_path() -> Path:
    """Return an absolute polib path.

    POLIB_PATH env var is honoured when set.  A relative value is resolved
    against the project root (not CWD) so the output directory is always
    inside this project regardless of where the CLI is invoked from.
    """
    raw = os.environ.get("POLIB_PATH", "polib")
    p = Path(raw)
    if not p.is_absolute():
        p = _PROJECT_ROOT / p
    return p.resolve()


@dataclass
class Config:
    polib_path: Path = field(default_factory=_resolve_polib_path)
    store_path: Path = field(default_factory=lambda: _PROJECT_ROOT / "store.json")
    lake_binary: str = field(default_factory=lambda: os.environ.get("LAKE_BINARY", "lake"))
    max_rounds_per_node: int = field(default_factory=lambda: int(os.environ.get("MAX_ROUNDS_PER_NODE", "5")))
    max_node_retries: int = field(default_factory=lambda: int(os.environ.get("MAX_NODE_RETRIES", "4")))
    max_sorry_total: int = field(default_factory=lambda: int(os.environ.get("MAX_SORRY_TOTAL", "0")))
    # Default models target proof-quality, not throughput:
    # - main: Opus 4.7 for actual proof work (generation + fix loop). Sonnet 4.6
    #   was the previous default but lost too often on harder combinatorial proofs.
    # - fast: Sonnet 4.6 for peripheral structured work (hint generation, JSON
    #   decisions). Haiku 4.5 was the previous default but produced too many
    #   shallow / hallucinated lemma names downstream.
    # Override via MODEL_MAIN / MODEL_FAST env vars.
    model_main: str = field(
        default_factory=lambda: os.environ.get("MODEL_MAIN", "claude-opus-4-7")
    )
    model_fast: str = field(
        default_factory=lambda: os.environ.get("MODEL_FAST", "claude-sonnet-4-6")
    )
    compile_timeout_seconds: int = 180
    keep_temp_on_failure: bool = field(
        default_factory=lambda: os.environ.get("KEEP_TEMP_ON_FAILURE", "").lower() == "true"
    )
    max_parallel_nodes: int = field(default_factory=lambda: int(os.environ.get("MAX_PARALLEL_NODES", "6")))

    # proof_agent session knobs — passed straight into prove_node() per step 4 node.
    # Defaults are sized for hard combinatorial proofs (Opus + high effort + 80
    # turns + 25-minute timeout); each node can override the budget via env var.
    proof_agent_effort: str = field(
        default_factory=lambda: os.environ.get("PROOF_AGENT_EFFORT", "high")
    )
    proof_agent_max_turns: int = field(
        default_factory=lambda: int(os.environ.get("PROOF_AGENT_MAX_TURNS", "80"))
    )
    proof_agent_timeout_seconds: int = field(
        default_factory=lambda: int(os.environ.get("PROOF_AGENT_TIMEOUT", "1500"))
    )

    verbose: bool = True

    def __post_init__(self):
        if isinstance(self.polib_path, str):
            self.polib_path = Path(self.polib_path)
        # Always resolve to absolute so downstream code never depends on CWD.
        if not self.polib_path.is_absolute():
            self.polib_path = (_PROJECT_ROOT / self.polib_path).resolve()

    @classmethod
    def from_env(cls) -> "Config":
        return cls()
