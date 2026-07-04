"""Polib index + fuzzy search.

What's left here after the legacy hint-generator cleanup:

* ``SavedEntry``   — one row of the per-node Polib catalogue
                     (persisted in ``store.json:polib_index``).
* ``PolibSearch``  — exact + fuzzy (TF-IDF) lookup over saved entries,
                     with an alias map so the planner's blueprint names
                     can resolve to the real Polib lemma names.

All Mathlib / GitHub / Loogle / LLM-hint-generator classes that used to
live here (``LoogleSearch``, ``MathlibSearch``, ``GitHubLean4Search``,
``CombinedHintGenerator``, ``LLMProofReasoningHintGenerator``) were
retired together with the legacy fix-loop in ``_generate_lean``.  The
new proof_agent does its own Grep/Read of Inventory + Polib + Mathlib
inside its session and no longer relies on pre-computed hints.
"""
from __future__ import annotations

import re
import threading
from dataclasses import dataclass

from agent.prover.tools.blueprint import BlueprintNode
from agent.prover.tools.parsed_theorem import ParsedTheorem


@dataclass
class SavedEntry:
    node_id: str
    theorem_name: str
    category: str
    lean_file_path: str
    status: str  # "proved" | "partial" | "pending"
    sorry_count: int
    quality_score: float
    saved_at: str
    mathlib_imports: list[str]
    polib_imports: list[str]
    description: str = ""

    def to_dict(self) -> dict:
        return {
            "node_id": self.node_id,
            "theorem_name": self.theorem_name,
            "category": self.category,
            "lean_file_path": self.lean_file_path,
            "status": self.status,
            "sorry_count": self.sorry_count,
            "quality_score": self.quality_score,
            "saved_at": self.saved_at,
            "mathlib_imports": self.mathlib_imports,
            "polib_imports": self.polib_imports,
            "description": self.description,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "SavedEntry":
        return cls(
            node_id=d["node_id"],
            theorem_name=d.get("theorem_name", d.get("node_id", "")),
            category=d.get("category", "Polytope"),
            lean_file_path=d.get("lean_file_path", "Inventory"),
            status=d["status"],
            sorry_count=d.get("sorry_count", 0),
            quality_score=d.get("quality_score", 0.0),
            saved_at=d.get("saved_at", ""),
            mathlib_imports=d.get("mathlib_imports", []),
            polib_imports=d.get("polib_imports", []),
            description=d.get("description", ""),
        )


class PolibSearch:
    """Exact + fuzzy search over the Polib catalogue.

    Public methods used by the pipeline:
      * ``find_by_node_id(node_id)``  — exact match, with alias fallback
      * ``search(node, parsed)``      — TF-IDF fuzzy match (cosine ≥ 0.65)
      * ``register_alias(planner, real)`` — record blueprint→polib name aliasing
      * ``register(entry)``           — append/replace an entry and persist
    """

    def __init__(self, store):
        """store: StoreManager instance (or None for empty search)."""
        self._store = store
        self._entries: list[SavedEntry] = []
        self._proved_entries: list[SavedEntry] = []
        self._vectorizer = None
        self._corpus_matrix = None
        self._alias_lock = threading.Lock()
        self._alias_map: dict[str, str] = {}
        self._load()

    # ------------------------------------------------------------------
    # Persistence + indexing
    # ------------------------------------------------------------------

    def _load(self) -> None:
        if self._store is None:
            self._entries = []
        else:
            raw = self._store.get("polib_index") or []
            self._entries = [SavedEntry.from_dict(e) for e in raw]
        self._fit_vectorizer()

    def _fit_vectorizer(self) -> None:
        # Only index fully proved entries — partial entries have sorrys and
        # must not be returned as skip candidates by search().
        proved = [e for e in self._entries if e.status == "proved"]
        if not proved:
            self._vectorizer = None
            self._corpus_matrix = None
            self._proved_entries = []
            return
        from sklearn.feature_extraction.text import TfidfVectorizer

        corpus = [
            f"{e.theorem_name} {e.node_id} {_expand_camel(e.node_id)} {e.category} {e.description}"
            for e in proved
        ]
        self._vectorizer = TfidfVectorizer(stop_words="english")
        self._corpus_matrix = self._vectorizer.fit_transform(corpus)
        self._proved_entries = proved

    def _save(self) -> None:
        if self._store is not None:
            self._store.update("polib_index", [e.to_dict() for e in self._entries])

    # ------------------------------------------------------------------
    # Lookup
    # ------------------------------------------------------------------

    def find_by_node_id(self, node_id: str) -> "SavedEntry | None":
        """Return the entry whose ``node_id`` exactly matches, with alias fallback.

        If the exact name misses but ``node_id`` was registered as a fuzzy
        alias (planner's blueprint name → real polib name via
        ``register_alias``), follow the alias and return that entry.
        """
        for entry in self._entries:
            if entry.node_id == node_id:
                return entry
        with self._alias_lock:
            real_name = self._alias_map.get(node_id)
        if real_name and real_name != node_id:
            for entry in self._entries:
                if entry.node_id == real_name:
                    return entry
        return None

    def search(self, node: BlueprintNode, parsed: ParsedTheorem) -> "SavedEntry | None":
        """Return the best fuzzy match for ``node`` among proved entries.

        Uses TF-IDF cosine similarity over (theorem_name + node_id + expanded
        CamelCase + category + description).  Returns None below a 0.65
        threshold (calibration kept from the original implementation).
        """
        proved = self._proved_entries
        if not proved or self._vectorizer is None or self._corpus_matrix is None:
            return None
        from sklearn.metrics.pairwise import cosine_similarity

        query = f"{node.node_id} {_expand_camel(node.node_id)} {node.description}"
        try:
            q_vec = self._vectorizer.transform([query])
            scores = cosine_similarity(q_vec, self._corpus_matrix).flatten()
        except ValueError:
            return None
        best_idx = int(scores.argmax())
        if float(scores[best_idx]) < 0.65:
            return None
        return proved[best_idx]

    # ------------------------------------------------------------------
    # Aliases + registration
    # ------------------------------------------------------------------

    def register_alias(self, planner_name: str, real_polib_name: str) -> None:
        """Record ``planner_name → real_polib_name`` so that future
        ``find_by_node_id(planner_name)`` calls return the real entry.

        Called by ``_process_node`` when fuzzy ``search()`` matches a different
        name.  This is what propagates the real Lean identifier into downstream
        prompts (otherwise the LLM is told the dep name is the planner's name
        but Polib.lean has the lemma under a different name → unknown-identifier
        compile error).

        Thread-safe: level-0/1 worker threads may register aliases in parallel.
        """
        if planner_name == real_polib_name:
            return
        with self._alias_lock:
            self._alias_map[planner_name] = real_polib_name

    def resolve_alias(self, planner_name: str) -> "str | None":
        """Return the real polib name registered for ``planner_name`` (or None).

        Step-6 deep check needs this: an alias-accepted node's saved code
        declares the REAL lemma name, so the drift check must look for that
        declaration, not the planner's blueprint name.
        """
        with self._alias_lock:
            return self._alias_map.get(planner_name)

    def register(self, entry: SavedEntry) -> None:
        """Append ``entry`` to the index (replacing any same-node_id entry) and persist."""
        self._entries = [e for e in self._entries if e.node_id != entry.node_id]
        self._entries.append(entry)
        self._fit_vectorizer()
        self._save()


def _expand_camel(node_id: str) -> str:
    """Split CamelCase ``node_id`` into space-separated word tokens.

    Helps TF-IDF cosine similarity match ``"P6InequalityBound"`` against a
    query mentioning ``"inequality bound"``.
    """
    return " ".join(re.findall(r"[A-Z][a-z]+", node_id))
