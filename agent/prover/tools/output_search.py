from __future__ import annotations

import re
from pathlib import Path

from agent.prover.tools.blueprint import BlueprintNode

# ---------------------------------------------------------------------------
# Keyword helpers
# ---------------------------------------------------------------------------

def _camel_keywords(name: str) -> set[str]:
    """Split a CamelCase identifier into lowercase words, dropping short ones.

    Examples:
      HexagonEdgesLowerBound → {'hexagon', 'edges', 'lower', 'bound'}
      BasePVectorEquation    → {'base', 'vector', 'equation'}
    """
    words = re.findall(
        r'[A-Z][a-z]+|[A-Z]{2,}(?=[A-Z][a-z]|$)|[A-Z](?=[a-z])|[a-z]+',
        name,
    )
    return {w.lower() for w in words if len(w) > 2}


_STOPWORDS: frozenset[str] = frozenset({
    # English
    "the", "and", "for", "that", "with", "this", "from", "into", "each",
    "which", "are", "has", "its", "any", "all", "was", "not", "one", "two",
    "can", "bounds", "bound",
    # Lean / math jargon so common they add no signal
    "lean", "mathlib", "lemma", "theorem", "proof", "def", "fun",
    "let", "have", "show", "case", "exact", "apply", "intro",
})


def _desc_keywords(description: str) -> set[str]:
    """Extract meaningful lowercase words from a prose description."""
    words = re.findall(r'\b[A-Za-z]{4,}\b', description)
    return {w.lower() for w in words} - _STOPWORDS


# ---------------------------------------------------------------------------
# OutputSearch
# ---------------------------------------------------------------------------

class OutputSearch:
    """Find compiled-OK Lean files in output/Output/ that are relevant to a node.

    Relevance score (higher = more relevant):
      name_overlap  × 2.0   — CamelCase keywords shared between node_id and filename
      desc_overlap  × 0.5   — description keywords shared with filename keywords
      content_hits  × 0.2   — all query keywords found anywhere in file content (capped 5)

    A file must share at least one name keyword to be considered at all.
    Only files with the ``-- compile: OK`` header are eligible.
    """

    def __init__(self, output_root: Path) -> None:
        self._output_dir = output_root / "Output"

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def find_references(
        self,
        node: BlueprintNode,
        max_results: int = 2,
        max_chars_per_file: int = 3000,
    ) -> list[str]:
        """Return formatted reference snippets for injection into LLM prompts.

        Each snippet is a string:
            -- [SomeFile.lean]  (score=4.2)
            <file body, stripped of auto-generated header>

        Returns an empty list if the output directory does not exist or no
        relevant compiled files are found.
        """
        if not self._output_dir.exists():
            return []

        name_kws = _camel_keywords(node.node_id) - _STOPWORDS
        desc_kws = _desc_keywords(node.description)
        all_kws  = name_kws | desc_kws

        if not all_kws:
            return []

        scored: list[tuple[float, Path, str]] = []

        for lean_file in self._output_dir.glob("*.lean"):
            if lean_file.stem == node.node_id:
                continue  # skip self

            try:
                content = lean_file.read_text(encoding="utf-8", errors="ignore")
            except OSError:
                continue

            if "-- compile: OK" not in content:
                continue  # only proved files

            file_kws = _camel_keywords(lean_file.stem) - _STOPWORDS

            name_overlap = len(name_kws & file_kws)
            if name_overlap == 0:
                continue  # must share at least one name keyword

            desc_overlap  = len(desc_kws & file_kws)
            content_lower = content.lower()
            content_hits  = min(5, sum(1 for kw in all_kws if kw in content_lower))

            score = name_overlap * 2.0 + desc_overlap * 0.5 + content_hits * 0.2
            scored.append((score, lean_file, content))

        if not scored:
            return []

        scored.sort(key=lambda t: -t[0])

        results: list[str] = []
        for score, path, content in scored[:max_results]:
            body = self._clean_body(content)
            if len(body) > max_chars_per_file:
                body = body[:max_chars_per_file] + "\n-- ... [truncated]"
            results.append(
                f"-- [{path.name}]  (relevance score: {score:.1f})\n{body}"
            )

        return results

    # ------------------------------------------------------------------
    # Internal helpers
    # ------------------------------------------------------------------

    @staticmethod
    def _clean_body(content: str) -> str:
        """Strip auto-generated header lines and deduplicate import lines."""
        lines = content.splitlines()

        # Drop the three auto-generated comment lines at the top
        body: list[str] = []
        for line in lines:
            s = line.strip()
            if (s.startswith("-- Output/")
                    or s.startswith("-- generated_at:")
                    or s.startswith("-- compile:")):
                continue
            body.append(line)

        # Deduplicate import lines (keep first occurrence)
        seen_imports: set[str] = set()
        deduped: list[str] = []
        for line in body:
            s = line.strip()
            if s.startswith("import "):
                if s in seen_imports:
                    continue
                seen_imports.add(s)
            deduped.append(line)

        return "\n".join(deduped).strip()
