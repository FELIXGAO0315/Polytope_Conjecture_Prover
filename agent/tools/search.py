from __future__ import annotations

import json
import re
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path

from agent.tools.blueprint import BlueprintNode
from agent.tools.latex_parser import ParsedTheorem


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
    latex_hash: str
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
            "latex_hash": self.latex_hash,
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
            lean_file_path=d.get("lean_file_path", "Polib"),
            status=d["status"],
            sorry_count=d.get("sorry_count", 0),
            quality_score=d.get("quality_score", 0.0),
            saved_at=d.get("saved_at", ""),
            latex_hash=d.get("latex_hash", ""),
            mathlib_imports=d.get("mathlib_imports", []),
            polib_imports=d.get("polib_imports", []),
            description=d.get("description", ""),
        )


class PolibSearch:
    def __init__(self, store):
        """store: StoreManager instance (or None for empty search)."""
        self._store = store
        self._entries: list[SavedEntry] = []
        self._proved_entries: list[SavedEntry] = []
        self._vectorizer = None
        self._corpus_matrix = None
        self._load()

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
            return
        from sklearn.feature_extraction.text import TfidfVectorizer

        def _expand(node_id: str) -> str:
            return " ".join(re.findall(r"[A-Z][a-z]+", node_id))

        corpus = [
            f"{e.theorem_name} {e.node_id} {_expand(e.node_id)} {e.category} {e.description}"
            for e in proved
        ]
        self._vectorizer = TfidfVectorizer(stop_words="english")
        self._corpus_matrix = self._vectorizer.fit_transform(corpus)
        self._proved_entries = proved

    def _save(self) -> None:
        if self._store is not None:
            self._store.update("polib_index", [e.to_dict() for e in self._entries])

    def search(self, node: BlueprintNode, parsed: ParsedTheorem) -> SavedEntry | None:
        proved = getattr(self, '_proved_entries', None)
        if not proved or self._vectorizer is None or self._corpus_matrix is None:
            return None

        from sklearn.metrics.pairwise import cosine_similarity

        def _expand(node_id: str) -> str:
            return " ".join(re.findall(r"[A-Z][a-z]+", node_id))

        # Use node_id (expanded) + description so query vocabulary overlaps with corpus
        query = f"{node.node_id} {_expand(node.node_id)} {node.description}"
        try:
            q_vec = self._vectorizer.transform([query])
            scores = cosine_similarity(q_vec, self._corpus_matrix).flatten()
        except ValueError:
            return None

        best_idx = int(scores.argmax())
        if float(scores[best_idx]) < 0.65:
            return None

        return proved[best_idx]

    def search_by_text(self, query: str) -> list["SavedEntry"]:
        """Search entries by plain text substring match across name, node_id, and category.

        Falls back to this simple strategy when the TF-IDF vectoriser is not fitted
        (i.e. the index is empty). When the vectoriser IS fitted, also runs a
        TF-IDF cosine similarity search and merges results.
        """
        q = query.lower()

        # Always include substring matches
        matches: list[SavedEntry] = [
            e for e in self._entries
            if q in e.theorem_name.lower()
            or q in e.node_id.lower()
            or q in e.category.lower()
        ]

        # Also run TF-IDF search if available and query is long enough
        if self._vectorizer is not None and self._corpus_matrix is not None and len(q) > 3:
            try:
                from sklearn.metrics.pairwise import cosine_similarity
                q_vec = self._vectorizer.transform([query])
                scores = cosine_similarity(q_vec, self._corpus_matrix).flatten()
                for idx, score in enumerate(scores):
                    if float(score) >= 0.25:
                        candidate = self._entries[idx]
                        if candidate not in matches:
                            matches.append(candidate)
            except Exception:
                pass  # TF-IDF search is best-effort

        return matches

    def find_by_node_id(self, node_id: str) -> "SavedEntry | None":
        """Return the entry whose node_id exactly matches, or None."""
        for entry in self._entries:
            if entry.node_id == node_id:
                return entry
        return None

    def register(self, entry: SavedEntry) -> None:
        self._entries = [e for e in self._entries if e.node_id != entry.node_id]
        self._entries.append(entry)
        self._fit_vectorizer()
        self._save()


@dataclass
class LoogleResult:
    name: str
    signature: str
    docstring: str
    module: str

    def as_hint(self) -> str:
        return f"{self.name} : {self.signature}"


class LoogleSearch:
    """
    Searches Mathlib via the Loogle web API (https://loogle.lean-lang.org).
    Returns qualified Lean 4 identifier names usable as proof hints.
    """

    _API_URL = "https://loogle.lean-lang.org/json"

    def __init__(self, timeout: int = 15, max_results: int = 8):
        self._timeout = timeout
        self._max_results = max_results
        self._cache: dict[str, list[LoogleResult]] = {}

    def search(self, node: BlueprintNode) -> list[str]:
        """Return a list of hint strings for the given blueprint node."""
        queries = self._build_queries(node)
        seen: dict[str, str] = {}  # name -> hint string, dedup

        for q in queries:
            try:
                results = self._query(q)
                for r in results:
                    if r.name not in seen:
                        seen[r.name] = r.as_hint()
                    if len(seen) >= self._max_results:
                        break
            except Exception:
                continue
            if len(seen) >= self._max_results:
                break

        return list(seen.values())

    # Maps common math concepts → valid Mathlib theorem/definition identifiers.
    # Only include actual Lean identifiers (no tactics like linarith/ring/push_cast,
    # no bare namespaces like Finset/SimpleGraph/Int).
    _CONCEPT_MAP: dict[str, list[str]] = {
        "sum": ["Finset.sum_Ico_consecutive", "Finset.sum_union", "Finset.sum_le_sum"],
        "ico": ["Finset.sum_Ico_consecutive", "Finset.mem_Ico", "Finset.Ico_union_Ico_eq_Ico"],
        "interval": ["Finset.sum_Ico_consecutive", "Finset.Ico_union_Ico_eq_Ico"],
        "disjoint": ["Finset.disjoint_left", "Finset.sum_union"],
        "split": ["Finset.sum_Ico_consecutive", "Finset.sum_union"],
        "arithmetic": ["Finset.sum_Ico_consecutive", "Finset.sum_union", "Nat.add_le_add"],
        "infinite": ["Set.Infinite", "Set.infinite_univ"],
        "finite": ["Set.Finite", "Finset.finite_toSet"],
        "genus": ["Finset.sum_Ico_consecutive", "Int.add_comm"],
        "euler": ["Finset.sum_Ico_consecutive", "Int.add_comm"],
        "polygon": ["Finset.card", "SimpleGraph.edgeFinset"],
        "graph": ["SimpleGraph.edgeFinset", "SimpleGraph.degree"],
        "degree": ["SimpleGraph.degree", "SimpleGraph.card_neighborFinset_eq_degree"],
        "face": ["Finset.card", "SimpleGraph.edgeFinset"],
        "edge": ["SimpleGraph.edgeFinset", "SimpleGraph.degree"],
        "vertex": ["SimpleGraph.vertexFinset", "Finset.card"],
        "bound": ["Finset.sum_le_sum", "le_of_eq", "Nat.le_of_succ_le"],
        "inequality": ["le_trans", "add_le_add", "Nat.add_le_add"],
        "floor": ["Int.floor_nonneg", "Nat.div_le_self"],
        "integer": ["Int.toNat_of_nonneg", "Nat.cast_add", "Nat.cast_mul"],
        "cast": ["Nat.cast_add", "Nat.cast_mul", "Int.coe_nat_add"],
        "connected": ["SimpleGraph.Connected", "SimpleGraph.Preconnected"],
        "occupation": ["Finset.sum_le_sum", "Finset.mem_filter"],
        "hexagon": ["Finset.sum_Ico_consecutive", "Finset.sum_union"],
        "equation": ["Finset.sum_Ico_consecutive", "Nat.add_left_cancel", "Int.add_left_cancel"],
    }

    # Words to strip from node_id before building fallback queries
    _NODE_ID_PREFIXES = {"Lemma", "Def", "Thm", "Theorem", "Prop", "Corollary", "Claim"}

    def _build_queries(self, node: BlueprintNode) -> list[str]:
        """Build Lean-identifier-style Loogle queries from node description."""
        desc = node.description.lower()
        queries: list[str] = []

        # Map known concepts to Lean identifiers
        for concept, identifiers in self._CONCEPT_MAP.items():
            if concept in desc:
                queries.extend(identifiers)
                if len(queries) >= 6:
                    break

        # Fallback: search each meaningful CamelCase word from the node id
        # (skip generic prefix words like Lemma/Def/Thm)
        words = [w for w in re.findall(r"[A-Z][a-z]+", node.node_id)
                 if w not in self._NODE_ID_PREFIXES]
        for word in words[:3]:
            queries.append(word.lower())

        return list(dict.fromkeys(queries))  # dedup, preserve order

    def _query(self, q: str) -> list[LoogleResult]:
        if q in self._cache:
            return self._cache[q]

        url = f"{self._API_URL}?q={urllib.parse.quote(q)}"
        req = urllib.request.Request(url, headers={"User-Agent": "PolytopeFormalizerBot/1.0"})

        import time
        last_exc: Exception | None = None
        for attempt in range(3):
            try:
                with urllib.request.urlopen(req, timeout=self._timeout) as resp:
                    data = json.loads(resp.read().decode())
                break
            except Exception as exc:
                last_exc = exc
                if attempt < 2:
                    time.sleep(1.5 * (attempt + 1))
        else:
            raise last_exc  # type: ignore[misc]

        results: list[LoogleResult] = []
        # Loogle returns {"hits": [...], "count": N} or {"error": "..."}
        if "error" in data:
            self._cache[q] = results
            return results
        for hit in data.get("hits", [])[: self._max_results]:
            results.append(LoogleResult(
                name=hit.get("name", ""),
                signature=hit.get("type", ""),
                docstring=hit.get("doc", ""),
                module=hit.get("module", ""),
            ))
        self._cache[q] = results
        return results


# Keep MathlibSearch as an alias for backwards compatibility
class MathlibSearch(LoogleSearch):
    """Alias: MathlibSearch now delegates to LoogleSearch."""

    def __init__(self):
        super().__init__()


class GitHubLean4Search:
    """Search GitHub for existing Lean 4 formalizations similar to a given node.

    Uses the GitHub code search API to find .lean files on GitHub that contain
    similar mathematical content. Results are used as structural reference in
    the generation prompt — Claude should NOT copy them verbatim.
    """

    _API_URL = "https://api.github.com/search/code"

    # Maps mathematical concepts to GitHub search terms likely to find
    # relevant Lean 4 formalizations.
    _CONCEPT_MAP: dict[str, str] = {
        "independent":   "independentSet cycle Finset lean4 Mathlib",
        "occupation":    "occupation triangle face lean4 formalization",
        "cycle":         "SimpleGraph cycle card lean4 Mathlib",
        "floor":         "Nat.div floor half lean4 Mathlib",
        "quadrangle":    "quadrangle adjacency face lean4",
        "construction":  "infinite family exists induction lean4",
        "equality":      "equality case exists witness lean4 genus",
        "kgon":          "kgon polygon face lean4 Mathlib",
        "bound":         "Finset.card_le lean4 bound Mathlib",
        "induction":     "Nat.rec induction lean4 Mathlib formalization",
    }

    _PREFIX_STOP = {"Lemma", "Def", "Thm", "Theorem", "Prop", "Corollary"}

    def __init__(self, timeout: int = 10, max_results: int = 2):
        self._timeout = timeout
        self._max_results = max_results
        self._cache: dict[str, list[str]] = {}

    def search(self, node: "BlueprintNode") -> list[str]:
        """Return Lean 4 code snippets from GitHub relevant to this node."""
        queries = self._build_queries(node)
        snippets: list[str] = []

        for q in queries:
            if len(snippets) >= self._max_results:
                break
            try:
                results = self._query_github(q)
                snippets.extend(results)
            except Exception:
                continue

        return snippets[: self._max_results]

    def _build_queries(self, node: "BlueprintNode") -> list[str]:
        desc = node.description.lower()
        queries: list[str] = []

        for concept, search_terms in self._CONCEPT_MAP.items():
            if concept in desc or concept in node.node_id.lower():
                queries.append(search_terms)

        # Fallback: CamelCase words from node_id
        words = [
            w for w in re.findall(r"[A-Z][a-z]+", node.node_id)
            if w not in self._PREFIX_STOP
        ]
        if words:
            queries.append(" ".join(words[:3]) + " lean4 Mathlib")

        return list(dict.fromkeys(queries))

    def _query_github(self, query: str) -> list[str]:
        if query in self._cache:
            return self._cache[query]

        full_query = f"{query} language:lean"
        url = (
            f"{self._API_URL}?q={urllib.parse.quote(full_query)}"
            f"&per_page={self._max_results}"
        )
        req = urllib.request.Request(
            url,
            headers={
                "User-Agent": "PolytopeFormalizerBot/1.0",
                "Accept": "application/vnd.github+json",
            },
        )

        snippets: list[str] = []
        try:
            with urllib.request.urlopen(req, timeout=self._timeout) as resp:
                data = json.loads(resp.read().decode())

            for item in data.get("items", [])[: self._max_results]:
                raw_url = (
                    item.get("html_url", "")
                    .replace("github.com", "raw.githubusercontent.com")
                    .replace("/blob/", "/")
                )
                if not raw_url:
                    continue
                try:
                    with urllib.request.urlopen(raw_url, timeout=8) as r:
                        content = r.read().decode("utf-8", errors="replace")
                    snippet = self._extract_relevant(content, query)
                    if snippet.strip():
                        snippets.append(snippet)
                except Exception:
                    continue

        except Exception:
            pass

        self._cache[query] = snippets
        return snippets

    @staticmethod
    def _extract_relevant(content: str, query: str) -> str:
        """Extract up to 30 lines nearest to the first query keyword match."""
        lines = content.splitlines()
        keywords = [w.lower() for w in query.split() if len(w) > 4
                    and w.lower() not in {"lean4", "mathlib", "lean"}]

        best_line = 0
        for i, line in enumerate(lines):
            if any(kw in line.lower() for kw in keywords):
                best_line = i
                break

        start = max(0, best_line - 3)
        end = min(len(lines), best_line + 28)
        return "\n".join(lines[start:end])


class CombinedHintGenerator:
    """Single-call Mathlib hint generator.

    One Haiku LLM call produces both type-signature Loogle patterns and
    keyword/name search queries simultaneously.  All Loogle queries then
    run in parallel.  All returned names are real Mathlib identifiers
    (verified by coming directly from Loogle hits), so no post-validation
    step is required.

    Replaces the previous SmartMathLibHintGenerator + LoogleSearchHintGenerator pair.
    """

    LOOGLE_API = "https://loogle.lean-lang.org/json"

    _ANALYSIS_PROMPT = """\
You are a Lean 4 / Mathlib expert. Given a blueprint node from a formal proof,
generate Loogle search queries to find the Mathlib lemmas needed to prove it.

Node ID: {node_id}
Node type: {node_type}
Description: {description}
LaTeX fragment: {latex_fragment}

Task: Output ONLY a JSON object with three keys:

  "proof_class": one of
      "algebraic_identity"  | for pure ring/field equalities, sum rearrangements
      "arithmetic_bound"    | for inequalities involving floor, ceiling, div, mod
      "finset_sum"          | for Finset.sum manipulation, Ico splits, union sums
      "existence_witness"   | for ∃ statements needing an explicit construction
      "local_geometry"      | for adjacency, occupation, face/edge structure
      "casting"             | for ℕ → ℤ or ℤ → ℝ coercions in expressions
      "induction"           | for Nat.rec or structural induction proofs
      "other"               | anything not covered above

  "type_patterns": list of 3-6 Loogle type-signature PATTERNS using _ as wildcard.
    Each pattern describes the shape of the lemma type needed.
    NEVER write bare lemma names — always write type-signature patterns.
    Examples: "∑ _ ∈ Finset.Ico _ _, _ = _ + _"  "_ / 2 + (_ + 1) / 2 = _"
              "↑(∑ _ ∈ _, _) = ∑ _ ∈ _, ↑_"

  "keyword_queries": list of 3-5 partial lemma names or concept keyword strings.
    Used for name-fragment or keyword search.
    Examples: ["Finset.sum_Ico", "Int.floor_natCast", "floor div cast ℚ"]

Output ONLY valid JSON. No prose. No markdown fences.
Example:
{{"proof_class": "finset_sum", "type_patterns": ["∑ _ ∈ Finset.Ico _ _, _ = ∑ _ ∈ Finset.Ico _ _, _ + _", "∑ _ ∈ _, _ ≤ ∑ _ ∈ _, _"], "keyword_queries": ["Finset.sum_Ico", "sum_union disjoint"]}}
"""

    _FALLBACK: dict[str, list[str]] = {
        "algebraic_identity": [
            "Finset.sum_Ico_consecutive",
            "Nat.cast_sum", "push_cast", "ring",
        ],
        "arithmetic_bound": [
            "Nat.div_le_self", "Int.ediv_le_self",
            "Nat.floor_le", "Int.add_le_add",
        ],
        "finset_sum": [
            "Finset.sum_Ico_consecutive", "Finset.sum_union",
            "Finset.sum_le_sum", "Finset.disjoint_left",
        ],
        "existence_witness": [
            "exists_prop", "Set.infinite_univ",
        ],
        "local_geometry": [
            "Finset.card_le_card", "Finset.card_filter",
        ],
        "casting": [
            "Nat.cast_sum", "Nat.cast_mul", "Int.coe_nat_add",
            "push_cast", "norm_cast",
        ],
        "induction": [
            "Nat.rec", "Nat.le_induction", "Finset.induction_on",
        ],
        "other": [
            "Finset.sum_Ico_consecutive", "linarith", "omega",
        ],
    }

    def __init__(self, client: "Any", model: str = "claude-haiku-4-5-20251001",
                 timeout: int = 8, max_hints: int = 16):
        self._client = client
        self._model = model
        self._timeout = timeout
        self._max_hints = max_hints
        self._loogle = LoogleSearch()
        self._cache: dict[str, list[str]] = {}

    def generate(self, node: "BlueprintNode") -> list[str]:
        """One Haiku call + parallel Loogle queries → verified Mathlib hint list."""
        cache_key = node.node_id + "|" + node.description[:80]
        if cache_key in self._cache:
            return self._cache[cache_key]

        proof_class, type_patterns, keyword_queries = self._analyse_node(node)
        all_queries_type = type_patterns
        all_queries_kw = keyword_queries

        if not all_queries_type and not all_queries_kw:
            hints = self._FALLBACK.get(proof_class, self._FALLBACK["other"])
            self._cache[cache_key] = hints
            return hints

        hints: list[str] = []
        seen: set[str] = set()

        n_workers = max(1, len(all_queries_type) + len(all_queries_kw))
        with ThreadPoolExecutor(max_workers=n_workers) as _lex:
            futs = (
                [_lex.submit(self._query_type_pattern, q) for q in all_queries_type]
                + [_lex.submit(self._query_keyword, q) for q in all_queries_kw]
            )
            for fut in as_completed(futs):
                for item in (fut.result() or []):
                    if item not in seen:
                        seen.add(item)
                        hints.append(item)

        hints = hints[:self._max_hints]
        if not hints:
            hints = self._FALLBACK.get(proof_class, self._FALLBACK["other"])

        self._cache[cache_key] = hints
        return hints

    def _analyse_node(self, node: "BlueprintNode") -> tuple[str, list[str], list[str]]:
        """One Haiku call: classify proof + generate type patterns + keyword queries."""
        import json as _json
        import re as _re
        latex_safe = node.latex_fragment[:600].replace("{", "{{").replace("}", "}}")
        prompt = self._ANALYSIS_PROMPT.format(
            node_id=node.node_id,
            node_type=node.node_type,
            description=node.description,
            latex_fragment=latex_safe,
        )
        try:
            response = self._client.messages.create(
                model=self._model,
                max_tokens=320,
                messages=[{"role": "user", "content": prompt}],
                timeout=45,
            )
            text = response.content[0].text.strip()
            m = _re.search(r"\{.*\}", text, _re.DOTALL)
            if not m:
                raise ValueError("No JSON in response")
            data = _json.loads(m.group())
            proof_class = data.get("proof_class", "other")
            type_patterns = data.get("type_patterns", [])
            keyword_queries = data.get("keyword_queries", [])
            if not isinstance(type_patterns, list):
                type_patterns = []
            if not isinstance(keyword_queries, list):
                keyword_queries = []
            return proof_class, type_patterns[:6], keyword_queries[:5]
        except Exception:
            return "other", [], self._loogle.search(node)

    def _query_type_pattern(self, pattern: str) -> list[str]:
        """Query Loogle with a type-signature pattern; return hint strings."""
        try:
            results = self._loogle._query(pattern)
            return [r.as_hint() for r in results]
        except Exception:
            return []

    def _query_keyword(self, query: str) -> list[str]:
        """Query Loogle with a keyword/name fragment; return lemma name strings."""
        try:
            url = f"{self.LOOGLE_API}?q={urllib.parse.quote(query)}"
            req = urllib.request.Request(url, headers={"User-Agent": "FormalizerAgent/1.0"})
            with urllib.request.urlopen(req, timeout=self._timeout) as resp:
                data = json.loads(resp.read().decode())
            return [h["name"] for h in data.get("hits", []) if "name" in h][:6]
        except Exception:
            return []


class LLMProofReasoningHintGenerator:
    """
    Uses the main (Sonnet-class) LLM to reason through a proof and produce
    a concrete Lean 4 proof sketch.

    Unlike hint generators that produce lemma names, this generator:
    1. Reads all available Polib lemma signatures
    2. Asks the model to think step-by-step through the proof
    3. Returns a full proof sketch the code-generation model can follow

    Called as a last resort when Loogle-based hints yield < 3 usable lemmas.
    """

    _SYSTEM = (
        "You are an expert Lean 4 mathematician specializing in combinatorial "
        "geometry proofs. You reason carefully and produce concrete, compilable Lean 4 code."
    )

    _PROMPT = """\
A Lean 4 proof step failed because the automated system could not identify the \
right proof strategy. Your task: reason through the proof and produce a concrete sketch.

## Node to prove
Node ID: {node_id}
Type: {node_type}
Description: {description}
LaTeX: {latex_fragment}

## Locked goal signature (prove this EXACTLY — do not change names or types)
```lean
{goal_signature}
```

## Available Polib lemmas (use via `import Polib`, call by exact name)
```lean
{polib_signatures}
```

## Shared axioms (standalone lemmas — call WITHOUT dot-notation):
- `euler_formula maps` : `(v : ℤ) - e + ∑ k ∈ Ico 3 (m+1), p_i k = 2 - 2*g`
- `handshake maps`    : `2 * e = ∑ k ∈ Ico 3 (m+1), k * p_i k`
- `regularity maps`   : `3 * v = 2 * e`
- `kgon_occupation_bound maps k hk occupied h_mem` → `occupied.card ≤ k / 2`
- `quad_occ_reduction maps r hr h4 hr0 occupied h_mem` → `occupied.card ≤ r / 2 - 1`
- `equality_family maps n` → existence witness for the equality case

## Instructions
Think step by step:
1. What does the goal assert mathematically?
2. Which Polib lemma(s) directly establish the key fact? (name them exactly)
3. What `have` statements are needed to connect lemmas to the goal?
4. Which tactic closes the final goal: `linarith`, `omega`, `ring`, `simp`, etc.?

Then write the complete proof body — just the `by` block, not the lemma header:

```lean
  -- Step 1: ...
  have h1 := ExactLemmaName args
  -- Step 2: ...
  have h2 : ... := by ...
  -- Close:
  linarith [h1, h2]
```

Be specific: use exact Lean 4 identifiers. Prefer `linarith`/`omega` to close arithmetic goals.
Do NOT use `sorry` unless a sub-step is genuinely beyond the available axioms.
"""

    def __init__(self, client: "Any", polib_path: str):
        self._client = client
        self._polib_path = Path(polib_path)
        self._polib_sig_cache: str | None = None

    def generate(self, node: "BlueprintNode", goal_signature: str = "") -> list[str]:
        """Reason through the proof and return the sketch as a single hint string."""
        polib_sigs = self._read_polib_signatures()
        prompt = self._PROMPT.format(
            node_id=node.node_id,
            node_type=node.node_type,
            description=node.description,
            latex_fragment=node.latex_fragment[:600],
            goal_signature=goal_signature or "(not available)",
            polib_signatures=polib_sigs,
        )
        try:
            raw = self._client._call(prompt, system=self._SYSTEM, timeout=90)
            if raw and raw.strip():
                # Indent continuation lines so the bullet-list formatting in the
                # generation prompt stays readable.
                sketch = raw.strip().replace("\n", "\n    ")
                return [f"[proof-sketch by LLM reasoning]\n    {sketch}"]
        except Exception:
            pass
        return []

    _ASSESS_PROMPT = """\
A Lean 4 proof node was partially proved but still contains `sorry` placeholders. \
Assess whether it can now be completed given the available hints and lemmas.

## Node to complete
Node ID: {node_id}
Type: {node_type}
Description: {description}

## Goal signature
```lean
{goal_signature}
```

## Current partial proof (contains sorry)
```lean
{partial_code}
```

## Available hints / lemma names
{hints}

## Available Polib lemmas
```lean
{polib_signatures}
```

## Your task
1. Identify exactly which `sorry`(s) remain and what each one needs to prove.
2. Determine whether the available hints and Polib lemmas are sufficient to fill them.
3. Answer with EXACTLY one of:
   - `FEASIBLE` — you can write a concrete proof for every sorry
   - `INFEASIBLE` — critical lemmas or information are still missing

If FEASIBLE, immediately follow with the complete revised proof body (the `by` block only, \
no lemma header). If INFEASIBLE, give a one-sentence reason.

Format:
FEASIBLE
```lean
  <complete proof body>
```
or
INFEASIBLE: <reason>
"""

    def assess_and_sketch_partial(
        self,
        node: "BlueprintNode",
        partial_code: str,
        hints: list[str],
        goal_signature: str = "",
    ) -> tuple[bool, list[str]]:
        """Assess whether a partial (sorry-containing) proof can now be completed.

        Returns (feasible, sketch_hints) where sketch_hints is non-empty only when feasible.
        """
        polib_sigs = self._read_polib_signatures()
        hints_text = "\n".join(f"- {h}" for h in hints) if hints else "(none)"
        prompt = self._ASSESS_PROMPT.format(
            node_id=node.node_id,
            node_type=node.node_type,
            description=node.description,
            goal_signature=goal_signature or "(not available)",
            partial_code=partial_code[:1200],
            hints=hints_text,
            polib_signatures=polib_sigs,
        )
        try:
            raw = self._client._call(prompt, system=self._SYSTEM, timeout=60)
            if not raw:
                return False, []
            raw = raw.strip()
            if raw.startswith("FEASIBLE"):
                sketch = raw[len("FEASIBLE"):].strip()
                if sketch:
                    sketch = sketch.replace("\n", "\n    ")
                    return True, [f"[partial-completion sketch]\n    {sketch}"]
                return True, []
            return False, []
        except Exception:
            return False, []

    def _read_polib_signatures(self) -> str:
        """Extract lemma signatures (not full proofs) from Polib.lean."""
        if self._polib_sig_cache is not None:
            return self._polib_sig_cache
        polib_lean = self._polib_path / "Polib.lean"
        if not polib_lean.exists():
            return "(Polib.lean not found)"

        content = polib_lean.read_text(encoding="utf-8")
        marker_re = re.compile(r"^-- === (.+?) \(proved\)", re.MULTILINE)
        matches = list(marker_re.finditer(content))

        sections: list[str] = []
        for i, m in enumerate(matches):
            start = m.start()
            end = matches[i + 1].start() if i + 1 < len(matches) else len(content)
            section_text = content[start:end]
            sig_lines: list[str] = []
            for line in section_text.splitlines()[:30]:
                sig_lines.append(line)
                # Stop at the start of the proof body
                if ":= by" in line or line.rstrip().endswith(":= by"):
                    break
            sections.append("\n".join(sig_lines))

        result = "\n\n".join(sections) if sections else "(no proved lemmas)"
        self._polib_sig_cache = result
        return result
