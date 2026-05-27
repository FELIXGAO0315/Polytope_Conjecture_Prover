"""ProverAgent — attempts to prove unproven conjectures.

Architecture
------------
ProverAgent extends FormalizerAgent and reuses its entire pipeline
(goal extraction, compile-fix loop, Polib management, etc.).

The only differences from the standard formalizer are:

1. Input  — accepts a ParsedConjecture (or plain statement string) instead of
            a LaTeX document that already contains a proof.

2. Blueprint — uses ConjectureDecomposer, which prompts the LLM to *discover*
               a proof strategy rather than decompose an existing proof.

3. Entry point — prove_conjecture() / prove() wrap the input into a synthetic
                 LaTeX theorem block and call FormalizerAgent.formalize().
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import TYPE_CHECKING

from agent.config import Config
from agent.formalizer_agent import FormalizationResult, FormalizerAgent
from agent.tools.blueprint import (
    Blueprint,
    BlueprintDecomposer,
    BlueprintNode,
    _parse_blueprint_json,
    _topological_sort,
    _validate_blueprint_nodes,
)
from agent.tools.conjecture_parser import ConjectureParser, ParsedConjecture
from agent.tools.latex_parser import ParsedTheorem

if TYPE_CHECKING:
    pass


# ---------------------------------------------------------------------------
# Signature extraction + relevance ranking helpers
# ---------------------------------------------------------------------------

_SIG_DECL_START = re.compile(
    r"^(?:private\s+)?(?:lemma|theorem|def|abbrev)\s+(\w+)",
    re.MULTILINE,
)


def _extract_lean_signatures(polib_lean: Path) -> dict[str, str]:
    """Return {node_id: signature_text} by scanning Polib.lean.

    Extracts only the type signature (the part before ':= by' or ':='),
    capped at 200 chars so the prompt stays readable.
    """
    try:
        text = polib_lean.read_text(encoding="utf-8")
    except OSError:
        return {}
    sigs: dict[str, str] = {}
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        m = _SIG_DECL_START.match(lines[i])
        if m:
            name = m.group(1)
            collected: list[str] = []
            done = False
            for j in range(i, min(i + 6, len(lines))):
                line = lines[j]
                # Check for ':= by' first (proof tactic block)
                if ":= by" in line:
                    collected.append(line.split(":= by")[0])
                    done = True
                    break
                # Check for ':=' with something after it on the same line (inline body)
                if re.search(r":=\s*\S", line):
                    collected.append(re.split(r":=\s*\S", line)[0] + ":=")
                    done = True
                    break
                collected.append(line)
                # ':=' at end of line means body is on the next line — stop here
                if re.search(r":=\s*$", line):
                    done = True
                    break
            sigs[name] = " ".join(collected).strip()[:200]
            _ = done  # just consumed
        i += 1
    return sigs


def _camel_tokens(s: str) -> set[str]:
    """Split a CamelCase/underscore identifier into lowercase word tokens."""
    return {w.lower() for w in re.findall(r"[A-Z][a-z]+|[a-z]+|[0-9]+", s)}


_RANK_STOP = frozenset(
    {"maps", "the", "a", "an", "and", "or", "in", "of", "for", "is", "to",
     "with", "all", "let", "if", "then", "be", "by", "on", "at", "from"}
)


def _rank_lemmas_for_discovery(
    proved_lemmas: list[dict],
    theorem_name: str,
    hypotheses: list[str],
    conclusion: str,
    top_k: int = 12,
) -> tuple[list[dict], list[dict]]:
    """Return (top_k_relevant, rest) sorted by token overlap with the conjecture."""
    if not proved_lemmas:
        return [], []
    context_tokens = (
        _camel_tokens(theorem_name)
        | {w for w in re.findall(r"\w+", " ".join(hypotheses).lower())}
        | {w for w in re.findall(r"\w+", conclusion.lower())}
    ) - _RANK_STOP

    def _score(e: dict) -> int:
        text = f"{e.get('node_id', '')} {e.get('description', '')}"
        tokens = _camel_tokens(text) | {w for w in re.findall(r"\w+", text.lower())}
        return len(tokens & context_tokens)

    ranked = sorted(proved_lemmas, key=_score, reverse=True)
    return ranked[:top_k], ranked[top_k:]


# ---------------------------------------------------------------------------
# Discovery-mode blueprint prompt
# ---------------------------------------------------------------------------

DISCOVERY_BLUEPRINT_PROMPT = """\
You are a Lean 4 proof discovery expert working in the domain of combinatorial
polytope theory. Your task is to devise a proof strategy for the following
UNPROVEN conjecture and express it as a directed acyclic graph (DAG) of
blueprint nodes. There is no known proof — you must figure out how to prove
it from first principles using Lean 4 / Mathlib tactics and the Polib lemmas
listed below.

Conjecture name: {theorem_name}
Lean signature:  {lean_signature}
Hypotheses:
{hypotheses}
Conclusion: {conclusion}

## Domain context (simple 3-polytopes / maps on surfaces)
- Euler's formula for the sphere: v - e + f = 2
- Handshaking: 2e = sum_k k*p_k   (each face has k edges)
- Vertex-degree for simple polytopes: 2e = 3v
- p-vector constraint: sum_k p_k = f_2  (total face count)
- Dehn–Sommerville: sum_k (6-k)*p_k = 12  (for genus-0 simple maps)
- All p_k >= 0; only finitely many p_k are nonzero (captured by maps.m)
- The Lean structure is SimplyCon3ConnectedMap 0 (genus 0 = sphere for ALL IRIS
  conjectures). Fields: maps.p_i k (face counts), maps.v, maps.e, maps.m.
  NEVER use maps.f2 or maps.f_2 — those fields do not exist.
  f_2 (total face count) = ∑ k in Finset.Ico 3 (maps.m + 1), maps.p_i k.
  Do NOT add IsSimple, maps.simple, or any simplicity hypothesis — it is not defined.

## Polib lemmas (available via `import Polib`)
Two kinds are listed below:
- **proved** (no tag): fully verified, zero sorry — safe to depend on directly.
- **partial** (tagged `[partial — has sorry…]`): proof structure exists but incomplete.
  Use these for **structural reference** (understand the proof approach, reuse sub-steps),
  but do NOT add them as `dependencies` — treat them as inspiration, not axioms.

The most relevant lemmas are shown with their Lean signatures; others are listed
by name only. Use signatures to decide which lemma to call and how to apply it.
{available_lemmas}
For any node whose proof can directly call a **proved** lemma, say so explicitly
in the `description` field.

## Node structure
- Each auxiliary definition or lemma needed before the main result gets its own node.
- **Parallelism**: only add a dependency edge A→B when B's proof body will
  DIRECTLY call or apply A by name. Avoid speculative edges — unnecessary
  dependencies force sequential execution and slow things down.
- **Independence**: if two sub-lemmas don't use each other's results, leave
  them unconnected so they can run in parallel. For example, extracting the
  Euler relation and extracting the handshaking identity are independent; only
  the final combination node should depend on both.
- Node types: "def" | "lemma" | "theorem"
- Exactly ONE node must have "is_main_target": true.
- "latex_fragment": write a brief mathematical description of what this node
  states (no verbatim proof exists — summarise the sub-goal instead).

## CRITICAL — Node naming
All nodes live in a shared Polib namespace. You MUST prefix every new node
you define with the exact conjecture identifier: `{theorem_name}`.

  REQUIRED prefix: `{theorem_name}`
  BAD:   "InequalityBound"        ← no prefix, will collide
  BAD:   "P6InequalityBound"      ← wrong conjecture prefix
  GOOD:  "{theorem_name}InequalityBound"  ← correct

Exception: nodes that intentionally REUSE an existing Polib lemma listed above
must use that lemma's exact name unchanged.

## CRITICAL — Dependency rules
Add A as a dependency of B ONLY IF B's proof directly calls/applies A's result
or B's type mentions a type defined in A. When in doubt, omit the dependency.

## CRITICAL — Cross-theorem dependencies are FORBIDDEN
Dependencies must only reference node_ids defined WITHIN THIS blueprint.
Do NOT list a node_id from another theorem's blueprint (e.g. "C2_DehnSommerville"
for a C4 blueprint) — those lemmas are already available via `import Polib` and
must NOT appear as dependency entries. If you need a proved Polib lemma, just
reference it by name in the `description` field; leave `dependencies` empty for that edge.

Respond with ONLY valid JSON — no prose, no markdown fences.

{{
  "nodes": [
    {{
      "node_id": "CamelCaseUniqueId",
      "node_type": "def" | "lemma" | "theorem",
      "description": "One sentence: what this node proves or defines.",
      "latex_fragment": "Brief mathematical description of the sub-goal.",
      "dependencies": ["only_direct_deps_here"],
      "is_main_target": false
    }}
  ]
}}
"""


class ConjectureDecomposer(BlueprintDecomposer):
    """BlueprintDecomposer variant that uses the discovery-mode prompt."""

    def __init__(self, client, model: str, polib_lean: Path | None = None) -> None:
        super().__init__(client, model)
        self._polib_lean = polib_lean

    def decompose(
        self,
        parsed: ParsedTheorem,
        goal,
        proved_lemmas: list[dict] | None = None,
    ) -> Blueprint:
        locked_goal = goal.goal if hasattr(goal, "goal") else goal

        # Load Lean signatures once from Polib.lean (best-effort)
        sigs: dict[str, str] = {}
        if self._polib_lean is not None:
            sigs = _extract_lean_signatures(self._polib_lean)

        # Rank lemmas by relevance; show top-k with signatures, rest names-only
        all_lemmas: list[dict] = proved_lemmas or []
        top, rest = _rank_lemmas_for_discovery(
            all_lemmas,
            theorem_name=parsed.name,
            hypotheses=list(parsed.hypotheses),
            conclusion=parsed.conclusion,
        )

        def _fmt_entry(e: dict) -> str:
            line = f"  - `{e['node_id']}`"
            if e.get("description"):
                line += f": {e['description']}"
            sig = sigs.get(e["node_id"], "")
            if sig:
                line += f"\n    Lean: `{sig}`"
            return line

        if all_lemmas:
            avail_lines = [_fmt_entry(e) for e in top]
            if rest:
                rest_ids = ", ".join(f"`{e['node_id']}`" for e in rest)
                avail_lines.append(
                    f"  Also available (name only): {rest_ids}"
                )
            avail = "\n".join(avail_lines)
        else:
            avail = "  (none yet)"

        user_content = DISCOVERY_BLUEPRINT_PROMPT.format(
            theorem_name=parsed.name,
            lean_signature=locked_goal.lean_signature,
            hypotheses="\n".join(f"  - {h}" for h in parsed.hypotheses),
            conclusion=parsed.conclusion,
            available_lemmas=avail,
        )
        response = self._client.messages.create(
            model=self._model,
            max_tokens=2048,
            messages=[{"role": "user", "content": user_content}],
        )
        text = response.content[0].text.strip()
        nodes = _parse_blueprint_json(text)
        polib_ids = {e["node_id"] for e in (proved_lemmas or [])}
        _validate_blueprint_nodes(nodes, known_polib_ids=polib_ids)
        topo_order = _topological_sort(nodes)
        blueprint_data = json.dumps([n.to_dict() for n in nodes], sort_keys=True)
        blueprint_hash = hashlib.sha256(blueprint_data.encode()).hexdigest()
        return Blueprint(
            theorem_name=parsed.name,
            nodes=nodes,
            topo_order=topo_order,
            blueprint_hash=blueprint_hash,
        )


# ---------------------------------------------------------------------------
# ProverAgent
# ---------------------------------------------------------------------------

class ProverAgent(FormalizerAgent):
    """Attempts to prove unproven conjectures using the standard formalization
    pipeline but with a discovery-mode blueprint decomposer.

    Usage
    -----
    agent = ProverAgent(Config.from_env())

    # From a ParsedConjecture (parsed from the IRIS table):
    result = agent.prove_conjecture(conjecture)

    # From a raw statement string:
    result = agent.prove_statement(
        statement_latex="$p_6 \\geq -5\\sum_{k\\geq 7} p_k + 10$",
        conjecture_id="MyConj",
    )

    # From a ParsedTheorem already constructed elsewhere:
    result = agent.prove(parsed_theorem)
    """

    _proof_subdir: str = "conjecture_proof"  # output/conjecture_proof/ instead of complete_proof/

    def __init__(self, config: Config) -> None:
        super().__init__(config)
        # Replace the standard decomposer with the discovery-mode one.
        self._decomposer = ConjectureDecomposer(
            self._sdk_fast,
            config.model_fast,
            polib_lean=Path(config.polib_path) / "Polib.lean",
        )

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def prove_conjecture(
        self,
        conjecture: ParsedConjecture,
        category: str = "Polytope",
        verbose: bool = True,
    ) -> FormalizationResult:
        """Prove a ParsedConjecture (extracted from the IRIS table).

        Output is written to output/conjecture_proof/{conjecture_id}.lean.
        """
        # tex_path stem is used as the output filename; the file need not exist.
        tex_path = str(
            Path(__file__).resolve().parent.parent
            / "conjectures" / "individual"
            / f"{conjecture.conjecture_id}.tex"
        )
        parsed_theorem = conjecture.to_parsed_theorem()
        return self.formalize(
            conjecture._synth_latex(),
            category=category,
            verbose=verbose,
            tex_path=tex_path,
            parsed=parsed_theorem,
        )

    def prove_statement(
        self,
        statement_latex: str,
        conjecture_id: str = "Conjecture",
        category: str = "Polytope",
        verbose: bool = True,
    ) -> FormalizationResult:
        """Prove an arbitrary LaTeX statement string (no theorem environment needed)."""
        parser = ConjectureParser()
        conjecture = parser.parse_statement(statement_latex, conjecture_id)
        return self.prove_conjecture(conjecture, category=category, verbose=verbose)

    def prove(
        self,
        parsed: ParsedTheorem,
        category: str = "Polytope",
        verbose: bool = True,
    ) -> FormalizationResult:
        """Prove using an already-constructed ParsedTheorem (skips LLM parsing)."""
        return self.formalize(
            parsed.latex_source,
            category=category,
            verbose=verbose,
            parsed=parsed,
        )
