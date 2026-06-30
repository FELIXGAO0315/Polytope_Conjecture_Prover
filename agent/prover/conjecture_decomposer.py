"""Discovery-mode blueprint decomposer for conjecture proving.

Subclasses ``BlueprintDecomposer`` to replace the prompt with one tuned for
\"there\'s no known proof yet — please find one\".  Reads Polib for proved
lemmas to advertise, ranks the most relevant for the planner prompt, and
embeds the conjecture as structured JSON so the planner can\'t accidentally
swap coefficients.
"""
from __future__ import annotations

import re
from pathlib import Path
from typing import TYPE_CHECKING

from agent.prover._helpers import (
    _build_conjecture_json,
    _extract_lean_signatures,
    _rank_lemmas_for_discovery,
)
from agent.prover.tools.blueprint import (
    Blueprint,
    BlueprintDecomposer,
    _parse_blueprint_json,
    _topological_sort,
    _validate_blueprint_nodes,
)
from agent.prover.tools.blueprint_validator import BlueprintValidator
from agent.exceptions import BlueprintError

if TYPE_CHECKING:
    from agent.prover.tools.goal_lock import GoalLock, LockedGoal
    from agent.prover.tools.latex_parser import ParsedTheorem


DISCOVERY_BLUEPRINT_PROMPT = """\
You are a Lean 4 proof discovery expert working in the domain of combinatorial
polytope theory. Your task is to devise a proof strategy for the following
UNPROVEN conjecture and express it as a directed acyclic graph (DAG) of
blueprint nodes. There is no known proof — you must figure out how to prove
it from first principles using Lean 4 / Mathlib tactics and the Inventory lemmas
listed below.

Conjecture name: {theorem_name}

## Conjecture statement (structured JSON — AUTHORITATIVE)
The block below is the canonical machine-parsed form of the conjecture.
**Trust `lean_signature` over every other representation.** The `raw_formula`
and `conclusion.coefficients` are provided as redundant cross-checks; if you
ever derive an algebraic claim, verify it against `lean_signature` by direct
substitution. NEVER swap, scale, or "simplify" the coefficients — copy them
exactly into any `latex_fragment` you emit.

```json
{conjecture_json}
```

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

## Polib lemmas (available via `import Inventory`)
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
- "lean_signature": for EVERY non-main node, write the COMPLETE Lean 4
  declaration header up to (and including) the `:= by` or `:=` token, e.g.
    `private lemma C104_LargeSumCase (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h_sum : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≥ 4) : maps.p_i 6 ≥ 0 := by`
  • MUST use the SAME genus as the parent theorem (`SimplyCon3ConnectedMap 0`,
    not `{{g : ℤ}}`).
  • MUST reuse the parent's hypothesis variable names (`maps`, `hM`, `h_p4`,
    `h_p5`, `h_f2`, …) so the main proof can apply it directly.
  • The lean_signature must be CONSISTENT with the latex_fragment — if you
    write `latex_fragment = "p_6 ≥ 0"` then lean_signature must conclude
    `: maps.p_i 6 ≥ 0` (not `≤`, not different RHS).
  • For the main-target node, leave "lean_signature" as null/omit — the
    locked goal signature is supplied by the system.

## CRITICAL — Node naming
All nodes live in a shared Inventory namespace. You MUST prefix every new node
you define with the exact conjecture identifier: `{theorem_name}`.

  REQUIRED prefix: `{theorem_name}`
  BAD:   "InequalityBound"        ← no prefix, will collide
  BAD:   "P6InequalityBound"      ← wrong conjecture prefix
  GOOD:  "{theorem_name}InequalityBound"  ← correct

Exception: nodes that intentionally REUSE an existing Inventory lemma listed above
must use that lemma's exact name unchanged.

## CRITICAL — Dependency rules
Add A as a dependency of B ONLY IF B's proof directly calls/applies A's result
or B's type mentions a type defined in A. When in doubt, omit the dependency.

## CRITICAL — Cross-theorem dependencies are FORBIDDEN
Dependencies must only reference node_ids defined WITHIN THIS blueprint.
Do NOT list a node_id from another theorem's blueprint (e.g. "C2_DehnSommerville"
for a C4 blueprint) — those lemmas are already available via `import Inventory` and
must NOT appear as dependency entries. If you need a proved Inventory lemma, just
reference it by name in the `description` field; leave `dependencies` empty for that edge.

Respond with ONLY valid JSON — no prose, no markdown fences.

{{
  "nodes": [
    {{
      "node_id": "CamelCaseUniqueId",
      "node_type": "def" | "lemma" | "theorem",
      "description": "One sentence: what this node proves or defines.",
      "latex_fragment": "Brief mathematical description of the sub-goal.",
      "lean_signature": "private lemma CamelCaseUniqueId (maps : SimplyCon3ConnectedMap 0) ... : ... := by",
      "dependencies": ["only_direct_deps_here"],
      "is_main_target": false
    }}
  ]
}}
"""


class ConjectureDecomposer(BlueprintDecomposer):
    """BlueprintDecomposer variant that uses the discovery-mode prompt.

    Wraps the LLM call in a 3-attempt retry-with-correction loop guarded by
    `BlueprintValidator`: when an intermediate node's `latex_fragment` is
    refuted by a realizable plantri-pool polytope satisfying the conjecture's
    hypotheses, the concrete counter-example is fed back to the planner and
    it is asked to re-decompose. Catches the false-sub-lemma class of bugs
    (e.g. C104_P6HigherFacesBound: p_6 + 5·Σ ≥ 10 was refuted by the
    truncated tetrahedron) BEFORE downstream proof attempts waste budget.
    """

    # Default plantri pool used by the post-decompose sanity check.
    # If the path doesn't exist (running tests without harvest output), the
    # validator silently no-ops — pure safety net, never blocks pipeline.
    _DEFAULT_PLANTRI_POOL = (
        Path(__file__).resolve().parents[2]
        / "output" / "conjecture_generator" / "plantri_pool.json"
    )

    def __init__(
        self,
        client,
        model: str,
        polib_lean: Path | None = None,
        plantri_pool_path: Path | None = None,
    ) -> None:
        super().__init__(client, model)
        self._polib_lean = polib_lean
        self._validator = BlueprintValidator(
            plantri_pool_path or self._DEFAULT_PLANTRI_POOL
        )

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

        conjecture_json = _build_conjecture_json(
            parsed, locked_goal.lean_signature,
        )
        user_content = DISCOVERY_BLUEPRINT_PROMPT.format(
            theorem_name=parsed.name,
            conjecture_json=conjecture_json,
            available_lemmas=avail,
        )

        polib_ids = {e["node_id"] for e in (proved_lemmas or [])}
        messages: list[dict] = [{"role": "user", "content": user_content}]
        last_exc: Exception | None = None
        nodes: list[BlueprintNode] | None = None
        text = ""

        for attempt in range(3):
            print(f"      [planner attempt {attempt + 1}/3] sending prompt "
                  f"({len(messages)} messages in history)", flush=True)
            response = self._client.messages.create(
                model=self._model,
                max_tokens=2048,
                messages=messages,
            )
            text = response.content[0].text.strip()
            try:
                nodes = _parse_blueprint_json(text)
                _validate_blueprint_nodes(nodes, known_polib_ids=polib_ids)
                # Plantri-pool sanity check: refute blueprints whose
                # intermediate claims are violated by realizable polytopes
                # satisfying the conjecture's hypotheses. False intermediates
                # are caught here BEFORE downstream LLM calls burn budget on
                # proving an unprovable sub-lemma.
                refutation = self._validator.check(nodes, parsed.hypotheses)
                if refutation is not None:
                    raise BlueprintError(refutation.message())
                print(f"      [planner attempt {attempt + 1}/3] ACCEPTED — "
                      f"{len(nodes)} nodes, no refutation", flush=True)
                break
            except BlueprintError as exc:
                last_exc = exc
                err_msg = str(exc)
                # Log the rejection so the operator can see what L2.A caught
                # without having to add ad-hoc print statements.
                err_class = "REFUTED" if "REFUTED" in err_msg else (
                    "INVALID_JSON" if "JSON" in err_msg else "SCHEMA"
                )
                print(f"      [planner attempt {attempt + 1}/3] REJECTED "
                      f"({err_class}): {err_msg[:200]}", flush=True)
                if "REFUTED" in err_msg:
                    correction = (
                        err_msg + "\n\n"
                        "Re-emit the blueprint with a corrected decomposition. "
                        "The refuted intermediate is mathematically false and "
                        "must be replaced — do not keep it. Output ONLY the "
                        "JSON object."
                    )
                else:
                    correction = (
                        "Your response was not valid JSON matching the "
                        "required schema. Respond with ONLY the JSON object — "
                        "no prose, no markdown, no comments. Start your "
                        "response with '{' and end with '}'."
                    )
                messages = messages + [
                    {"role": "assistant", "content": text},
                    {"role": "user", "content": correction},
                ]
        else:
            print(f"      [planner] all 3 attempts failed — last error: "
                  f"{str(last_exc)[:200]}", flush=True)
            raise last_exc  # type: ignore[misc]

        assert nodes is not None  # for type checker
        topo_order = _topological_sort(nodes)
        blueprint_data = json.dumps([n.to_dict() for n in nodes], sort_keys=True)
        blueprint_hash = hashlib.sha256(blueprint_data.encode()).hexdigest()
        return Blueprint(
            theorem_name=parsed.name,
            nodes=nodes,
            topo_order=topo_order,
            blueprint_hash=blueprint_hash,
        )
