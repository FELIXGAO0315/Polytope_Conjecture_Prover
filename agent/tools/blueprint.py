from __future__ import annotations

import hashlib
import json
import re
import time
from collections import deque
from dataclasses import dataclass

from agent.exceptions import BlueprintError
from agent.tools.goal_lock import LockedGoal
from agent.tools.latex_parser import ParsedTheorem

BLUEPRINT_PROMPT = """\
You are a Lean 4 formalization expert. Decompose the following LaTeX proof into a directed acyclic graph (DAG) of blueprint nodes.

Theorem: {theorem_name}
Lean signature: {lean_signature}
Hypotheses:
{hypotheses}
Conclusion: {conclusion}

Proof steps:
{proof_steps}

## Already-proved Polib lemmas (available via `import Polib` — do NOT re-prove these)
{available_lemmas}
For any node whose proof can directly call one of these lemmas, say so explicitly in the
`description` field (e.g. "Follows directly from `EdgeCountEquation` and `NonHexOccupationTotal`").
A node that is already fully covered by an existing Polib lemma should still appear in the
blueprint (for name-stability) but its description must reference the lemma by name.

## Instructions

### Node structure
- Each distinct definition or auxiliary lemma that must exist before the main theorem gets its own node.
- Node types: "def" for structures/type definitions, "lemma" for auxiliary results, "theorem" for the main target.
- Exactly ONE node must have "is_main_target": true (the main theorem).
- "latex_fragment" must be a verbatim excerpt from the proof above — do not paraphrase.

### CRITICAL — Node naming to avoid Polib collisions
All nodes live in a shared global library (Polib). A node named `InequalityPart` from theorem A
will be REUSED (not re-proved) by theorem B if theorem B also produces a node with that name.
To prevent incorrect reuse across theorems:
- **FIRST**: check `Already-proved Polib lemmas` above. If an existing lemma covers the same
  mathematical content, name your node identically to that lemma and mark it as proved via that lemma.
- **Otherwise**: prefix generic names with the theorem name.
  BAD:  `"node_id": "InequalityPart"`   — too generic, will collide across theorems
  GOOD: `"node_id": "P6InequalityPart"` — theorem-scoped, no collision risk
  GOOD: `"node_id": "InequalityPart"`   — only if it reuses an existing Polib lemma of the same name
- Exception: nodes that define shared structure (defs, type classes) may keep generic names
  IF they are mathematically identical to their Polib counterpart.

### CRITICAL — Dependency rules (read carefully)
A node B should list node A as a dependency ONLY IF:
  1. B's proof directly CALLS or APPLIES a result from A (e.g. B rewrites using a lemma proved in A), OR
  2. B's TYPE SIGNATURE mentions a type or constant defined in A.

DO NOT add A as a dependency of B if:
  - A and B merely appear in the same proof
  - A is "earlier" in the proof text but B does not use A's result
  - A defines something that B could re-derive independently
  - You are unsure — when in doubt, omit the dependency

### Why this matters
Unnecessary dependencies force sequential compilation. Nodes with no dependency between them will be compiled in PARALLEL, which is much faster. Only add a dependency edge when it is logically required.

### Example of BAD dependencies (too many):
  LemmaB depends on [DefA, LemmaX, LemmaY]  ← wrong if B only uses DefA

### Example of GOOD dependencies (minimal):
  LemmaB depends on [DefA]  ← correct if B only references types from DefA

Respond with ONLY valid JSON matching this schema. No prose. No markdown fences.

{{
  "nodes": [
    {{
      "node_id": "CamelCaseUniqueId",
      "node_type": "def" | "lemma" | "theorem",
      "description": "One sentence describing what this node proves or defines.",
      "latex_fragment": "verbatim excerpt from the proof",
      "dependencies": ["only_direct_deps_here"],
      "is_main_target": false
    }}
  ]
}}
"""


@dataclass
class BlueprintNode:
    node_id: str
    node_type: str  # "def" | "lemma" | "theorem"
    description: str
    latex_fragment: str
    dependencies: list[str]
    is_main_target: bool

    def to_dict(self) -> dict:
        return {
            "node_id": self.node_id,
            "node_type": self.node_type,
            "description": self.description,
            "latex_fragment": self.latex_fragment,
            "dependencies": self.dependencies,
            "is_main_target": self.is_main_target,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "BlueprintNode":
        return cls(
            node_id=d["node_id"],
            node_type=d["node_type"],
            description=d["description"],
            latex_fragment=d["latex_fragment"],
            dependencies=d["dependencies"],
            is_main_target=d["is_main_target"],
        )


@dataclass
class Blueprint:
    theorem_name: str
    nodes: list[BlueprintNode]
    topo_order: list[str]
    blueprint_hash: str

    def to_dict(self) -> dict:
        return {
            "theorem_name": self.theorem_name,
            "nodes": [n.to_dict() for n in self.nodes],
            "topo_order": self.topo_order,
            "blueprint_hash": self.blueprint_hash,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "Blueprint":
        return cls(
            theorem_name=d["theorem_name"],
            nodes=[BlueprintNode.from_dict(n) for n in d["nodes"]],
            topo_order=d["topo_order"],
            blueprint_hash=d["blueprint_hash"],
        )

    def get_node(self, node_id: str) -> BlueprintNode:
        for node in self.nodes:
            if node.node_id == node_id:
                return node
        raise KeyError(f"Node '{node_id}' not found in blueprint")

    def get_dependencies(self, node_id: str) -> list[BlueprintNode]:
        node = self.get_node(node_id)
        return [self.get_node(dep_id) for dep_id in node.dependencies]


def _topological_sort(nodes: list[BlueprintNode]) -> list[str]:
    """Kahn's algorithm. Raises BlueprintError on cycle."""
    node_ids = {n.node_id for n in nodes}
    in_degree: dict[str, int] = {n.node_id: 0 for n in nodes}
    adj: dict[str, list[str]] = {n.node_id: [] for n in nodes}

    for node in nodes:
        for dep in node.dependencies:
            if dep not in node_ids:
                raise BlueprintError(
                    f"Node '{node.node_id}' depends on unknown node '{dep}'"
                )
            adj[dep].append(node.node_id)
            in_degree[node.node_id] += 1

    queue: deque[str] = deque(nid for nid, deg in in_degree.items() if deg == 0)
    order: list[str] = []

    while queue:
        nid = queue.popleft()
        order.append(nid)
        for successor in adj[nid]:
            in_degree[successor] -= 1
            if in_degree[successor] == 0:
                queue.append(successor)

    if len(order) != len(nodes):
        processed = set(order)
        cycle_nodes = [n.node_id for n in nodes if n.node_id not in processed]
        raise BlueprintError(f"Circular dependency detected among nodes: {cycle_nodes}")

    return order


def _validate_blueprint_nodes(
    nodes: list[BlueprintNode],
    known_polib_ids: set[str] | None = None,
) -> None:
    main_targets = [n for n in nodes if n.is_main_target]
    if len(main_targets) != 1:
        raise BlueprintError(
            f"Blueprint must have exactly one main target node, got {len(main_targets)}"
        )
    node_ids = {n.node_id for n in nodes}
    allowed = node_ids | (known_polib_ids or set())
    for node in nodes:
        for dep in node.dependencies:
            if dep not in allowed:
                raise BlueprintError(
                    f"Node '{node.node_id}' depends on '{dep}' which does not exist"
                )


def _parse_blueprint_json(text: str) -> list[BlueprintNode]:
    """Extract and parse the blueprint JSON from a Claude response."""
    # Strip markdown fences if present
    text = re.sub(r"```(?:json)?\s*", "", text)
    text = text.strip()

    # Find outermost JSON object or array
    json_match = re.search(r"\{.*\}", text, re.DOTALL)
    if not json_match:
        raise BlueprintError(f"No JSON object found in blueprint response:\n{text[:500]}")

    try:
        data = json.loads(json_match.group())
    except json.JSONDecodeError as exc:
        raise BlueprintError(f"Invalid JSON in blueprint response: {exc}") from exc

    raw_nodes = data.get("nodes", [])
    if not raw_nodes:
        raise BlueprintError("Blueprint JSON contains no nodes")

    nodes: list[BlueprintNode] = []
    for item in raw_nodes:
        try:
            nodes.append(BlueprintNode.from_dict(item))
        except (KeyError, TypeError) as exc:
            raise BlueprintError(f"Invalid node schema: {exc}") from exc

    return nodes


class BlueprintDecomposer:
    def __init__(self, client, model: str):
        self._client = client
        self._model = model

    def decompose(
        self,
        parsed: ParsedTheorem,
        goal: "LockedGoal | GoalLock",
        proved_lemmas: list[dict] | None = None,
    ) -> Blueprint:
        proof_text = "\n".join(s.latex_text for s in parsed.proof_steps)
        # Accept either LockedGoal directly or GoalLock wrapper
        locked_goal = goal.goal if hasattr(goal, "goal") else goal
        if proved_lemmas:
            avail = "\n".join(
                f"  - `{e['node_id']}`" + (f": {e['description']}" if e.get('description') else "")
                for e in proved_lemmas
            )
        else:
            avail = "  (none yet)"
        # Escape any curly braces in interpolated values so .format() doesn't choke
        avail = avail.replace("{", "{{").replace("}", "}}")
        user_content = BLUEPRINT_PROMPT.format(
            theorem_name=parsed.name,
            lean_signature=locked_goal.lean_signature,
            hypotheses="\n".join(f"  - {h}" for h in parsed.hypotheses),
            conclusion=parsed.conclusion,
            proof_steps=proof_text,
            available_lemmas=avail,
        )

        polib_ids = {e["node_id"] for e in (proved_lemmas or [])}
        last_exc: Exception | None = None
        messages: list[dict] = [{"role": "user", "content": user_content}]
        for attempt in range(3):
            if attempt > 0:
                time.sleep(5 * attempt)
            response = self._client.messages.create(
                model=self._model,
                max_tokens=2048,
                messages=messages,
            )
            text = response.content[0].text.strip()
            try:
                nodes = _parse_blueprint_json(text)
                _validate_blueprint_nodes(nodes, known_polib_ids=polib_ids)
                topo_order = _topological_sort(nodes)
                break
            except BlueprintError as exc:
                last_exc = exc
                # Add the bad response + correction request to the conversation and retry
                messages = messages + [
                    {"role": "assistant", "content": text},
                    {"role": "user", "content":
                        "Your response was not valid JSON matching the required schema. "
                        "Respond with ONLY the JSON object — no prose, no markdown, no comments. "
                        "Start your response with '{' and end with '}'."},
                ]
        else:
            raise last_exc  # type: ignore[misc]

        blueprint_data = json.dumps([n.to_dict() for n in nodes], sort_keys=True)
        blueprint_hash = hashlib.sha256(blueprint_data.encode()).hexdigest()

        return Blueprint(
            theorem_name=parsed.name,
            nodes=nodes,
            topo_order=topo_order,
            blueprint_hash=blueprint_hash,
        )
