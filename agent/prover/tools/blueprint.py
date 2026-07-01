"""Blueprint DAG types + parsing helpers.

The actual decomposer lives in ``agent/prover/conjecture_decomposer.py``
(``ConjectureDecomposer``); this module only owns the data classes
(``BlueprintNode``, ``Blueprint``) and the shared JSON-parsing / topo-sort
/ schema-validation helpers it uses.
"""
from __future__ import annotations

import json
import re
from collections import deque
from dataclasses import dataclass

from agent.exceptions import BlueprintError


@dataclass
class BlueprintNode:
    node_id: str
    node_type: str  # "def" | "lemma" | "theorem"
    description: str
    latex_fragment: str
    dependencies: list[str]
    is_main_target: bool
    # Optional Lean 4 signature for sub-lemmas. When the planner supplies this,
    # the prover treats it as a LOCKED goal (same way the main theorem's
    # goal_lock works) instead of asking the LLM to re-invent a signature from
    # `latex_fragment` each round. Eliminates signature drift across retries.
    lean_signature: str | None = None

    def to_dict(self) -> dict:
        return {
            "node_id": self.node_id,
            "node_type": self.node_type,
            "description": self.description,
            "latex_fragment": self.latex_fragment,
            "dependencies": self.dependencies,
            "is_main_target": self.is_main_target,
            "lean_signature": self.lean_signature,
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
            lean_signature=d.get("lean_signature"),
        )


@dataclass
class Blueprint:
    nodes: list[BlueprintNode]
    topo_order: list[str]

    def to_dict(self) -> dict:
        return {
            "nodes": [n.to_dict() for n in self.nodes],
            "topo_order": self.topo_order,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "Blueprint":
        # Old store.json entries may have `theorem_name` + `blueprint_hash`
        # keys; .get-ignored harmlessly.
        return cls(
            nodes=[BlueprintNode.from_dict(n) for n in d["nodes"]],
            topo_order=d["topo_order"],
        )

    def get_node(self, node_id: str) -> BlueprintNode:
        for node in self.nodes:
            if node.node_id == node_id:
                return node
        raise KeyError(f"Node '{node_id}' not found in blueprint")


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


def _validate_blueprint_nodes(nodes: list[BlueprintNode]) -> None:
    """Schema check: exactly one main target, unique node_ids, in-blueprint deps,
    and every non-main node carries a planner-supplied ``lean_signature``.

    Without ``lean_signature``, a sub-lemma node has no goal for the prover to
    aim at — the LLM would receive the parent conjecture's signature and write
    the parent's theorem name in every file, which the acceptance check then
    rejects.  Make the planner declare the sub-lemma signatures upfront so the
    prover always knows what to prove.
    """
    main_targets = [n for n in nodes if n.is_main_target]
    if len(main_targets) != 1:
        raise BlueprintError(
            f"Blueprint must have exactly one main target node, got {len(main_targets)}"
        )
    node_ids = [n.node_id for n in nodes]
    seen: set[str] = set()
    dupes: list[str] = []
    for nid in node_ids:
        if nid in seen:
            dupes.append(nid)
        seen.add(nid)
    if dupes:
        raise BlueprintError(
            f"Duplicate node_id(s) in blueprint: {sorted(set(dupes))} — "
            f"every node must have a unique identifier"
        )
    missing_sig = [
        n.node_id for n in nodes
        if not n.is_main_target and not (n.lean_signature or "").strip()
    ]
    if missing_sig:
        raise BlueprintError(
            f"Non-main-target node(s) missing `lean_signature`: {missing_sig}. "
            f"Every sub-lemma must declare its exact Lean header (with the node id "
            f"as the declaration name) so the prover knows what to prove. "
            f"Only the main-target node may omit it (the system uses the "
            f"conjecture's locked goal there)."
        )
    for node in nodes:
        for dep in node.dependencies:
            if dep not in seen:
                raise BlueprintError(
                    f"Node '{node.node_id}' depends on '{dep}' which is not "
                    f"a node in this blueprint (cross-theorem deps are forbidden — "
                    f"reference Inventory lemmas in `description` instead)"
                )


def _parse_blueprint_json(text: str) -> list[BlueprintNode]:
    """Extract and parse the blueprint JSON from a Claude response."""
    text = re.sub(r"```(?:json)?\s*", "", text)
    text = text.strip()

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
