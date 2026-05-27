"""
agent/tools/polytope_constructor.py — PolytopeConstructor

Attempts to construct an actual simple convex 3-polytope graph (3-connected
cubic planar graph) whose p-vector matches a given target.

If construction succeeds the p-vector is PROVEN realizable — no theorem
citation or LLM opinion required.

Strategies (tried in order of speed)
--------------------------------------
1. Exact known polytopes  — O(1) dict lookup
2. Prism family           — O(k) direct edge list
3. Fullerene / near-dodecahedron  — dodecahedron + chops for p5-only family
4. A* chop search from dodecahedron  — heuristic, fast for barrel family
5. A* chop search from tetrahedron  — fallback for exotic p-vectors
"""
from __future__ import annotations

import time
import heapq
import warnings
from typing import Optional

import networkx as nx
warnings.filterwarnings("ignore", message=".*hashes produced.*", module="networkx")

try:
    import graphcalc as gc
    from graphcalc.graphs.polytopes import (
        simple_polytope_graph, p_vector as gc_p_vector,
        dodecahedron_graph, tetrahedron_graph,
    )
    _GC_OK = True
except ImportError:
    _GC_OK = False


# ── graphcalc wrappers ────────────────────────────────────────────────────────

def _is_simple_polytope(G: nx.Graph) -> bool:
    if not _GC_OK:
        return False
    try:
        return bool(simple_polytope_graph(G))
    except Exception:
        return False


def _pvec_of(G: nx.Graph) -> Optional[dict[int, int]]:
    """Return p-vector as {face_size: count} or None if not a simple polytope."""
    if not _GC_OK:
        return None
    try:
        if not simple_polytope_graph(G):
            return None
        raw = gc_p_vector(G)          # list [p3, p4, p5, p6, ...]
        return {k + 3: v for k, v in enumerate(raw) if v > 0}
    except Exception:
        return None


# ── chop operation ────────────────────────────────────────────────────────────

def _chop(G: nx.Graph, v: int) -> Optional[nx.Graph]:
    """Node-chop of vertex v (must have degree 3). Returns new graph or None."""
    if G.degree(v) != 3:
        return None
    G2 = G.copy()
    nbrs = list(G2.neighbors(v))
    G2.remove_node(v)
    nxt = max(G2.nodes()) + 1 if G2.nodes() else 0
    a, b, c = nxt, nxt + 1, nxt + 2
    G2.add_edges_from([
        (a, b), (b, c), (c, a),
        (a, nbrs[0]), (b, nbrs[1]), (c, nbrs[2]),
    ])
    return G2


# ── p-vector distance heuristic ───────────────────────────────────────────────

def _pv_dist(pv: dict[int, int], target: dict[int, int]) -> int:
    """L1 distance between two p-vectors (over union of keys)."""
    keys = set(pv) | set(target)
    return sum(abs(pv.get(k, 0) - target.get(k, 0)) for k in keys)


# ── Strategy 1: exact known polytopes ────────────────────────────────────────

_KNOWN: list[tuple[dict[int, int], str]] = [
    ({3: 4},       "tetrahedron"),
    ({3: 2, 4: 3}, "triangular_prism"),
    ({4: 6},       "cube"),
    ({5: 12},      "dodecahedron"),
]

def _build_known(p_vec: dict[int, int]) -> Optional[nx.Graph]:
    nonzero = {k: v for k, v in p_vec.items() if v > 0}
    for known_pv, name in _KNOWN:
        if nonzero == known_pv:
            if name == "tetrahedron":
                return nx.complete_graph(4)
            if name == "triangular_prism":
                return nx.triangular_prism_graph()
            if name == "cube":
                return nx.hypercube_graph(3)   # 3-cube = Q3
            if name == "dodecahedron":
                return nx.dodecahedral_graph()
    return None


# ── Strategy 2: prism family (p4=n, p_n=2) ───────────────────────────────────

def _build_prism(p_vec: dict[int, int]) -> Optional[nx.Graph]:
    """n-gonal prism: p4=n, p_n=2 for n ≥ 3."""
    nonzero = {k: v for k, v in p_vec.items() if v > 0}
    if set(nonzero.keys()) == {4, 3}:
        # Triangular prism special case
        if nonzero[4] == 3 and nonzero[3] == 2:
            return nx.triangular_prism_graph()
    if len(nonzero) != 2:
        return None
    sizes = list(nonzero.keys())
    # One size should be 4 (p4=n), the other is n (p_n=2)
    for s in sizes:
        n = s
        if nonzero.get(4, 0) == n and nonzero.get(n, 0) == 2 and n >= 3:
            return _make_prism(n)
    return None


def _make_prism(n: int) -> nx.Graph:
    """Build n-gonal prism graph."""
    G = nx.Graph()
    # Bottom ring: 0..n-1, top ring: n..2n-1
    for i in range(n):
        G.add_edge(i, (i + 1) % n)
        G.add_edge(n + i, n + (i + 1) % n)
        G.add_edge(i, n + i)
    return G


# ── Strategy 3 & 4: A* chop search ───────────────────────────────────────────

def _astar_chop(
    start: nx.Graph,
    target_pv: dict[int, int],
    timeout: float,
    max_f2_over: int = 3,
) -> Optional[nx.Graph]:
    """
    A* search over node-chop operations.

    State: (f_score, g_score, unique_id, graph)
    Heuristic h: L1 distance between current and target p-vectors
                 (admissible since each chop changes exactly 4 p-vector entries
                  by at most 1 each, so can reduce distance by at most 4).
    """
    target_f2 = sum(target_pv.values())
    start_pv = _pvec_of(start)
    if start_pv is None:
        return None

    h0 = _pv_dist(start_pv, target_pv)
    counter = 0   # tie-break

    # heap: (f, g, id, G, pv)
    heap = [(h0, 0, counter, start, start_pv)]
    visited: set[str] = {nx.weisfeiler_lehman_graph_hash(start)}
    deadline = time.monotonic() + timeout

    while heap:
        if time.monotonic() > deadline:
            return None

        f, g, _, G, pv = heapq.heappop(heap)

        if pv == target_pv:
            return G

        # Prune: too many faces already
        current_f2 = sum(pv.values()) if pv else G.number_of_nodes()
        if current_f2 > target_f2 + max_f2_over:
            continue

        for v in list(G.nodes()):
            G2 = _chop(G, v)
            if G2 is None:
                continue
            h2 = nx.weisfeiler_lehman_graph_hash(G2)
            if h2 in visited:
                continue
            visited.add(h2)

            pv2 = _pvec_of(G2)
            if pv2 is None:
                continue
            if pv2 == target_pv:
                return G2

            dist = _pv_dist(pv2, target_pv)
            g2 = g + 1
            f2_score = g2 + dist
            counter += 1
            heapq.heappush(heap, (f2_score, g2, counter, G2, pv2))

    return None


# ── Public API ────────────────────────────────────────────────────────────────

class PolytopeConstructor:
    """
    Constructs a witness simple 3-polytope graph from a p-vector.

    Usage
    -----
        G, method = PolytopeConstructor().build({5: 12})
        # G is a networkx.Graph whose p-vector matches the input,
        # or G is None if construction failed.
    """

    def build(
        self,
        p_vec: dict[int, int],
        timeout: float = 8.0,
    ) -> tuple[Optional[nx.Graph], str]:
        """Return (witness_graph, method_name) or (None, reason)."""
        nonzero = {k: v for k, v in p_vec.items() if v > 0}
        target_f2 = sum(nonzero.values())

        # Strategy 1: exact known polytopes
        G = _build_known(nonzero)
        if G is not None:
            return G, "exact_known_polytope"

        # Strategy 2: prism family
        G = _build_prism(nonzero)
        if G is not None and _pvec_of(G) == nonzero:
            return G, "prism_direct_construction"

        if not _GC_OK:
            return None, "graphcalc_unavailable"

        # Strategy 3: A* from dodecahedron (best for barrel / fullerene families)
        if target_f2 <= 30:
            G = _astar_chop(
                nx.dodecahedral_graph(), nonzero,
                timeout=timeout * 0.6,   # 60% of budget
            )
            if G is not None:
                return G, "astar_from_dodecahedron"

        # Strategy 4: A* from tetrahedron (fallback for exotic p-vectors)
        if target_f2 <= 20:
            G = _astar_chop(
                nx.complete_graph(4), nonzero,
                timeout=timeout * 0.35,  # remaining budget
            )
            if G is not None:
                return G, "astar_from_tetrahedron"

        return None, "construction_failed_within_timeout"
