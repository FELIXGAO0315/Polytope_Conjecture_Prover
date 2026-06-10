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

import json
import math
import os
import subprocess
import tempfile
import threading
import time
import heapq
import warnings
from pathlib import Path
from typing import Optional

import networkx as nx
warnings.filterwarnings("ignore", message=".*hashes produced.*", module="networkx")

try:
    import graphcalc as gc
    # graphcalc >= 1.3 exposes these at the top level (graphcalc.graphs.polytopes
    # no longer exists — the old path made this import silently fail and
    # permanently disabled the Tier-4 realizability constructor).
    from graphcalc import (
        simple_polytope_graph, p_vector as gc_p_vector,
        dodecahedron_graph, tetrahedron_graph,
    )
    _GC_OK = True
except ImportError:
    _GC_OK = False

try:
    import numpy as _np
    from scipy.spatial import ConvexHull as _ConvexHull
    _SCIPY_OK = True
except ImportError:
    _SCIPY_OK = False


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


# ── plantri exhaustive decision (exact, both directions) ─────────────────────
#
# plantri (Brinkmann & McKay) with the allowed_deg plugin enumerates ALL sphere
# triangulations with a prescribed degree multiset, isomorph-free. The dual of
# such a triangulation is exactly a simple 3-polytope with the target p-vector:
#   count > 0 → witness graph extracted   |   count = 0 → PROVEN non-realizable
# This decided C2: all five p3=p4=0 candidates at f2=22 are non-realizable, and
# {3:1,5:16,6:4,13:1} has exactly 2 realizations — the verified counterexample.

_PC_PROJECT_ROOT = Path(__file__).resolve().parents[3]
_PLANTRI_BIN = Path(os.environ.get(
    "PLANTRI_AD", _PC_PROJECT_ROOT / "tools" / "plantri" / "plantri_ad"))
_REALIZABILITY_CACHE = _PC_PROJECT_ROOT / "output" / "realizability_cache.json"
_cache_lock = threading.Lock()


def _cache_key(p_vec: dict[int, int]) -> str:
    return json.dumps({str(k): v for k, v in sorted(p_vec.items())})


def _cache_get(p_vec: dict[int, int]) -> Optional[str]:
    with _cache_lock:
        try:
            data = json.loads(_REALIZABILITY_CACHE.read_text())
        except Exception:
            return None
        return data.get(_cache_key(p_vec))


def _cache_put(p_vec: dict[int, int], verdict: str) -> None:
    # Only exhaustive verdicts are cached — never timeouts.
    with _cache_lock:
        try:
            data = json.loads(_REALIZABILITY_CACHE.read_text())
        except Exception:
            data = {}
        data[_cache_key(p_vec)] = verdict
        try:
            _REALIZABILITY_CACHE.parent.mkdir(parents=True, exist_ok=True)
            _REALIZABILITY_CACHE.write_text(json.dumps(data, indent=1))
        except Exception:
            pass


def _plantri_spec(p_vec: dict[int, int]) -> str:
    return "-" + "".join(f"F{k}_{v}^{v}" for k, v in sorted(p_vec.items()))


def _parse_plantri_ascii(line: str) -> dict[int, list[int]]:
    """ASCII code: 'n list,list,...' with neighbors in embedding rotation order."""
    n_str, lists = line.strip().split(" ", 1)
    rot = {i: [ord(c) - ord("a") for c in lst]
           for i, lst in enumerate(lists.split(","))}
    assert len(rot) == int(n_str)
    return rot


def _trace_faces(rot: dict[int, list[int]], succ: bool) -> list[list[int]]:
    faces, seen = [], set()
    for u in rot:
        for v in rot[u]:
            if (u, v) in seen:
                continue
            face, e = [], (u, v)
            while e not in seen:
                seen.add(e)
                face.append(e[0])
                a, b = e
                r = rot[b]
                i = r.index(a)
                e = (b, r[(i + 1) % len(r)] if succ else r[(i - 1) % len(r)])
            faces.append(face)
    return faces


def _triangulation_dual(rot: dict[int, list[int]]) -> Optional[nx.Graph]:
    """Primal polytope graph = dual of the triangulation (faces, ridge-adjacency)."""
    n = len(rot)
    faces = None
    for succ in (True, False):
        f = _trace_faces(rot, succ)
        if len(f) == 2 * n - 4 and all(len(x) == 3 for x in f):
            faces = f
            break
    if faces is None:
        return None
    edge2faces: dict[frozenset, list[int]] = {}
    for fi, f in enumerate(faces):
        for j in range(3):
            edge2faces.setdefault(frozenset((f[j], f[(j + 1) % 3])), []).append(fi)
    G = nx.Graph()
    G.add_nodes_from(range(len(faces)))
    for fs in edge2faces.values():
        if len(fs) != 2:
            return None
        G.add_edge(fs[0], fs[1])
    return G


def _plantri_decide(
    target: dict[int, int], timeout: float, jobs: int | None = None,
) -> tuple[Optional[nx.Graph], str]:
    """Exhaustively decide realizability of `target` with plantri.

    Returns (graph, "realizable") | (None, "nonrealizable") |
            (None, "timeout") | (None, "unavailable").
    """
    n = sum(target.values())
    f2_max = int(os.environ.get("PLANTRI_F2_MAX", "26"))
    if not _PLANTRI_BIN.exists() or n < 4 or n > f2_max or max(target) > n - 1:
        return None, "unavailable"
    if jobs is None:
        jobs = min(16, os.cpu_count() or 4)

    cached = _cache_get(target)
    if cached == "nonrealizable":
        return None, "nonrealizable"

    spec = _plantri_spec(target)
    deadline = time.monotonic() + timeout

    # Phase 1: count in parallel splits
    procs = [subprocess.Popen(
        [str(_PLANTRI_BIN), spec, str(n), f"{r}/{jobs}", "-u"],
        stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True,
    ) for r in range(jobs)]
    counts: list[int] = []
    try:
        for p in procs:
            remaining = max(0.5, deadline - time.monotonic())
            _, err = p.communicate(timeout=remaining)
            for ln in err.splitlines():
                if "triangulations generated" in ln or "triangulations written" in ln:
                    counts.append(int(ln.split()[0]))
                    break
            else:
                raise RuntimeError("plantri output not recognised")
    except (subprocess.TimeoutExpired, RuntimeError, Exception):
        for p in procs:
            try:
                p.kill()
            except Exception:
                pass
        return None, "timeout"

    if sum(counts) == 0:
        _cache_put(target, "nonrealizable")
        return None, "nonrealizable"

    # Phase 2: regenerate only the first nonzero split with ASCII output
    r_hit = next(i for i, c in enumerate(counts) if c > 0)
    with tempfile.NamedTemporaryFile(mode="r", suffix=".txt", delete=False) as tf:
        out_path = tf.name
    try:
        subprocess.run(
            [str(_PLANTRI_BIN), spec, str(n), f"{r_hit}/{jobs}", "-a", out_path],
            capture_output=True, text=True,
            timeout=max(5.0, deadline - time.monotonic() + timeout),
        )
        with open(out_path) as fh:
            line = fh.readline()
    finally:
        try:
            os.unlink(out_path)
        except OSError:
            pass
    if not line.strip():
        return None, "timeout"
    G = _triangulation_dual(_parse_plantri_ascii(line))
    if G is None:
        return None, "timeout"
    return G, "realizable"


# ── Dual-space perturbation search ────────────────────────────────────────────

def _primal_graph_from_dual_hull(hull) -> nx.Graph:
    """Primal simple-polytope graph from a dual simplicial hull: vertices are
    hull facets, edges join facets sharing a ridge (3-regular by construction)."""
    G = nx.Graph()
    G.add_nodes_from(range(len(hull.simplices)))
    for i, nbrs in enumerate(hull.neighbors):
        for j in nbrs:
            if int(j) >= 0:
                G.add_edge(i, int(j))
    return G


def _dual_perturbation_search(target: dict[int, int], timeout: float) -> Optional[nx.Graph]:
    """Realize `target` by local search over point configurations on the sphere.

    The dual of a simple 3-polytope is a simplicial polytope. Placing f2 points
    on the unit sphere makes every point a hull vertex, and the hull's
    vertex-valence histogram equals the primal p-vector. One point is moved at
    a time, hill-climbing on the L1 distance between histogram and target
    (sideways drift allowed, random restarts on stall). On exact match the
    primal graph is extracted and independently re-verified via graphcalc.
    """
    if not (_SCIPY_OK and _GC_OK):
        return None
    f2 = sum(target.values())
    if f2 < 4:
        return None
    rng = _np.random.default_rng()
    deadline = time.monotonic() + timeout

    def _hull_hist(pts):
        try:
            hull = _ConvexHull(pts)
        except Exception:
            return None, None
        if len(hull.vertices) != len(pts):
            return None, None
        deg: dict[int, int] = {}
        for s in hull.simplices:
            for v in s:
                deg[v] = deg.get(v, 0) + 1
        hist: dict[int, int] = {}
        for d in deg.values():
            hist[d] = hist.get(d, 0) + 1
        return hull, hist

    def _dist(hist: dict[int, int]) -> int:
        keys = set(hist) | set(target)
        return sum(abs(hist.get(k, 0) - target.get(k, 0)) for k in keys)

    def _rand_sphere(n: int):
        v = rng.normal(size=(n, 3))
        return v / _np.linalg.norm(v, axis=1, keepdims=True)

    def _cap_seed():
        """Seed with the largest face pre-built: a pole surrounded by a ring of
        kmax points (the pole's hull degree is then exactly kmax as long as the
        cap stays empty), remaining points spread over the southern region."""
        kmax = max(target)
        if kmax < 7 or target.get(kmax, 0) != 1 or f2 < kmax + 2:
            return None
        pts = [[0.0, 0.0, 1.0]]
        theta = 0.9   # ring polar angle (rad)
        for t in range(kmax):
            a = 2.0 * math.pi * t / kmax
            pts.append([math.sin(theta) * math.cos(a),
                        math.sin(theta) * math.sin(a),
                        math.cos(theta)])
        rest = f2 - 1 - kmax
        for t in range(rest):
            z = rng.uniform(-1.0, math.cos(1.25))
            a = rng.uniform(0.0, 2.0 * math.pi)
            r = math.sqrt(max(0.0, 1.0 - z * z))
            pts.append([r * math.cos(a), r * math.sin(a), z])
        arr = _np.array(pts) + rng.normal(scale=0.03, size=(f2, 3))
        return arr / _np.linalg.norm(arr, axis=1, keepdims=True)

    def _vertex_degrees(hull) -> dict[int, int]:
        deg: dict[int, int] = {}
        for s in hull.simplices:
            for v in s:
                deg[v] = deg.get(v, 0) + 1
        return deg

    def _pick_vertex(hull, hist) -> int:
        """Prefer moving a vertex whose degree class has a surplus vs target."""
        if rng.random() < 0.25:
            return int(rng.integers(f2))   # exploration
        degs = _vertex_degrees(hull)
        surplus = [v for v, d in degs.items() if hist.get(d, 0) > target.get(d, 0)]
        if not surplus:
            return int(rng.integers(f2))
        return int(surplus[int(rng.integers(len(surplus)))])

    while time.monotonic() < deadline:
        pts = None
        if rng.random() < 0.6:
            pts = _cap_seed()
        if pts is None:
            pts = _rand_sphere(f2)
        hull, hist = _hull_hist(pts)
        if hist is None:
            continue
        cur = _dist(hist)
        stall = 0
        temp = 1.5
        while time.monotonic() < deadline and stall < 1500:
            if cur == 0:
                G = _primal_graph_from_dual_hull(hull)
                if _pvec_of(G) == target:
                    return G
                stall = 10 ** 9  # verification mismatch — force a restart
                break
            i = _pick_vertex(hull, hist)
            new_pts = pts.copy()
            # half local jitter, half global teleport
            prop = (pts[i] + rng.normal(scale=0.25, size=3)) if rng.random() < 0.5 \
                else rng.normal(size=3)
            nrm = float(_np.linalg.norm(prop))
            if nrm < 1e-9:
                continue
            new_pts[i] = prop / nrm
            h2, hist2 = _hull_hist(new_pts)
            if hist2 is None:
                stall += 1
                continue
            d2 = _dist(hist2)
            # simulated annealing: always accept improvements, sometimes accept
            # equal/worse moves to escape histogram plateaus
            if d2 < cur:
                pts, hull, hist, cur = new_pts, h2, hist2, d2
                stall = 0
            elif rng.random() < float(_np.exp(-(d2 - cur) / max(temp, 1e-3))):
                pts, hull, hist, cur = new_pts, h2, hist2, d2
                stall += 1
            else:
                stall += 1
            temp = max(0.15, temp * 0.999)
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

        # Strategy 3: plantri exhaustive decision (exact, both directions).
        # If it completes, the answer is definitive: a witness graph, or a
        # proof by exhaustion that the p-vector is NON-realizable (the verdict
        # is cached across runs). Only on timeout do the heuristics below run.
        G, verdict = _plantri_decide(nonzero, timeout=timeout * 0.50)
        if verdict == "realizable" and G is not None and _pvec_of(G) == nonzero:
            return G, "plantri_exhaustive"
        if verdict == "nonrealizable":
            return None, "plantri_nonrealizable"

        # Chop reachability: every chop (vertex truncation) creates a new
        # triangular face, and the last chop's triangle persists in the final
        # graph. Hence any A* result with >= 1 chop has p3 >= 1; zero-chop
        # results equal the start graph (already covered by Tiers 1/2 above).
        # For triangle-free targets A* is provably hopeless — skip it and give
        # the whole budget to the dual-space search.
        chop_reachable = nonzero.get(3, 0) >= 1
        dual_budget = timeout * (0.20 if chop_reachable else 0.45)

        # Strategy 3b: dual-space perturbation search.
        # Moves points on the unit sphere until the dual hull's valence
        # histogram matches the target exactly — reaches topologies chop
        # search cannot (triangle-free targets, a single large face).
        G = _dual_perturbation_search(nonzero, timeout=dual_budget)
        if G is not None and _pvec_of(G) == nonzero:
            return G, "dual_perturbation_search"

        if not chop_reachable:
            return None, "construction_failed_within_timeout"

        # Strategy 4: A* from dodecahedron (best for barrel / fullerene families)
        if target_f2 <= 50:
            G = _astar_chop(
                nx.dodecahedral_graph(), nonzero,
                timeout=timeout * 0.30,
            )
            if G is not None:
                return G, "astar_from_dodecahedron"

        # Strategy 5: A* from tetrahedron (fallback for small / exotic p-vectors)
        if target_f2 <= 30:
            G = _astar_chop(
                nx.complete_graph(4), nonzero,
                timeout=timeout * 0.15,
            )
            if G is not None:
                return G, "astar_from_tetrahedron"

        # Strategy 6: A* from kmax-gon prism.
        # Helps targets that have large-k faces (k >= 7): starting the search
        # from a prism whose ring size matches the target's largest face puts
        # A* much closer in p-vector space, often halving the path length.
        kmax = max(nonzero.keys(), default=3)
        if kmax >= 7 and target_f2 <= 60:
            G = _astar_chop(
                _make_prism(kmax), nonzero,
                timeout=timeout * 0.15,
            )
            if G is not None:
                return G, f"astar_from_{kmax}gon_prism"

        return None, "construction_failed_within_timeout"
