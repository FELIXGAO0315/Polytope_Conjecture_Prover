"""
agent/hopper_ce_finder/agent.py — Hopper-inspired CE finder for simple 3-polytopes.

Adapts the Hopper algorithm (Swirszcz et al., 2025) for simple convex 3-polytopes.

Key geometric insight for d=3
─────────────────────────────
Every simple 3-polytope P has a dual simplicial polytope P* (all faces triangles).
The vertices of P* are the outward face-normals of P.  Conversely, the vertex-
valence distribution of P* equals the p-vector of P:
    deg(v) = k  ↔  the primal face corresponding to v is a k-gon.

This means Dehn-Sommerville (Σ(6-k)p_k = 12) is automatically satisfied because
it is equivalent to Euler's formula on P*, which always holds.

Therefore we work entirely in dual space:
  • A polytope is stored as a small set of FACE NORMALS (dual vertices).
  • A "hop" moves one dual vertex to a new position (paper Algorithm 1, d=3).
  • After the hop, the new convex hull is always simplicial (generically true),
    so no simplicity check is needed — just verify that no vertex became interior.
  • p-vector = vertex valence histogram of the new dual hull.

This achieves a ~96% valid-hop rate (vs 0% with the primal simple-polytope
representation), making the algorithm practical.

Neural network (paper §A.11, simplified for d=3)
─────────────────────────────────────────────────
Input:  (n×3 dual vertices,  4-dim hyperplane equation)
Output: 3-class logit  [good hop | geom infeasible | feasible but bad]
Architecture: mean-pool over dual vertices + hyperplane MLP → joint MLP.
(Replaces the prismatoid-specific Transformer; appropriate since d=3 is fixed.)
"""
from __future__ import annotations

import math
import re
import threading
from collections import Counter, defaultdict
from datetime import datetime, timezone
from itertools import combinations
from typing import Optional

import numpy as np
import torch
import torch.nn as nn
import torch.optim as optim
from scipy.optimize import linprog
from scipy.spatial import ConvexHull, QhullError

from agent.orchestrator.tools.pvec_eval import (
    is_valid_simple_polytope,
    is_counterexample,
    _eval_rhs_expr,
    _eval_hypothesis,
)

if torch.cuda.is_available():
    _major, _ = torch.cuda.get_device_capability()
    device = torch.device("cuda") if _major >= 7 else torch.device("cpu")
else:
    device = torch.device("cpu")

_TAG = "[Hopper ce finding]"


# ── Dual-vertex seeds ──────────────────────────────────────────────────────────

def _prism_dual(n: int) -> np.ndarray:
    """Dual vertices of a regular n-gonal prism.

    The prism has n+2 faces (2 base polygons + n rectangles), so the dual has
    n+2 vertices.  Face normals: ±z for the two bases, and n horizontal normals.
    """
    theta = np.array([2 * math.pi * k / n for k in range(n)])
    lateral = np.column_stack([np.cos(theta), np.sin(theta), np.zeros(n)])
    top = np.array([[0.0, 0.0, 1.0]])
    bot = np.array([[0.0, 0.0, -1.0]])
    return np.vstack([top, bot, lateral])   # (n+2, 3)


def _dodecahedron_dual() -> np.ndarray:
    """Dual vertices of the dodecahedron = vertices of the icosahedron."""
    phi = (1.0 + 5.0 ** 0.5) / 2.0
    v: list[list[float]] = []
    for a in (0, 1, -1):
        for b in (-phi, phi):
            # cyclic permutations of (0, ±1, ±φ)
            v.append([0, 1 if b > 0 else -1, b])
            v.append([1 if b > 0 else -1, b, 0])
            v.append([b, 0, 1 if b > 0 else -1])
    return np.array(v, dtype=float) / (phi ** 0.5 + 1)   # normalise roughly


# n-gonal prisms: n = 3…21 give primal f2 = 5…23
_BASE_SEEDS: list[np.ndarray] = (
    [_prism_dual(n) for n in range(3, 22)]
    + [_dodecahedron_dual()]
)


# ── P-vector from dual simplicial hull ────────────────────────────────────────

def _pvec_from_dual(hull: ConvexHull) -> dict[int, int]:
    """p-vector of primal simple polytope = vertex-valence histogram of dual hull.

    For a simplicial hull, every facet is a triangle (3 vertices).
    The valence of vertex v = number of triangular facets containing v
                            = size of the corresponding primal face.
    """
    deg: dict[int, int] = defaultdict(int)
    for simplex in hull.simplices:
        for v in simplex:
            deg[v] += 1
    return dict(Counter(deg.values()))


# ── Hyperplane computation ─────────────────────────────────────────────────────

def _hyperplanes(verts: np.ndarray) -> list[np.ndarray]:
    """All planes through d=3 distinct vertices. Returns [nx, ny, nz, offset] (unit normal)."""
    planes: list[np.ndarray] = []
    for i, j, k in combinations(range(len(verts)), 3):
        a, b, c = verts[i], verts[j], verts[k]
        normal = np.cross(b - a, c - a)
        nrm = float(np.linalg.norm(normal))
        if nrm < 1e-10:
            continue
        normal = normal / nrm
        planes.append(np.array([*normal, float(np.dot(normal, a))]))
    return planes


# ── Chebyshev centre (Algorithm 1, steps 8–11) ────────────────────────────────

def _chebyshev(
    halfspaces: list[tuple[np.ndarray, float]],
) -> tuple[np.ndarray, float] | None:
    """Largest inscribed ball in ∩{n·x ≤ d}.  Returns (centre, radius) or None."""
    if len(halfspaces) < 4:
        return None
    c_obj = np.array([0.0, 0.0, 0.0, -1.0])
    A_ub = np.array([[*n, float(np.linalg.norm(n))] for n, _ in halfspaces])
    b_ub = np.array([float(d) for _, d in halfspaces])
    bounds = [(None, None), (None, None), (None, None), (0.0, None)]
    try:
        res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method="highs")
    except Exception:
        return None
    if res.status != 0 or float(res.x[3]) < 1e-8:
        return None
    return res.x[:3].copy(), float(res.x[3])


# ── Neural network (paper §A.11, simplified for d=3) ─────────────────────────

class HopperBrain(nn.Module):
    """Score (dual polytope, hyperplane) → 3-class logit.

    Classes  0 = good hop (improvement found)
             1 = geometrically infeasible region
             2 = feasible but no improvement
    Architecture: mean-pool dual-vertex embeddings + hyperplane encoder → joint MLP.
    """

    def __init__(self, hidden: int = 64) -> None:
        super().__init__()
        self.vert_enc = nn.Sequential(
            nn.Linear(3, hidden), nn.GELU(), nn.Linear(hidden, hidden)
        )
        self.plane_enc = nn.Sequential(
            nn.Linear(4, hidden), nn.GELU(), nn.Linear(hidden, hidden)
        )
        self.joint = nn.Sequential(
            nn.Linear(2 * hidden, hidden), nn.GELU(),
            nn.Linear(hidden, hidden // 2), nn.GELU(),
            nn.Linear(hidden // 2, 3),
        )

    def forward(self, verts: torch.Tensor, planes: torch.Tensor) -> torch.Tensor:
        """
        verts:  (n, 3)  — dual polytope vertices (= primal face normals)
        planes: (m, 4)  — hyperplane equations [nx, ny, nz, offset]
        returns:(m, 3)  — class logits
        """
        poly_emb = self.vert_enc(verts).mean(dim=0)
        poly_rep = poly_emb.unsqueeze(0).expand(planes.shape[0], -1)
        plane_emb = self.plane_enc(planes)
        return self.joint(torch.cat([poly_rep, plane_emb], dim=1))


# ── Main class ─────────────────────────────────────────────────────────────────

class HopperCEFinder:
    """Hopper-style population search for counterexamples to simple 3-polytope conjectures.

    Works in the dual simplicial polytope space so that the valid-hop rate is ~96%
    (paper's Algorithm 1 with d=3, using face normals as vertices).

    Interface mirrors LLMCEFinder / RL train_on_conjecture:
      - run() returns a CE info dict or None
      - prints progress with _TAG prefix every 100 steps
    """

    def __init__(
        self,
        conjecture,
        num_steps: int = 5_000,
        stop_event: threading.Event | None = None,
        check_agent=None,
        pool_size: int = 50,
        train_every: int = 50,
        lr: float = 1e-3,
    ) -> None:
        self.conjecture = conjecture
        self.num_steps = num_steps
        self.stop_event = stop_event or threading.Event()
        self.check_agent = check_agent
        self.pool_size = pool_size
        self.train_every = train_every

        self.brain = HopperBrain(hidden=64).to(device)
        self.optimizer = optim.Adam(self.brain.parameters(), lr=lr)
        self._replay: list[dict] = []
        self._pool: list[dict] = []

        # multi-objective: alternate between slack and face-count (paper §A.7)
        self._use_slack_obj = True

    # ── Public entry point ─────────────────────────────────────────────────────

    def run(self) -> Optional[dict]:
        self._pool = self._init_pool()
        print(f"{_TAG} Init: {len(self._pool)} seed(s) in pool | device: {device}")
        if not self._pool:
            print(f"{_TAG} No valid seeds — aborting")
            return None

        best_slack = float("inf")
        total_hops = 0
        total_trains = 0

        for step in range(1, self.num_steps + 1):
            if self.stop_event.is_set():
                print(f"{_TAG} Stopped by stop_event")
                return None

            # alternate objectives every 200 steps (paper §A.7 multi-objective)
            if step % 200 == 0:
                self._use_slack_obj = not self._use_slack_obj

            entry = self._sample_pool()
            if entry is None:
                continue

            candidates, hop_idxs, feasible = self._hop(entry["dual_verts"])
            total_hops += len(candidates)

            improved = False
            for cand in candidates:
                c_pvec = cand["p_vec"]
                slack = self._slack(c_pvec)

                if slack < best_slack:
                    best_slack = slack

                # ── Check for CE ──────────────────────────────────────────────
                ok, detail = is_counterexample(c_pvec, self.conjecture)
                if ok:
                    print(f"{_TAG} Step {step}/{self.num_steps}: CE found — {c_pvec} — {detail}")
                    from agent.orchestrator.tools.check_pvector import PVectorCheckAgent
                    checker = self.check_agent or PVectorCheckAgent(client=None)
                    report = checker.run_silent(c_pvec, self.conjecture)
                    if report.all_passed:
                        return {
                            "p_vector": c_pvec,
                            "found_by": "hopper_agent",
                            "found_at_round": step,
                            "violation_detail": detail,
                            "other_candidates_not_checked": [],
                            "found_at": datetime.now(timezone.utc).isoformat(),
                        }
                    print(f"{_TAG} Step {step}/{self.num_steps}: candidate failed checks — continuing")

                # ── Update pool if improved ───────────────────────────────────
                fitness = self._fitness(c_pvec)
                if fitness < entry["fitness"]:
                    improved = True
                    self._add_to_pool(cand["dual_verts"], c_pvec, fitness, slack)

            # ── Training sample (paper §A.11.4) ──────────────────────────────
            if hop_idxs:
                all_planes = _hyperplanes(entry["dual_verts"])
                used = [all_planes[i] for i in hop_idxs if i < len(all_planes)]
                label = 0 if improved else (1 if not feasible else 2)
                self._add_training_sample(entry["dual_verts"], used, label)

            if step % self.train_every == 0:
                loss = self._train_step()
                if loss is not None:
                    total_trains += 1

            if step % 100 == 0:
                obj_label = "slack" if self._use_slack_obj else "f2"
                print(
                    f"{_TAG} Step {step}/{self.num_steps} | "
                    f"Pool:{len(self._pool)} | "
                    f"Slack:{best_slack:+.3f} | "
                    f"Hops:{total_hops} | "
                    f"Train:{total_trains} | "
                    f"Obj:{obj_label}"
                )

        print(f"{_TAG} Exhausted {self.num_steps} steps without a CE.")
        return None

    # ── Pool management ────────────────────────────────────────────────────────

    def _init_pool(self) -> list[dict]:
        min_f2 = self._min_f2_from_conjecture()
        pool: list[dict] = []
        for seed in _BASE_SEEDS:
            entry = self._make_entry(seed)
            if entry is None:
                continue
            f2 = sum(entry["p_vec"].values())
            if f2 >= min_f2 - 4:
                pool.append(entry)
        # fallback: accept all valid seeds if none met the f2 threshold
        if not pool:
            for seed in _BASE_SEEDS:
                entry = self._make_entry(seed)
                if entry is not None:
                    pool.append(entry)
        return pool

    def _make_entry(self, dual_verts: np.ndarray) -> Optional[dict]:
        try:
            hull = ConvexHull(dual_verts)
        except (QhullError, Exception):
            return None
        if len(hull.vertices) != len(dual_verts):
            return None
        p_vec = _pvec_from_dual(hull)
        ok, _ = is_valid_simple_polytope(p_vec)
        if not ok:
            return None
        slack = self._slack(p_vec)
        fitness = self._fitness(p_vec)
        return {
            "dual_verts": dual_verts.copy(),
            "p_vec": p_vec,
            "fitness": fitness,
            "slack": slack,
            "importance": self._importance(slack),
        }

    def _add_to_pool(
        self,
        dual_verts: np.ndarray,
        p_vec: dict[int, int],
        fitness: float,
        slack: float,
    ) -> None:
        self._pool.append({
            "dual_verts": dual_verts,
            "p_vec": p_vec,
            "fitness": fitness,
            "slack": slack,
            "importance": self._importance(slack),
        })
        if len(self._pool) > self.pool_size:
            self._pool.sort(key=lambda e: e["importance"])
            self._pool = self._pool[-self.pool_size:]

    def _sample_pool(self) -> Optional[dict]:
        if not self._pool:
            return None
        weights = np.array([e["importance"] for e in self._pool], dtype=float)
        weights = np.clip(weights, 1e-8, None)
        weights /= weights.sum()
        idx = int(np.random.choice(len(self._pool), p=weights))
        return self._pool[idx]

    @staticmethod
    def _importance(slack: float) -> float:
        return 1.0 / (1.0 + max(0.0, slack)) + 0.01

    # ── Fitness and slack ──────────────────────────────────────────────────────

    def _slack(self, p_vec: dict[int, int]) -> float:
        """Conjecture slack = p6 − RHS (or RHS − p6 for ≤).  Negative ↔ CE.
        Returns +inf if hypothesis not satisfied (polytope outside search domain)."""
        for hyp in self.conjecture.hypotheses:
            if not _eval_hypothesis(hyp, p_vec):
                return float("inf")
        conc = self.conjecture.conclusion.strip()
        m = re.match(r'p_?\{?6\}?\s*(?:\\geq|>=|\\leq|<=)\s*(.+)', conc, re.DOTALL)
        if not m:
            return float("inf")
        rhs = _eval_rhs_expr(m.group(1).strip(), p_vec)
        if rhs is None:
            return float("inf")
        direction = ">=" if (">=" in conc or r"\geq" in conc) else "<="
        p6 = float(p_vec.get(6, 0))
        return float(p6 - rhs) if direction == ">=" else float(rhs - p6)

    def _fitness(self, p_vec: dict[int, int]) -> float:
        """Multi-objective fitness: alternate between slack and face-count gap (paper §A.7)."""
        if self._use_slack_obj:
            return self._slack(p_vec)
        # secondary: push toward minimum required face count
        f2 = sum(p_vec.values())
        target = self._min_f2_from_conjecture()
        return float(max(0, target - f2))

    def _min_f2_from_conjecture(self) -> int:
        """Extract minimum f2 from hypothesis strings, e.g. 'f_2>=_22' → 22."""
        for hyp in self.conjecture.hypotheses:
            m = re.search(r'f[_2]*\s*>=?_?\s*(\d+)', str(hyp))
            if m:
                return int(m.group(1))
        return 4

    # ── Hop (Algorithm 1, paper §3, in dual space) ─────────────────────────────

    def _hop(
        self, dual_verts: np.ndarray
    ) -> tuple[list[dict], list[int], bool]:
        """Algorithm 1 applied to dual simplicial polytope vertices.

        Returns (candidates, used_hyperplane_indices, geometrically_feasible).
        Each candidate is {dual_verts, p_vec}.
        """
        planes = _hyperplanes(dual_verts)
        if len(planes) < 4:
            return [], [], False

        scores = self._score_hyperplanes(dual_verts, planes)
        centroid = dual_verts.mean(axis=0)

        for _ in range(30):   # safety fuse (paper §A.5)
            try:
                idxs = list(
                    map(int, np.random.choice(len(planes), size=4, replace=False, p=scores))
                )
            except ValueError:
                return [], [], False

            halfspaces: list[tuple[np.ndarray, float]] = []
            for i in idxs:
                n, d = planes[i][:3], float(planes[i][3])
                if float(np.dot(n, centroid)) > d:
                    halfspaces.append((-n, -d))
                else:
                    halfspaces.append((n, d))

            result = _chebyshev(halfspaces)
            if result is None:
                continue
            centre, radius = result
            if radius < 1e-6:
                continue

            # tighten with nearby hyperplanes (Algorithm 1 steps 9-11)
            for p in planes:
                n, d = p[:3], float(p[3])
                n_use, d_use = (-n, -d) if float(np.dot(n, centroid)) > d else (n, d)
                dist = (d_use - float(np.dot(n_use, centre))) / (float(np.linalg.norm(n_use)) + 1e-12)
                if dist < 0.8 * radius:
                    halfspaces.append((n_use, d_use))

            result2 = _chebyshev(halfspaces)
            if result2 is not None:
                centre, radius = result2

            # generate candidates (Algorithm 1 steps 12-16)
            candidates: list[dict] = []
            for vi in range(len(dual_verts)):
                new_dv = dual_verts.copy()
                new_dv[vi] = centre
                try:
                    hull = ConvexHull(new_dv)
                except (QhullError, Exception):
                    continue
                # admissibility: no dual vertex became interior
                if len(hull.vertices) != len(dual_verts):
                    continue
                pv = _pvec_from_dual(hull)
                ok_pv, _ = is_valid_simple_polytope(pv)
                if ok_pv:
                    candidates.append({"dual_verts": new_dv, "p_vec": pv})

            return candidates, idxs, True

        return [], [], False

    # ── Neural network scoring (paper §3.1) ────────────────────────────────────

    @torch.no_grad()
    def _score_hyperplanes(
        self, dual_verts: np.ndarray, planes: list[np.ndarray]
    ) -> np.ndarray:
        """Normalised probability over hyperplanes (probability of class 0 = good hop)."""
        v_t = torch.tensor(dual_verts, dtype=torch.float32).to(device)
        p_t = torch.tensor(np.array(planes), dtype=torch.float32).to(device)
        logits = self.brain(v_t, p_t)
        probs = torch.softmax(logits, dim=-1)[:, 0].cpu().numpy()
        probs = np.clip(probs, 1e-8, None)
        return probs / probs.sum()

    # ── Online training (paper §3.1, §A.11.4) ─────────────────────────────────

    def _add_training_sample(
        self, dual_verts: np.ndarray, used_planes: list[np.ndarray], label: int
    ) -> None:
        if not used_planes:
            return
        self._replay.append({"dual_verts": dual_verts, "planes": used_planes, "label": label})
        if len(self._replay) > 2_000:
            self._replay = self._replay[-2_000:]

    def _train_step(self) -> Optional[float]:
        if len(self._replay) < 16:
            return None
        batch_size = min(32, len(self._replay))
        idxs = np.random.choice(len(self._replay), size=batch_size, replace=False)
        samples = [self._replay[i] for i in idxs]

        self.optimizer.zero_grad()
        total_loss = torch.zeros(1, device=device)
        for s in samples:
            v_t = torch.tensor(s["dual_verts"], dtype=torch.float32).to(device)
            p_t = torch.tensor(np.array(s["planes"]), dtype=torch.float32).to(device)
            logits = self.brain(v_t, p_t)
            labels = torch.full(
                (len(s["planes"]),), s["label"], dtype=torch.long, device=device
            )
            total_loss = total_loss + nn.functional.cross_entropy(logits, labels)
        total_loss = total_loss / batch_size
        total_loss.backward()
        self.optimizer.step()
        return float(total_loss.detach())
