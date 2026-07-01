"""IRIS scoring (T, R, L) for a conjecture, evaluated on the verified pool.

Mirrors the formulas from the original Polytope repo
(github.com/FELIXGAO0315/Polytope, agents/conjecture_agent.py):

  T = |{x ∈ support : |slack(x)| ≤ eps}|  /  |support|
      "touch fraction" — how often the inequality is tight on the support.

  R = rank(X_touch.T) / |touch|
      "normalised rank" of the touching points' feature matrix —
      the diversity of polytopes that achieve equality.

  L = diam(X_touch) / diam(X_support)
      "normalised diameter" — geometric spread of the touching points
      relative to the full support.

`support` = polytopes in the verified pool where every hypothesis of the
conjecture is satisfied. `slack` is signed `p6 - rhs(p_vec)` for a `>=` bound
and `rhs(p_vec) - p6` for a `<=` bound, so |slack| measures distance to the
boundary in either direction.

Sort keys consumed by `agent/rl_ce_finder/agent.py::_iris_sort_key`:
  T, R, L, TR=T·R, TL=T·L, RL=R·L, TRL=T·R·L.
"""
from __future__ import annotations

from typing import Any, Dict, List, Optional

import numpy as np

from agent.conjectures import ConjectureSpec
from agent.orchestrator.tools.conjecture_parser import ParsedConjecture
from agent.orchestrator.tools.pvec_eval import (
    _compile_conclusion,
    _eval_hypothesis,
)

EPS = 1e-6
# 6-dimensional feature vector per p-vector.
# Stable ordering matters for the matrix rank / diameter to be reproducible.
_FEATURE_NAMES = ("p_3", "p_4", "p_5", "p_6", "sum_pk_k>=7", "f_2")


def _features(pv: Dict[int, int]) -> List[float]:
    return [
        float(pv.get(3, 0)),
        float(pv.get(4, 0)),
        float(pv.get(5, 0)),
        float(pv.get(6, 0)),
        float(sum(v for k, v in pv.items() if k >= 7)),
        float(sum(pv.values())),
    ]


def _pairwise_max_dist(X: np.ndarray) -> float:
    """Max pairwise Euclidean distance in X (rows = points). Returns 0 for
    fewer than 2 rows. Avoids the sklearn dep."""
    n = X.shape[0]
    if n < 2:
        return 0.0
    # (n,1,d) - (1,n,d) → (n,n,d). Fine at our pool size (≤ a few thousand).
    diffs = X[:, None, :] - X[None, :, :]
    d2 = np.einsum("ijk,ijk->ij", diffs, diffs)
    return float(np.sqrt(d2.max()))


def compute_iris(spec: ConjectureSpec,
                 row_pvecs: List[Dict[int, int]],
                 eps: float = EPS) -> Optional[Dict[str, Any]]:
    """Return {'T','R','L','iris_score','sort_keys','support','touch'} or
    None if the conjecture cannot be evaluated / has no support."""
    try:
        parsed = ParsedConjecture.from_conjecture_spec(spec)
    except Exception:
        return None
    kind, rhs_fn = _compile_conclusion(parsed.conclusion)
    if kind == "unknown" or rhs_fn is None:
        return None

    sign = 1.0 if kind == "ge" else -1.0   # slack = sign * (p6 - rhs)
    slack: List[float] = []
    feats: List[List[float]] = []
    for pv in row_pvecs:
        try:
            if not all(_eval_hypothesis(h, pv) for h in parsed.hypotheses):
                continue
            rhs = float(rhs_fn(pv))
            p6 = float(pv.get(6, 0))
        except Exception:
            continue
        slack.append(sign * (p6 - rhs))
        feats.append(_features(pv))

    n_support = len(slack)
    if n_support == 0:
        return None
    slack_arr = np.asarray(slack, dtype=float)
    X = np.asarray(feats, dtype=float)
    touch_mask = np.abs(slack_arr) <= eps
    n_touch = int(touch_mask.sum())

    T = float(n_touch) / float(n_support)
    if n_touch == 0:
        R = 0.0
        L = 0.0
    else:
        X_touch = X[touch_mask, :]
        # R: rank of touching points in feature space, normalised by |touch|.
        # Matches old repo: rank(X_touch.T) / t  (transposing doesn't change rank).
        try:
            r = float(np.linalg.matrix_rank(X_touch))
        except Exception:
            r = 0.0
        R = r / float(n_touch)
        # L: diameter ratio.
        diam_t = _pairwise_max_dist(X_touch)
        diam_all = _pairwise_max_dist(X)
        L = (diam_t / diam_all) if diam_all > 1e-12 else 0.0

    iris_score = T + R + L
    return {
        "T": T,
        "R": R,
        "L": L,
        "iris_score": iris_score,
        "sort_keys": {
            "T":   T,
            "R":   R,
            "L":   L,
            "TR":  T * R,
            "TL":  T * L,
            "RL":  R * L,
            "TRL": T * R * L,
        },
        "support": n_support,
        "touch": n_touch,
        "feature_names": list(_FEATURE_NAMES),
        "eps": eps,
    }
