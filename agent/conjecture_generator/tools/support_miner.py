"""
agent/conjecture_generator/tools/support_miner.py — support-function miner.

WHY: C104 (`p_4=0 ∧ p_5≤2 ∧ f_2≥7 ⟹ p6 ≥ -Σ₇₊/2 + 2`) — the repo's first
non-trivial Lean-proved theorem — is geometrically a LOWER HULL EDGE of the
verified pool: on its hypothesis cell the point cloud (Σ₇₊, p6) has a tight
supporting line of slope -1/2 touching at ≥ 2 points, and the bound is
FORCED by Dehn-Sommerville (small-face starvation ⇒ hexagons must appear).
Graffiti3's dalmatian LP surfaces such a bound at most once per
configuration and mostly prefers data-ceiling upper bounds — exactly the
class the failed bucket shows being slaughtered by hexagon-band CEs.
Nothing sweeps the pool's support function in the PROVABLE direction.
This miner does:

  for each hypothesis CELL (small-face atoms × optional f_2 floor)
    for each RHS variable v ∈ {p3, p4, p5, Σ₇₊} not pinned by the cell
      for each slope a in a denominator-≤6 menu
        c(a) = min over cell rows of (p6 - a·v)      ← exact, integer math
        emit `p6 >= a·v + c` iff
          • non-vacuous (a > 0 or c > 0),
          • supported (≥ MIN_SUPPORT rows),
          • a true EDGE: ≥ 2 touching rows at DISTINCT v (single-vertex
            contact = boring in-between slope).

Every emission is tight and pool-consistent BY CONSTRUCTION (the min is
attained), denominators ≤ 6 by menu choice. Lower bounds only — that is the
DS-provable direction; ceiling-hugging upper bounds are left to sources the
hard gates can discipline. The generator's gates still get the final word.
"""
from __future__ import annotations

from fractions import Fraction

MINER_MAX = 12
MIN_SUPPORT = 30

# Slope menu: every rational in [-3, 3] with denominator ∈ {1, 2, 3, 6}
# that experience says renders into Lean-friendly bounds. 0 = constant
# lower bounds (Eberhard-style "at least c hexagons on this cell").
_SLOPES = [Fraction(n, d) for n, d in (
    (-3, 1), (-2, 1), (-3, 2), (-1, 1), (-2, 3), (-1, 2), (-1, 3), (-1, 6),
    (0, 1), (1, 6), (1, 3), (1, 2), (2, 3), (1, 1), (3, 2), (2, 1), (3, 1),
)]

_VARS = {
    "p3": lambda pv: pv.get(3, 0),
    "p4": lambda pv: pv.get(4, 0),
    "p5": lambda pv: pv.get(5, 0),
    "sum_pk_after_p6": lambda pv: sum(n for k, n in pv.items() if k >= 7),
}

# (label, DSL atom, row predicate, constrained var, pins-var-to-a-point)
_ATOMS = [
    ("p3=0",  "(p_3 = 0)",  lambda pv: pv.get(3, 0) == 0, "p3", True),
    ("p4=0",  "(p_4 = 0)",  lambda pv: pv.get(4, 0) == 0, "p4", True),
    ("p5=0",  "(p_5 = 0)",  lambda pv: pv.get(5, 0) == 0, "p5", True),
    ("p3<=2", "(p_3 <= 2)", lambda pv: pv.get(3, 0) <= 2, "p3", False),
    ("p4<=2", "(p_4 <= 2)", lambda pv: pv.get(4, 0) <= 2, "p4", False),
    ("p5<=2", "(p_5 <= 2)", lambda pv: pv.get(5, 0) <= 2, "p5", False),
]

# f_2 floors: None (whole cell) or exclude the tiny-polytope corner that
# drags the hull down (C104 needed f_2 ≥ 7 to shed the tetrahedron family).
_F2_FLOORS = (None, 7, 17)


def _fmt(q: Fraction) -> str:
    if q.denominator == 1:
        return str(q.numerator)
    return f"{float(q):.10g}"


def _cell_combos():
    """Single atoms + cross-variable pairs."""
    singles = [[a] for a in _ATOMS]
    pairs = [[_ATOMS[i], _ATOMS[j]]
             for i in range(len(_ATOMS))
             for j in range(i + 1, len(_ATOMS))
             if _ATOMS[i][3] != _ATOMS[j][3]]
    return singles + pairs


def _render(atom_dsls: list[str], floor, a: Fraction, v: str, c: Fraction) -> str:
    hyp = ["(is_simple)"] + atom_dsls
    if floor is not None:
        hyp.append(f"(f_2>=_{floor})")
    if a == 0:
        rhs = _fmt(c)
    elif c == 0:
        rhs = f"({_fmt(a)} * {v})"
    else:
        rhs = f"(({_fmt(a)} * {v}) + {_fmt(c)})"
    return f"if ({' and '.join(hyp)}), then p6 >= ({rhs})"


def mine_support_bounds(
    pool: list[dict[int, int]],
    known_formulas: set[str] | None = None,
    max_out: int = MINER_MAX,
) -> list[tuple[str, str]]:
    """Return up to `max_out` (formula, source) tight lower bounds, ranked by
    touch count (how many pool rows achieve equality — the tighter the edge,
    the higher the IRIS-T downstream and the more it constrains reality)."""
    from agent.conjectures import canonicalize_formula  # lazy: avoid cycles

    known = known_formulas or set()
    scored: list[tuple[int, int, str, str]] = []
    seen: set[str] = set()

    for atoms in _cell_combos():
        preds = [a[2] for a in atoms]
        dsls = [a[1] for a in atoms]
        label = "&".join(a[0] for a in atoms)
        pinned = {a[3] for a in atoms if a[4]}
        base_rows = [pv for pv in pool if all(p(pv) for p in preds)]
        for floor in _F2_FLOORS:
            rows = (base_rows if floor is None else
                    [pv for pv in base_rows if sum(pv.values()) >= floor])
            if len(rows) < MIN_SUPPORT:
                continue
            for vname, vfn in _VARS.items():
                if vname in pinned:
                    continue
                pts = [(vfn(pv), pv.get(6, 0)) for pv in rows]
                for a in _SLOPES:
                    n, d = a.numerator, a.denominator
                    # score = d·p6 - n·v  (integer); c = min(score)/d
                    scores = [d * p6 - n * v for v, p6 in pts]
                    c_int = min(scores)
                    c = Fraction(c_int, d)
                    if a <= 0 and c <= 0:
                        continue                      # vacuous bound
                    touch_idx = [i for i, s in enumerate(scores) if s == c_int]
                    touch_vs = {pts[i][0] for i in touch_idx}
                    if len(touch_vs) < 2:
                        continue                      # vertex, not an edge
                    formula = canonicalize_formula(
                        _render(dsls, floor, a, vname, c))
                    if formula in seen or formula in known:
                        continue
                    seen.add(formula)
                    scored.append((len(touch_idx), len(rows), formula,
                                   f"miner:{label}:{vname}"))

    scored.sort(key=lambda t: (t[0], t[1]), reverse=True)
    return [(f, src) for _, _, f, src in scored[:max_out]]
