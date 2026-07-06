"""Independence check for PROVED conjectures vs. the known results.

Question (supervisor, 2026-07-05): are the proved conjectures independent
of the previously known theorems — i.e. NOT just (nonnegative) linear
combinations of them?

Known results (sphere, g = 0; variables p_k >= 0, S := sum_{k>=7} p_k),
exactly as axiomatized in polib/Inventory.lean:

  (E)  Euler/Eberhard identity   3*p3 = 12 - 2*p4 - p5 + sum_{k>=7} (k-6)*p_k
       [Inventory: Juc_EulerFormula / P6EdgeCountEquation]
  (J)  Jucovic 1971              3*p6 >= 12 - 2*p4 - 3*p5
                                         + sum_{k>=7} (floor((k+1)/2)-6)*p_k
       [Inventory: Juc_InequalityPart / P6InequalityPart]
  (B)  Barnette 1969             2*p6 >= 4 + p3 - p5 - 2*S,  valid only if S >= 3
       [Inventory: Barnette_P6Bound]

Eberhard's theorem PROPER (the existence statement / equality_family) is
never referenced by any proof; "Eberhard" enters only via identity (E).

Verdicts established below (each backed by a machine-checked certificate
or counterexample):

  C124  TRIVIAL     — tautology of nonnegativity alone (0 <= 2*p3 + 2*S);
                      uses no known theorem at all.
  C201  DEPENDENT   — pure nonneg linear combination of (J) + p_k >= 0:
                      explicit Farkas certificate, no integrality needed.
                      (Strictly weaker than Jucovic under its hypotheses.)
  C104  NOT a linear combination — a real point satisfies (E), (J), the
                      hypotheses, and B's guard fails (S = 1 < 3), yet the
                      conclusion is violated; so no Farkas certificate
                      exists. Moreover (E)+(J)+integrality alone are still
                      insufficient (integer counterexample killed only by
                      (B)). C104 IS derivable from (E)+(J)+(B) + the fact
                      that p_k are nonnegative INTEGERS (rounding + case
                      split on S) — an integer-programming corollary of
                      the knowns, with no new geometric input.

POLICY NOTE: this is OFFLINE analysis tooling only. The Inventory-LP
precheck was deliberately removed from the pipeline on 2026-06-15 and must
not be reintroduced as a generation/proving gate or hint provider. Run
manually:

    python3 independence_check.py

Exits 0 iff every certificate/counterexample verifies.
"""

from fractions import Fraction as F

FAILURES: list[str] = []


def a_juc(k: int) -> int:
    """Jucovic coefficient floor((k+1)/2) - 6 for k >= 7."""
    return (k + 1) // 2 - 6


def check(cond: bool, label: str) -> None:
    tag = "OK  " if cond else "FAIL"
    print(f"    [{tag}] {label}")
    if not cond:
        FAILURES.append(label)


def check_c104_point(name: str, p: dict[int, F]) -> None:
    """Verify a candidate counterexample against (E), (J), guarded (B),
    the C104 hypotheses, and the C104 conclusion (which must FAIL)."""
    get = lambda k: p.get(k, F(0))
    S = sum(v for k, v in p.items() if k >= 7)
    N = sum(p.values())
    print(f"  {name}: p = {{{', '.join(f'{k}:{v}' for k, v in sorted(p.items()))}}}")

    check(3 * get(3) == 12 - 2 * get(4) - get(5)
          + sum((k - 6) * v for k, v in p.items() if k >= 7),
          "Euler/Eberhard identity (E) holds")
    check(3 * get(6) >= 12 - 2 * get(4) - 3 * get(5)
          + sum(a_juc(k) * v for k, v in p.items() if k >= 7),
          "Jucovic inequality (J) holds")
    if S >= 3:
        barnette_holds = 2 * get(6) >= 4 + get(3) - get(5) - 2 * S
        check(not barnette_holds,
              f"Barnette applies (S={S}>=3) and is VIOLATED "
              "-> only (B) excludes this point")
    else:
        check(True, f"Barnette guard S={S} < 3 -> vacuous (unusable here)")
    check(get(4) == 0 and get(5) <= 2 and N >= 7,
          f"C104 hypotheses p4=0, p5<=2, total N={N}>=7 hold")
    check(not (2 * get(6) >= 4 - S),
          f"C104 conclusion 2*p6 >= 4-S is VIOLATED ({2 * get(6)} < {4 - S})")
    print()


def main() -> int:
    print("=" * 72)
    print("C104: 2*p6 >= 4 - S  given p4=0, p5<=2, N>=7")
    print("=" * 72)
    # Real point: (E) tight, (J) tight, hypotheses hold, (B) vacuous, and the
    # conclusion fails => C104 is NOT implied over the reals, hence NOT a
    # nonnegative linear combination of the knowns (no Farkas certificate).
    check_c104_point("real counterexample (kills any linear-combination claim)",
                     {3: F(11, 3), 5: F(2), 6: F(4, 3), 7: F(1)})
    # Integer point satisfying (E), (J), hypotheses AND integrality but
    # violating the conclusion: only (B) (applicable, S=3) excludes it.
    # => (E)+(J)+integrality insufficient; Barnette is load-bearing.
    check_c104_point("integer counterexample (shows Barnette is load-bearing)",
                     {3: F(5), 5: F(2), 6: F(0), 7: F(1), 8: F(2)})
    print("  Verdict: NOT a linear combination of {E, J, B}. Derivable from")
    print("  {E, J, B} + integrality of p_k (rounding + case split on S);")
    print("  no geometric property beyond the three knowns is used.")
    print()

    print("=" * 72)
    print("C201: p6 >= 2 - S  given p4=0, p5=0, S>=1")
    print("=" * 72)
    # Farkas certificate:
    #   p6 + S - 2 = (1/3)*[3*p6 - 12 - sum a_juc(k)*p_k]      (J slack, p4=p5=0)
    #                + sum_{k>=7} ((a_juc(k)+3)/3) * p_k        (p_k >= 0)
    #                + 2                                        (constant slack)
    # Coefficient identity checked per variable; all multipliers >= 1/3 > 0.
    ok = True
    for k in range(7, 501):
        mult_k = F(a_juc(k) + 3, 3)
        if F(-a_juc(k), 3) + mult_k != 1 or mult_k <= 0:
            ok = False
    check(ok, "Farkas certificate p6+S-2 = (1/3)*J_slack "
              "+ sum ((a(k)+3)/3)*p_k + 2, multipliers > 0 (k <= 500)")
    print("  Verdict: DEPENDENT — a pure nonneg linear combination of Jucovic")
    print("  + nonnegativity (no integrality, no case split, no Euler, no")
    print("  Barnette). Strictly weaker than Jucovic under its hypotheses.")
    print()

    print("=" * 72)
    print("C124: 2*p6 <= 2*N - 2*p4 - 2*p5")
    print("=" * 72)
    print("  Rearranges to 0 <= 2*p3 + 2*S — a tautology of nonnegativity.")
    print("  Verdict: TRIVIAL — uses no known theorem at all.")
    print()

    print("=" * 72)
    if FAILURES:
        print(f"RESULT: {len(FAILURES)} verification(s) FAILED:")
        for f_ in FAILURES:
            print(f"  - {f_}")
        return 1
    print("RESULT: all certificates/counterexamples verified.")
    print("Summary:  C124 trivial | C201 dependent (LP-weakening of Jucovic)")
    print("          C104 not a linear combination, but an integer-programming")
    print("          corollary of Eberhard-relation + Jucovic + Barnette.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
