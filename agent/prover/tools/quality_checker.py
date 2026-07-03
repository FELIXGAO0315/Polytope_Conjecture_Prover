"""Stage-4 per-node quality gate.

The 4 rules below run every time a proof-agent produces a candidate .lean for
a node.  A node is admitted to Polib only if EVERY applicable rule passes.

  R1  Soundness guard    — no SimplyCon3ConnectedMap instance construction
                            (Inventory has sorry axioms; a fabricated
                            instance lets you derive False).
  R2  Sorry/admit audit  — no `sorry` or `admit` in non-comment portions.
  R3  Axiom sweep        — no inline `axiom` declaration (only Inventory
                            may declare axioms).
  R4  Formula fidelity   — only for the ROOT theorem:
                            R4a  declaration name present in lean_code
                            R4b  every numeric constant in JSON hypotheses
                                 appears in the locked signature
                            R4c  conclusion direction (≤/≥) matches
                            R4d  LLM semantic verdict on locked sig vs JSON
                                 (fail-closed on LLM failure)

Verbatim signature substring match is NOT a rule here — it is enforced
STRUCTURALLY at stage 6 (deep_check D2, which walks binders + normalizes
the conclusion).  Duplicating it here would just repeat the same complaint
twice at different stages.
"""
from __future__ import annotations

import os
import re
from dataclasses import dataclass, field

from agent.prover.tools.goal_lock import LockedGoal
from agent.prover.tools.lean_compiler import find_struct_construction
from agent.prover.tools.parsed_theorem import ParsedTheorem


# ---------------------------------------------------------------------------
# Report — only the fields consumed downstream survive
# ---------------------------------------------------------------------------

@dataclass
class QualityReport:
    """Per-node stage-4 verdict.

    Downstream consumers (checked with `grep`):
      * ``passed``       — _node_solver_mixin gates polib admission on this
      * ``sorry_count``  — _node_solver_mixin logs / polib_manager rejects >0
      * ``findings``     — pipeline logs the FAIL/WARN entries
      * ``score``        — 1.0 iff passed; kept for dashboards
      * ``summary``      — one-liner for the finalisation logger
    Anything else was dead weight; removed.
    """
    passed: bool
    score: float
    sorry_count: int
    findings: list[str] = field(default_factory=list)
    summary: str = ""


# ---------------------------------------------------------------------------
# Non-comment scanning: strips ``--`` line comments AND their prefixes
# ---------------------------------------------------------------------------

_SORRY_RE = re.compile(r"\b(?:sorry|admit)\b")
_AXIOM_RE = re.compile(r"\baxiom\s+\w+")

# Direction-check anchors, keyed off the JSON formula conclusion.
_LE_CONC_RE = re.compile(r"p_?\{?6\}?\s*(?:<=|\\leq)")
_GE_CONC_RE = re.compile(r"p_?\{?6\}?\s*(?:>=|\\geq)")


def _strip_comments(lean_code: str) -> str:
    """Return ``lean_code`` with every ``--`` line-comment tail cut, so the
    non-comment scanners can't false-positive on things like
    ``rw [foo] -- sorry ain't in here``.

    We intentionally do NOT strip block comments ``/- ... -/`` because none of
    our current scanners care about them; adding block-comment stripping later
    is a one-liner if a rule wants it."""
    out: list[str] = []
    for line in lean_code.splitlines():
        idx = line.find("--")
        out.append(line[:idx] if idx >= 0 else line)
    return "\n".join(out)


def _count_sorry(lean_code: str) -> int:
    """Number of `sorry` or `admit` occurrences in non-comment code."""
    return len(_SORRY_RE.findall(_strip_comments(lean_code)))


def _find_axiom_decl(lean_code: str) -> str | None:
    """First inline `axiom X` declaration, or None."""
    m = _AXIOM_RE.search(_strip_comments(lean_code))
    return m.group(0) if m else None


# ---------------------------------------------------------------------------
# Formula fidelity — R4b constant match, R4c direction match
# ---------------------------------------------------------------------------

def _hyp_required_numerals(hyp: str) -> list[str]:
    """Numeric constants a hypothesis REQUIRES to appear in the locked
    signature.  Only known JSON hypothesis grammars are enumerated —
    everything else returns [] and is covered by the R4d semantic check.
    """
    flat = re.sub(r"[()]", "", hyp).strip()
    ns = flat.replace(" ", "")
    if flat == "is_simple" or flat.startswith("\\text"):
        return []

    if (m := re.fullmatch(r"f_2(?:>=|<=)_(\d+)", ns)):
        return [m.group(1)]
    if (m := re.fullmatch(r"sum_pk_k>=7(?:>=|<=)(\d+)", ns)):
        return ["7", m.group(1)]
    if (m := re.match(
        r"\\sum_\{k\s*(?:\\geq|\\ge|>=)\s*(\d+)\}\s*p_k\s*"
        r"(?:\\geq|\\leq|>=|<=)\s*(\d+)", flat)):
        return [m.group(1), m.group(2)]
    if (m := re.match(r"f_(?:\{2\}|2)\s*(?:\\geq|\\leq|>=|<=)\s*(\d+)", flat)):
        return [m.group(1)]
    if (m := re.match(r"p_\{?(\d+)\}?\s*(?:\\geq|\\leq|>=|<=|=)\s*(\d+)", flat)):
        return [m.group(1), m.group(2)]
    return []


def _check_constant_fidelity(parsed: ParsedTheorem, sig: str) -> tuple[bool, list[str]]:
    findings: list[str] = []
    ok = True
    for hyp in parsed.hypotheses:
        for n in _hyp_required_numerals(hyp):
            if not re.search(rf"(?<!\d){re.escape(n)}(?!\d)", sig):
                ok = False
                findings.append(
                    f"R4b Constant fidelity: FAIL — hypothesis {hyp!r} "
                    f"requires numeral {n} in the Lean signature"
                )
    if ok:
        findings.append("R4b Constant fidelity: PASS")
    return ok, findings


def _check_direction(parsed: ParsedTheorem, sig: str) -> tuple[bool, list[str]]:
    conc = (parsed.conclusion or "").strip()
    if _GE_CONC_RE.match(conc) and not re.search(r"≥|>=", sig):
        return False, ["R4c Direction: FAIL — conclusion ≥-form; signature has no ≥"]
    if _LE_CONC_RE.match(conc) and not re.search(r"≤|<=", sig):
        return False, ["R4c Direction: FAIL — conclusion ≤-form; signature has no ≤"]
    return True, ["R4c Direction: PASS"]


# ---------------------------------------------------------------------------
# R4d — LLM semantic faithfulness on the locked signature
# ---------------------------------------------------------------------------

_FAITHFULNESS_PROMPT = """You are auditing whether a Lean 4 signature faithfully represents a JSON conjecture.

# JSON conjecture
Hypotheses:
{hypotheses}

Conclusion:
{conclusion}

# Locked Lean 4 signature
{lean_signature}

# Ground rules
- Variable renaming is faithful: `p6` ≡ `maps.p_i 6`, `sum_pk_after_p6` ≡ `∑ k ∈ Finset.Ico 7 …`, `>=` ≡ `≥`.
- `is_simple` maps to `maps : SimplyCon3ConnectedMap 0`.
- Bounds like `f_2 >= 22` map to a named binder `h_f2 : maps.f_2 ≥ 22` (or equivalent).
- The structural parameter `maps : SimplyCon3ConnectedMap g` is NEVER an extra constraint — it encodes the domain.
- Multiplying both sides of the conclusion by a positive integer to clear a `0.5` (e.g. Lean writes `2*p_6 ≤ 2*f_2 - 2*p_4 - 2*p_5` for the JSON `p_6 ≤ 2 + 0.5*(2*f_2 - 4) - p_4 - p_5`) IS faithful.

Answer with EXACTLY this format (nothing else before/after):
CONCLUSION_MATCH: yes/no
HYPOTHESES_COVERED: yes/no
NO_EXTRA_CONSTRAINTS: yes/no
OVERALL_FAITHFUL: yes/no
REASON: <one sentence, only if any answer above is no>"""


# ---------------------------------------------------------------------------
# Checker
# ---------------------------------------------------------------------------

class QualityChecker:
    def __init__(self, client=None, model: str = "claude-sonnet-4-5"):
        self._client = client  # ClaudeSDKClient (needs ._call)
        self._model = model

    def check(
        self,
        parsed: ParsedTheorem,
        goal: LockedGoal,
        lean_code: str,
        is_main_target: bool = True,
    ) -> QualityReport:
        """Run R1–R4 against ``lean_code``.  Fail-fast: rules run in order
        and the first FAIL returns immediately with a populated report.

        Helper nodes (``is_main_target=False``) skip R4 — their signatures
        are LLM-invented stepping stones, not the JSON conjecture.
        """
        findings: list[str] = []

        # ── R1  Soundness guard ──────────────────────────────────────────
        struct = find_struct_construction(lean_code)
        if struct:
            findings.append(f"R1 Soundness guard: FAIL — {struct}")
            return _failed(findings, sorry_count=0)
        findings.append("R1 Soundness guard: PASS")

        # ── R2  Sorry / admit audit ──────────────────────────────────────
        sorry_count = _count_sorry(lean_code)
        if sorry_count > 0:
            findings.append(
                f"R2 Sorry/admit audit: FAIL — {sorry_count} occurrence(s)")
            return _failed(findings, sorry_count=sorry_count)
        findings.append("R2 Sorry/admit audit: PASS")

        # ── R3  Axiom sweep ──────────────────────────────────────────────
        axiom = _find_axiom_decl(lean_code)
        if axiom:
            findings.append(
                f"R3 Axiom sweep: FAIL — found `{axiom}` (only Inventory "
                f"may declare axioms)")
            return _failed(findings, sorry_count=0)
        findings.append("R3 Axiom sweep: PASS")

        if not is_main_target:
            findings.append("R4 Formula fidelity: N/A (intermediate helper node)")
            return _passed(findings)

        # ── R4a  Declaration name present ────────────────────────────────
        theorem_name = goal.lean_signature.split("(")[0].strip().split()[-1]
        if not re.search(rf'(?:theorem|lemma)\s+{re.escape(theorem_name)}\b', lean_code):
            findings.append(f"R4a Declaration name: FAIL — `{theorem_name}` not found")
            return _failed(findings, sorry_count=0)
        findings.append(f"R4a Declaration name: PASS — `{theorem_name}`")

        # ── R4b  Constant fidelity ───────────────────────────────────────
        ok, msgs = _check_constant_fidelity(parsed, goal.lean_signature)
        findings.extend(msgs)
        if not ok:
            return _failed(findings, sorry_count=0)

        # ── R4c  Direction match ─────────────────────────────────────────
        ok, msgs = _check_direction(parsed, goal.lean_signature)
        findings.extend(msgs)
        if not ok:
            return _failed(findings, sorry_count=0)

        # ── R4d  LLM semantic faithfulness (fail-closed) ─────────────────
        ok, msgs = self._semantic_faithfulness_check(parsed, goal)
        findings.extend(msgs)
        if not ok:
            return _failed(findings, sorry_count=0)

        return _passed(findings)

    # ------------------------------------------------------------------
    # LLM helper — kept as a public-ish method because deep_check historically
    # imported it.  With D5 removed from stage 6 nothing else calls this; it's
    # now purely an implementation detail of R4d.
    # ------------------------------------------------------------------

    def _semantic_faithfulness_check(
        self, parsed: ParsedTheorem, goal: LockedGoal,
    ) -> tuple[bool, list[str]]:
        """Ask the LLM: does the LOCKED signature faithfully encode the JSON
        conjecture?  Fail-closed on no-client / call failure / parse error.
        """
        findings: list[str] = []
        if self._client is None:
            findings.append(
                "R4d Semantic faithfulness: FAIL (fail-closed) — "
                "no client available; faithfulness UNVERIFIED")
            return False, findings

        prompt = _FAITHFULNESS_PROMPT.format(
            hypotheses="\n".join(f"  - {h}" for h in parsed.hypotheses) or "  (none)",
            conclusion=parsed.conclusion,
            lean_signature=goal.lean_type_only,
        )
        timeout = int(os.environ.get("PROVER_QC_TIMEOUT", "90"))
        response: str | None = None
        last_exc: Exception | None = None
        for _ in range(2):  # single retry on transient failure
            try:
                response = self._client._call(prompt, timeout=timeout)
                break
            except Exception as exc:
                last_exc = exc
        if response is None:
            findings.append(
                f"R4d Semantic faithfulness: FAIL (fail-closed) — LLM "
                f"call failed twice ({last_exc!s:.60}); faithfulness UNVERIFIED")
            return False, findings

        try:
            reason = next(
                (l.split("REASON:", 1)[1].strip()
                 for l in response.splitlines()
                 if l.strip().startswith("REASON:")),
                "",
            )
            checks = [
                ("CONCLUSION_MATCH",     "R4d.1 Conclusion match"),
                ("HYPOTHESES_COVERED",   "R4d.2 Hypotheses covered"),
                ("NO_EXTRA_CONSTRAINTS", "R4d.3 No extra constraints"),
                ("OVERALL_FAITHFUL",     "R4d.4 Overall faithful"),
            ]
            all_ok = True
            for key, label in checks:
                ok = f"{key}: yes" in response
                findings.append(
                    f"{label}: {'PASS' if ok else 'FAIL'}"
                    + (f" — {reason}" if not ok and reason else ""))
                all_ok = all_ok and ok
            return all_ok, findings
        except Exception as exc:
            findings.append(
                f"R4d Semantic faithfulness: FAIL (fail-closed) — response "
                f"parse error: {exc!s:.60}")
            return False, findings


# ---------------------------------------------------------------------------
# Small helpers
# ---------------------------------------------------------------------------

def _passed(findings: list[str]) -> QualityReport:
    return QualityReport(
        passed=True, score=1.0, sorry_count=0, findings=findings,
        summary=f"PASSED ({len(findings)} finding(s))",
    )


def _failed(findings: list[str], sorry_count: int) -> QualityReport:
    return QualityReport(
        passed=False, score=0.0, sorry_count=sorry_count, findings=findings,
        summary=f"FAILED ({len(findings)} finding(s))",
    )
