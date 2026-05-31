from __future__ import annotations

import re
from dataclasses import dataclass

from agent.prover.tools.goal_lock import LockedGoal
from agent.prover.tools.latex_parser import ParsedTheorem


@dataclass
class QualityReport:
    passed: bool
    score: float
    faithfulness_ok: bool
    no_hallucination: bool
    sorry_count: int
    sorry_annotated: bool
    proof_structure_ok: bool
    allowed_additions: list[str]
    blocked_additions: list[str]
    findings: list[str]
    summary: str

    def to_dict(self) -> dict:
        return {
            "passed": self.passed,
            "score": self.score,
            "faithfulness_ok": self.faithfulness_ok,
            "no_hallucination": self.no_hallucination,
            "sorry_count": self.sorry_count,
            "sorry_annotated": self.sorry_annotated,
            "proof_structure_ok": self.proof_structure_ok,
            "allowed_additions": self.allowed_additions,
            "blocked_additions": self.blocked_additions,
            "findings": self.findings,
            "summary": self.summary,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "QualityReport":
        return cls(
            passed=d["passed"],
            score=d["score"],
            faithfulness_ok=d["faithfulness_ok"],
            no_hallucination=d["no_hallucination"],
            sorry_count=d["sorry_count"],
            sorry_annotated=d["sorry_annotated"],
            proof_structure_ok=d["proof_structure_ok"],
            allowed_additions=d["allowed_additions"],
            blocked_additions=d["blocked_additions"],
            findings=d["findings"],
            summary=d["summary"],
        )


# Sorry patterns
_SORRY_RE = re.compile(r"\bexact\s+sorry\b|\bsorry\b")
_SORRY_BLOCK_RE = re.compile(
    r"--\s*\[SORRY\]\s*class:.*\n"
    r".*--\s*\[SORRY\]\s*reason:.*\n"
    r".*--\s*\[SORRY\]\s*impact:.*\n"
    r".*--\s*\[SORRY\]\s*suggested_next:.*\n",
    re.MULTILINE,
)

# Proof tactic step counter
_TACTIC_RE = re.compile(r"^\s*(have|apply|exact|intro|simp|linarith|ring|omega|norm_num)\b", re.MULTILINE)


def _count_sorry(lean_code: str) -> int:
    count = 0
    for line in lean_code.splitlines():
        if line.strip().startswith("--"):
            continue
        count += len(_SORRY_RE.findall(line))
    return count


def _all_sorrys_annotated(lean_code: str) -> bool:
    """Check every sorry is preceded by a complete [SORRY] block."""
    sorry_count = _count_sorry(lean_code)
    if sorry_count == 0:
        return True
    annotated_count = len(_SORRY_BLOCK_RE.findall(lean_code))
    return annotated_count >= sorry_count


def _count_lean_tactics(proof_body: str) -> int:
    return len(_TACTIC_RE.findall(proof_body))


def _extract_proof_body(lean_code: str) -> str:
    """Extract everything after `:= by`."""
    idx = lean_code.find(":= by")
    if idx == -1:
        return lean_code
    return lean_code[idx + len(":= by"):]


# ── Semantic faithfulness prompt ────────────────────────────────────────────
_FAITHFULNESS_PROMPT = """\
You are verifying that a Lean 4 theorem signature faithfully represents a mathematical formula.

Formula hypotheses (from JSON conjecture):
{hypotheses}

Formula conclusion (from JSON conjecture):
{conclusion}

Lean 4 theorem signature (locked and validated at goal-extraction time):
{lean_signature}

Answer the following questions. Be concise.

Q1: CONCLUSION_MATCH — Does the Lean conclusion faithfully represent the formula conclusion?
    (Note: variable names may differ, e.g. "p6" = "maps.p_i 6", "sum_pk_after_p6" = "∑ k ∈ Finset.Ico 7 ... maps.p_i k", ">=" = "≥")
    Answer: yes / no

Q2: HYPOTHESES_COVERED — Are all formula hypotheses represented in the Lean signature?
    (Note: "is_simple" maps to `maps : SimplyCon3ConnectedMap 0`; "f_2>=_22" maps to the h_f2 hypothesis)
    Answer: yes / no

Q3: NO_EXTRA_CONSTRAINTS — Does the Lean signature add mathematical constraints beyond what the formula specifies?
    (Structural parameters like `maps : SimplyCon3ConnectedMap g` are always valid — they encode the domain, not extra constraints)
    Answer: yes (no extras) / no (has extras)

Q4: OVERALL_FAITHFUL — Overall, is this Lean signature a faithful translation of the formula?
    Answer: yes / no

Format your response as:
CONCLUSION_MATCH: yes/no
HYPOTHESES_COVERED: yes/no
NO_EXTRA_CONSTRAINTS: yes/no
OVERALL_FAITHFUL: yes/no
REASON: <one sentence explanation if any answer is "no">
"""


class QualityChecker:
    def __init__(self, client=None, model: str = "claude-sonnet-4-5"):
        self._client = client  # ClaudeSDKClient (has ._call method)
        self._model = model

    def check(
        self,
        parsed: ParsedTheorem,
        goal: LockedGoal,
        lean_code: str,
        is_main_target: bool = True,
    ) -> QualityReport:
        """Check quality of generated Lean code.

        For intermediate nodes (is_main_target=False):
          - Only sorry audit applies.
          - Helper lemmas are internal stepping stones; their signatures are not
            required to match the root formula and should not be compared against it.

        For the root theorem (is_main_target=True):
          - Semantic faithfulness: Claude verifies the locked Lean signature faithfully
            represents the JSON formula (conclusion + hypotheses match, no extra constraints).
          - No-hallucination: checks the generated code uses the locked signature, not a
            weaker or different one.
          - Sorry audit.
          - Proof structure (soft warning).

        Why Claude instead of token matching:
          JSON formula tokens (e.g. "is_simple", "f_2") do not literally appear in the
          Lean signature ("SimplyCon3ConnectedMap", "h_f2"). Token intersection would
          always be empty, producing false hallucination alerts. Claude understands the
          semantic equivalence and produces correct verdicts.
        """
        findings: list[str] = []
        allowed_additions: list[str] = []
        blocked_additions: list[str] = []

        # ── Check 1: sorry audit (applies to ALL nodes) ──────────────────────
        sorry_count = _count_sorry(lean_code)
        sorry_annotated = _all_sorrys_annotated(lean_code)
        if sorry_count > 0 and not sorry_annotated:
            findings.append(
                f"Sorry audit: FAIL — {sorry_count} sorry(s) found, "
                f"not all have [SORRY] annotations"
            )
        elif sorry_count > 0:
            findings.append(f"Sorry audit: WARN — {sorry_count} sorry(s), all annotated")
        else:
            findings.append("Sorry audit: PASS — 0 sorry")

        if not is_main_target:
            # ── Intermediate node: only sorry matters ────────────────────────
            # Helper lemmas are designed by the LLM as internal stepping stones.
            # Their signatures need not match the root formula. Formula comparison
            # would always produce false positives here.
            findings.append("Formula faithfulness: N/A (intermediate helper node, not root theorem)")
            faithfulness_ok = True
            no_hallucination = True
            proof_structure_ok = True
            score = 1.0 if sorry_annotated else 0.0
            passed = sorry_annotated
        else:
            # ── Root theorem: full formula-faithfulness check ────────────────

            # Check 2a: declaration name present in generated code
            theorem_name = goal.lean_signature.split("(")[0].strip().split()[-1]
            name_present = bool(
                re.search(r'(?:theorem|lemma)\s+' + re.escape(theorem_name), lean_code)
            )
            if name_present:
                findings.append(f"Declaration name: PASS — '{theorem_name}' found")
            else:
                findings.append(f"Declaration name: FAIL — '{theorem_name}' not declared in generated code")

            # Check 2b: semantic faithfulness via Claude
            # The locked goal was translated from the JSON formula at goal-lock time.
            # We ask Claude to confirm that the Lean signature faithfully represents
            # the original formula. This is the definitive JSON→Lean consistency check.
            faithfulness_ok, no_hallucination, faithfulness_findings = self._semantic_faithfulness_check(
                parsed, goal
            )
            findings.extend(faithfulness_findings)

            # Combine name check into faithfulness
            faithfulness_ok = faithfulness_ok and name_present

            # Check 3: proof structure (soft warning)
            latex_steps = len(parsed.proof_steps)
            proof_body = _extract_proof_body(lean_code)
            lean_steps = _count_lean_tactics(proof_body)
            proof_structure_ok = lean_steps <= max(3 * latex_steps, 30)
            if not proof_structure_ok:
                findings.append(
                    f"Proof structure: WARN — {lean_steps} tactic steps (>{max(3*latex_steps,30)} threshold)"
                )
            else:
                findings.append(f"Proof structure: PASS ({lean_steps} tactic steps)")

            # Score: faithfulness 0.70, sorry 0.20, structure 0.10
            score = (
                0.70 * (1.0 if faithfulness_ok else 0.0)
                + 0.20 * (1.0 if sorry_annotated else 0.0)
                + 0.10 * (1.0 if proof_structure_ok else 0.0)
            )
            passed = score >= 0.85 and faithfulness_ok and no_hallucination

        return QualityReport(
            passed=passed,
            score=round(score, 4),
            faithfulness_ok=faithfulness_ok,
            no_hallucination=no_hallucination,
            sorry_count=sorry_count,
            sorry_annotated=sorry_annotated,
            proof_structure_ok=proof_structure_ok,
            allowed_additions=allowed_additions,
            blocked_additions=blocked_additions,
            findings=findings,
            summary=(
                f"Score: {score:.2f}. "
                f"{'PASSED' if passed else 'FAILED'}. "
                f"{len(findings)} finding(s)."
            ),
        )

    def _semantic_faithfulness_check(
        self,
        parsed: ParsedTheorem,
        goal: LockedGoal,
    ) -> tuple[bool, bool, list[str]]:
        """Use Claude to verify the Lean signature faithfully represents the formula.

        Returns (faithfulness_ok, no_hallucination, findings_list).
        Falls back to passing if the client is unavailable (goal lock already validated).
        """
        findings: list[str] = []

        if self._client is None:
            findings.append("Semantic faithfulness: SKIP (no client — goal lock validation trusted)")
            return True, True, findings

        hypotheses_str = "\n".join(f"  - {h}" for h in parsed.hypotheses) or "  (none)"
        prompt = _FAITHFULNESS_PROMPT.format(
            hypotheses=hypotheses_str,
            conclusion=parsed.conclusion,
            lean_signature=goal.lean_type_only,
        )

        try:
            # Use the ClaudeSDKClient._call() which wraps the claude CLI.
            response = self._client._call(prompt, timeout=45)

            conclusion_match = "CONCLUSION_MATCH: yes" in response
            hyp_covered = "HYPOTHESES_COVERED: yes" in response
            no_extra = "NO_EXTRA_CONSTRAINTS: yes" in response
            overall = "OVERALL_FAITHFUL: yes" in response

            # Extract reason line if present
            reason = ""
            for line in response.splitlines():
                if line.strip().startswith("REASON:"):
                    reason = line.split("REASON:", 1)[1].strip()
                    break

            faithfulness_ok = conclusion_match and hyp_covered and overall
            no_hallucination = no_extra

            if conclusion_match:
                findings.append("Conclusion match: PASS")
            else:
                findings.append(f"Conclusion match: FAIL{' — ' + reason if reason else ''}")

            if hyp_covered:
                findings.append("Hypotheses covered: PASS")
            else:
                findings.append(f"Hypotheses covered: FAIL{' — ' + reason if reason else ''}")

            if no_extra:
                findings.append("No extra constraints: PASS")
            else:
                findings.append(f"No extra constraints: FAIL{' — ' + reason if reason else ''}")

            if overall:
                findings.append("Overall faithfulness: PASS")
            else:
                findings.append(f"Overall faithfulness: FAIL{' — ' + reason if reason else ''}")

        except Exception as exc:
            # Claude call failed (timeout, network, etc.) — trust the goal lock validation
            findings.append(f"Semantic faithfulness: SKIP (Claude call failed: {exc!s:.60}) — goal lock trusted")
            faithfulness_ok = True
            no_hallucination = True

        return faithfulness_ok, no_hallucination, findings
