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


# Regex to find hypothesis declarations in a Lean 4 signature
# Matches: (name : Type) or {name : Type} or [name : Type]
_HYP_RE = re.compile(r"[\(\{\[]\s*\w+\s*:\s*[^)\}\]]+[\)\}\]]")

# Implicit marker: comment `-- implicit`
_IMPLICIT_COMMENT_RE = re.compile(r"--\s*implicit")

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


def _count_lean_hyps(signature: str) -> int:
    """Count explicit hypothesis declarations in a Lean 4 signature."""
    return len(_HYP_RE.findall(signature))


def _count_lean_tactics(proof_body: str) -> int:
    return len(_TACTIC_RE.findall(proof_body))


def _extract_proof_body(lean_code: str) -> str:
    """Extract everything after `:= by`."""
    idx = lean_code.find(":= by")
    if idx == -1:
        return lean_code
    return lean_code[idx + len(":= by"):]


def _classify_hypothesis(hyp_text: str, parsed_hyps: list[str]) -> str:
    """Classify a Lean hypothesis as explicit | implicit | unknown.

    explicit  — tokens overlap with the LaTeX hypotheses (grounded in source)
    implicit  — carries the '-- implicit' annotation (intentional typeclass addition)
    unknown   — no overlap with LaTeX source and no annotation (potential hallucination)
    """
    # Annotated implicit additions are always allowed
    if _IMPLICIT_COMMENT_RE.search(hyp_text):
        return "implicit"

    stripped = hyp_text.strip()

    # Unannotated typeclass brackets are always suspicious
    if stripped.startswith("[") and stripped.endswith("]"):
        return "unknown"

    # Extract meaningful identifiers from the Lean hypothesis text
    lean_tokens = set(re.findall(r"\b[A-Za-z_][A-Za-z0-9_']*\b", stripped))

    # Strip universal Lean keywords that appear in every hypothesis
    lean_keywords = {
        "theorem", "lemma", "def", "have", "let", "fun", "by",
        "exact", "apply", "intro", "simp", "rw", "ring", "linarith",
        "omega", "norm_num", "Nat", "Int", "Real", "Bool",
        "True", "False", "Prop", "Type", "Sort",
    }
    lean_tokens -= lean_keywords

    if not lean_tokens:
        # Cannot make a determination — give benefit of the doubt
        return "explicit"

    # Collect all identifier tokens from all LaTeX hypothesis strings
    latex_tokens: set[str] = set()
    for h in parsed_hyps:
        latex_tokens.update(re.findall(r"\b[A-Za-z_][A-Za-z0-9_']*\b", h))

    # If the Lean hypothesis shares meaningful tokens with any LaTeX hypothesis,
    # it is grounded in the source material
    if lean_tokens & latex_tokens:
        return "explicit"

    # No overlap at all — flag as a potential hallucination
    return "unknown"


class QualityChecker:
    def __init__(self, client = None, model: str = "claude-sonnet-4-5"):
        self._client = client
        self._model = model

    def check(
        self,
        parsed: ParsedTheorem,
        goal: LockedGoal,
        lean_code: str,
    ) -> QualityReport:
        findings: list[str] = []
        allowed_additions: list[str] = []
        blocked_additions: list[str] = []

        # --- Check 1: Faithfulness (weight 0.40) ---
        lean_hyp_count = _count_lean_hyps(goal.lean_signature)
        latex_hyp_count = len(parsed.hypotheses)
        hyp_count_ok = lean_hyp_count >= latex_hyp_count  # lean may have implicit extras
        conclusion_ok = self._check_conclusion(parsed, goal, lean_code)
        faithfulness_ok = hyp_count_ok and conclusion_ok

        if not hyp_count_ok:
            findings.append(
                f"Hypothesis count mismatch: Lean has {lean_hyp_count}, "
                f"LaTeX has {latex_hyp_count}"
            )
        if not conclusion_ok:
            findings.append("Conclusion in Lean code does not match LaTeX conclusion")
        if faithfulness_ok:
            findings.append("Faithfulness: PASS")

        # --- Check 2: No Hallucination (weight 0.35) ---
        raw_hyps = _HYP_RE.findall(goal.lean_signature)
        for hyp in raw_hyps:
            cls = _classify_hypothesis(hyp, parsed.hypotheses)
            if cls == "implicit":
                allowed_additions.append(hyp.strip())
            elif cls == "unknown":
                blocked_additions.append(hyp.strip())

        no_hallucination = len(blocked_additions) == 0
        if not no_hallucination:
            findings.append(f"Blocked (hallucinated) hypotheses: {blocked_additions}")
        else:
            findings.append("No hallucination: PASS")

        # --- Check 3: Sorry Audit (weight 0.15) ---
        sorry_count = _count_sorry(lean_code)
        sorry_annotated = _all_sorrys_annotated(lean_code)
        if sorry_count > 0 and not sorry_annotated:
            findings.append(
                f"Sorry audit: FAIL — {sorry_count} sorry(s) found, "
                f"not all have complete [SORRY] annotations"
            )
        elif sorry_count > 0:
            findings.append(f"Sorry audit: {sorry_count} sorry(s), all annotated")
        else:
            findings.append("Sorry audit: PASS — no sorrys")

        # --- Check 4: Proof Structure (weight 0.10) ---
        latex_steps = len(parsed.proof_steps)
        proof_body = _extract_proof_body(lean_code)
        lean_steps = _count_lean_tactics(proof_body)
        proof_structure_ok = lean_steps <= max(3 * latex_steps, 3)
        if not proof_structure_ok:
            findings.append(
                f"Proof structure: WARN — {lean_steps} Lean tactic steps vs "
                f"{latex_steps} LaTeX steps (>3x ratio)"
            )
        else:
            findings.append(f"Proof structure: PASS ({lean_steps} tactics, {latex_steps} LaTeX steps)")

        # --- Score computation ---
        score = (
            0.40 * (1.0 if faithfulness_ok else 0.0)
            + 0.35 * (1.0 if no_hallucination else 0.0)
            + 0.15 * (1.0 if sorry_annotated else 0.0)
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
                f"{len(findings)} findings."
            ),
        )

    def _check_conclusion(
        self,
        parsed: ParsedTheorem,
        goal: LockedGoal,
        lean_code: str,
    ) -> bool:
        """Ask Claude whether the Lean type represents the LaTeX conclusion."""
        if self._client is None:
            # Without an API client, do a simple heuristic check:
            # The conclusion should not be trivially empty
            return ": True" not in goal.lean_type_only or "True" in parsed.conclusion

        prompt = (
            f"Does this Lean 4 type represent the following LaTeX conclusion? "
            f"Answer only 'yes' or 'no'.\n"
            f"LaTeX conclusion: {parsed.conclusion}\n"
            f"Lean type: {goal.lean_type_only}"
        )
        try:
            response = self._client.messages.create(
                model=self._model,
                max_tokens=8,
                messages=[{"role": "user", "content": prompt}],
            )
            answer = response.content[0].text.strip().lower()
            return answer.startswith("yes")
        except Exception:
            # Transient LLM failure — fall back to heuristic rather than crashing the node
            return ": True" not in goal.lean_type_only or "True" in parsed.conclusion
