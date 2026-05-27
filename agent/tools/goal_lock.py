from __future__ import annotations

import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone

from agent.exceptions import GoalExtractionError, GoalLockError
from agent.tools.latex_parser import ParsedTheorem


@dataclass
class LockedGoal:
    lean_signature: str
    lean_type_only: str
    locked_at: str
    validator_confirmed: bool
    validator_notes: str

    def to_dict(self) -> dict:
        return {
            "lean_signature": self.lean_signature,
            "lean_type_only": self.lean_type_only,
            "locked_at": self.locked_at,
            "validator_confirmed": self.validator_confirmed,
            "validator_notes": self.validator_notes,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "LockedGoal":
        return cls(
            lean_signature=d["lean_signature"],
            lean_type_only=d["lean_type_only"],
            locked_at=d["locked_at"],
            validator_confirmed=d["validator_confirmed"],
            validator_notes=d["validator_notes"],
        )

    def inject(self, proof_body: str) -> str:
        """Return full Lean 4 source: locked signature + proof body."""
        sig = self.lean_signature
        if sig.endswith(":= by"):
            return sig + "\n" + proof_body
        return sig + "\n  " + proof_body


@dataclass
class GoalValidationResult:
    passed: bool
    issues: list[str]
    suggested_signature: str

    def to_dict(self) -> dict:
        return {
            "passed": self.passed,
            "issues": self.issues,
            "suggested_signature": self.suggested_signature,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "GoalValidationResult":
        return cls(
            passed=d["passed"],
            issues=d["issues"],
            suggested_signature=d["suggested_signature"],
        )


_SIG_PATTERN = re.compile(
    r"^(theorem|lemma)\s+\S+.*:=\s*by\s*$",
    re.MULTILINE | re.DOTALL,
)


def _extract_signature_line(text: str) -> str:
    """Extract the first valid theorem/lemma signature from the response."""
    # Try to find a line or block matching `theorem ... := by`
    # Allow multiline signatures joined with whitespace
    lines = text.strip().splitlines()
    collected: list[str] = []
    in_sig = False
    for line in lines:
        stripped = line.strip()
        if not in_sig and re.match(r"^(theorem|lemma)\b", stripped):
            in_sig = True
        if in_sig:
            collected.append(stripped)
            joined = " ".join(collected)
            # Check for termination: ends with `:= by`
            if re.search(r":=\s*by\s*$", joined):
                return joined
    if collected:
        joined = " ".join(collected)
        if re.match(r"^(theorem|lemma)\b", joined):
            if ":=" not in joined:
                joined += " := by"
            elif not re.search(r":=\s*by\s*$", joined):
                joined = re.sub(r":=.*$", ":= by", joined)
            return joined
    raise GoalExtractionError(
        f"No valid theorem/lemma signature found in response:\n{text[:500]}"
    )


def _type_only(signature: str) -> str:
    """Strip `:= by` from end of signature."""
    return re.sub(r"\s*:=\s*by\s*$", "", signature).strip()


class GoalExtractor:
    def __init__(self, client, model: str):
        self._client = client
        self._model = model

    def extract(self, parsed: ParsedTheorem, hint: str = "") -> str:
        from agent.prompts.goal_extraction import GOAL_EXTRACTION_PROMPT

        user_content = GOAL_EXTRACTION_PROMPT.format(
            theorem_type=parsed.theorem_type,
            name=parsed.name,
            hypotheses="\n".join(f"  - {h}" for h in parsed.hypotheses),
            conclusion=parsed.conclusion,
            hint=f"\nHint from validator: {hint}" if hint else "",
        )
        response = self._client.messages.create(
            model=self._model,
            max_tokens=512,
            messages=[{"role": "user", "content": user_content}],
        )
        text = response.content[0].text.strip()
        return _extract_signature_line(text)


class GoalValidator:
    def __init__(self, client, model: str):
        self._client = client
        self._model = model

    def validate(self, parsed: ParsedTheorem, signature: str) -> GoalValidationResult:

        from agent.prompts.goal_extraction import GOAL_VALIDATION_PROMPT

        user_content = GOAL_VALIDATION_PROMPT.format(
            theorem_type=parsed.theorem_type,
            name=parsed.name,
            hypotheses="\n".join(f"  - {h}" for h in parsed.hypotheses),
            conclusion=parsed.conclusion,
            signature=signature,
        )
        response = self._client.messages.create(
            model=self._model,
            max_tokens=512,
            messages=[{"role": "user", "content": user_content}],
        )
        text = response.content[0].text.strip()
        # Extract JSON object from response
        json_match = re.search(r"\{.*\}", text, re.DOTALL)
        if not json_match:
            return GoalValidationResult(
                passed=False,
                issues=["Validator returned non-JSON response"],
                suggested_signature=signature,
            )
        try:
            data = json.loads(json_match.group())
            return GoalValidationResult(
                passed=bool(data.get("passed", False)),
                issues=data.get("issues", []),
                suggested_signature=data.get("suggested_signature", signature),
            )
        except json.JSONDecodeError as exc:
            return GoalValidationResult(
                passed=False,
                issues=[f"JSON parse error: {exc}"],
                suggested_signature=signature,
            )


class GoalLock:
    """Single source of truth for the theorem statement. Immutable after creation."""

    def __init__(self, goal: LockedGoal):
        self._goal = goal

    @property
    def goal(self) -> LockedGoal:
        return self._goal

    def inject(self, proof_body: str) -> str:
        return self._goal.inject(proof_body)

    @classmethod
    def create(
        cls,
        parsed: ParsedTheorem,
        extractor: GoalExtractor,
        validator: GoalValidator,
        max_attempts: int = 3,
    ) -> "GoalLock":
        hint = ""
        last_signature = ""
        last_extract_err: str = ""
        for attempt in range(max_attempts):
            try:
                signature = extractor.extract(parsed, hint=hint)
            except GoalExtractionError as exc:
                # LLM produced prose instead of a signature — retry with explicit nudge
                last_extract_err = str(exc)
                hint = (
                    "You MUST output ONLY a Lean 4 theorem signature starting with "
                    "`theorem` or `lemma` and ending with `:= by`. "
                    "Do NOT write any explanation or prose."
                )
                continue
            last_signature = signature
            validation = validator.validate(parsed, signature)
            if validation.passed:
                locked = LockedGoal(
                    lean_signature=signature,
                    lean_type_only=_type_only(signature),
                    locked_at=datetime.now(timezone.utc).isoformat(),
                    validator_confirmed=True,
                    validator_notes="; ".join(validation.issues) if validation.issues else "OK",
                )
                return cls(locked)
            hint = validation.suggested_signature or "; ".join(validation.issues)

        # All validation attempts failed but we have a syntactically valid signature.
        # Accept it with validator_confirmed=False rather than aborting the pipeline.
        if last_signature and re.match(r"^(theorem|lemma)\b", last_signature):
            locked = LockedGoal(
                lean_signature=last_signature,
                lean_type_only=_type_only(last_signature),
                locked_at=datetime.now(timezone.utc).isoformat(),
                validator_confirmed=False,
                validator_notes=f"Validation failed after {max_attempts} attempts; accepted as best-effort",
            )
            return cls(locked)

        raise GoalLockError(
            f"Goal extraction failed after {max_attempts} attempts. "
            f"Last signature: {last_signature!r}. Last extraction error: {last_extract_err}"
        )
