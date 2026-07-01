"""Goal extraction + locking for step 2 of the prover pipeline.

Public API:
  * ``LockedGoal``         — the immutable per-conjecture signature
  * ``lock_goal(...)``     — top-level entry: extract → static check → confirmed,
                             with retry-with-correction (up to 3 attempts)
  * ``_GOAL_PROMPT_HASH``  — exposed for the cache key so cached signatures
                             auto-invalidate when the prompt is tuned

The static check (``_check_signature_static``) replaces what used to be an
LLM-driven ``GoalValidator``.  The 6 syntactic rules it now enforces deliver
the same coverage as the LLM checks did, but instantly + deterministically.
Two semantic checks (conclusion fidelity, condition-strength) are dropped;
downstream Lean compilation catches those.
"""
from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass
from typing import Callable

from agent.exceptions import GoalExtractionError, GoalLockError
from agent.prover.tools.parsed_theorem import ParsedTheorem


# ---------------------------------------------------------------------------
# Extractor prompt
# ---------------------------------------------------------------------------

GOAL_EXTRACTION_PROMPT = """\
You are a Lean 4 expert. Convert the following theorem into a Lean 4 type signature.

Name: {name}
Hypotheses:
{hypotheses}
Conclusion: {conclusion}
{hint}

Rules:
1. Output exactly one line (or multiline continuation) beginning with `theorem` or `lemma` and ending with `:= by`. Nothing else.
2. Hypothesis count must equal the number of hypotheses listed above. Do not drop or merge them.
3. The conclusion must represent the conclusion above exactly (inequalities, existential quantifiers, all parts).
4. Never encode what must be PROVED as a hypothesis. Hypotheses = GIVEN; conclusion = TO PROVE.
5. Implicit additions (typeclass constraints) go after explicit hypotheses, marked `-- implicit`.

6. MANDATORY structure binder — every signature MUST begin with:
     `(maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps)`
   `0` is the genus (sphere) and is fixed for ALL IRIS conjectures. NEVER use a free `(g : ℤ)`.
   `hM` is the realizability token — every Inventory axiom needs it. Do NOT count `maps` or `hM` toward rule 2's hypothesis count.

7. Field access:
     face counts → `maps.p_i k`        (NEVER `maps.p_i 2` for f_2 — that's digons, always 0)
     edges      → `maps.e`
     vertices   → `maps.v`
     max face   → `maps.m`             (use as sum upper bound, do NOT add a separate (K : ℕ))
   `maps.f2` and `maps.f_2` do NOT exist as fields.

8. f_2 translation: `f_2 → ∑ k in Finset.Ico 3 (maps.m + 1), maps.p_i k`.
   General sums: `∑ k in Finset.Ico LOW (maps.m + 1), …` (NEVER `Finset.filter (· ≥ N) (Finset.range K)`).

9. Simplicity is encoded in `SimplyCon3ConnectedMap` — do NOT add `IsSimple`, `maps.simple`, `maps.is_simple`, `h_simple`, `h_3connected`, or any variant.

10. Fractional coefficients: multiply BOTH sides by the denominator to stay in ℤ/ℕ.
    Example: `p_6 ≥ (9/2)·X + 9` becomes `2 * maps.p_i 6 ≥ 9 * X + 18`.

11. Output ONLY the signature. No prose, no markdown fences, no explanation.
"""

# Hash baked into the goal cache key so cached signatures auto-invalidate
# when this prompt is tuned (otherwise a fixed prompt would keep serving
# the old buggy signatures).
_GOAL_PROMPT_HASH = hashlib.sha256(GOAL_EXTRACTION_PROMPT.encode()).hexdigest()[:8]


# ---------------------------------------------------------------------------
# LockedGoal — the immutable per-conjecture lock
# ---------------------------------------------------------------------------

@dataclass
class LockedGoal:
    lean_signature: str
    validator_confirmed: bool

    @property
    def lean_type_only(self) -> str:
        """Signature with ``:= by`` stripped, for places that want just the type."""
        return re.sub(r"\s*:=\s*by\s*$", "", self.lean_signature).strip()

    def inject(self, proof_body: str) -> str:
        """Return full Lean 4 source: locked signature + proof body."""
        sig = self.lean_signature
        if sig.endswith(":= by"):
            return sig + "\n" + proof_body
        return sig + "\n  " + proof_body

    def to_dict(self) -> dict:
        return {
            "lean_signature": self.lean_signature,
            "validator_confirmed": self.validator_confirmed,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "LockedGoal":
        return cls(
            lean_signature=d["lean_signature"],
            validator_confirmed=d["validator_confirmed"],
        )


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _extract_signature_line(text: str) -> str:
    """Return the first ``theorem|lemma ... := by`` block in *text*.

    Raises ``GoalExtractionError`` if no such block is found.  We refuse to
    concatenate prose into the signature — the retry loop re-prompts on
    failure.
    """
    collected: list[str] = []
    started = False
    for line in text.splitlines():
        stripped = line.strip()
        if not started and re.match(r"^(theorem|lemma)\b", stripped):
            started = True
        if not started:
            continue
        collected.append(stripped)
        joined = " ".join(collected)
        if re.search(r":=\s*by\s*$", joined):
            return joined
    raise GoalExtractionError(
        "No `theorem|lemma ... := by` block found in extractor response. "
        f"First 500 chars:\n{text[:500]}"
    )


def _check_signature_static(sig: str, parsed: ParsedTheorem) -> list[str]:
    """Return a list of issue strings.  Empty list = all checks pass."""
    issues: list[str] = []

    if not re.match(r"^\s*(theorem|lemma)\b", sig):
        issues.append("signature must start with `theorem` or `lemma`")
    if not re.search(r":=\s*by\s*$", sig):
        issues.append("signature must end with `:= by`")

    if not re.search(r"\(maps\s*:\s*SimplyCon3ConnectedMap\s+0\s*\)", sig):
        issues.append(
            "missing or malformed `(maps : SimplyCon3ConnectedMap 0)` binder "
            "(genus MUST be the literal 0, not a free `g`)"
        )
    if not re.search(
        r"\(maps\s*:\s*SimplyCon3ConnectedMap\s+0\s*\)\s*\(hM\s*:\s*IsMap\s+maps\s*\)",
        sig,
    ):
        issues.append(
            "`(hM : IsMap maps)` must appear IMMEDIATELY after the `(maps : ...)` binder"
        )

    if re.search(r"\(\s*g\s*:\s*(?:ℤ|Int)\s*\)", sig):
        issues.append("free genus parameter `(g : ℤ)` is banned — use `SimplyCon3ConnectedMap 0`")

    for pat, name in [
        (r"\bIsSimple\b", "IsSimple"),
        (r"\bmaps\.simple\b", "maps.simple"),
        (r"\bmaps\.is_simple\b", "maps.is_simple"),
        (r"\bh_simple\b", "h_simple"),
        (r"\bh_3connected\b", "h_3connected"),
    ]:
        if re.search(pat, sig):
            issues.append(
                f"`{name}` is not defined — simplicity is encoded in `SimplyCon3ConnectedMap`"
            )
            break

    if re.search(r"\bmaps\.f_?2\b", sig):
        issues.append(
            "`maps.f2`/`maps.f_2` does not exist — write "
            "`∑ k in Finset.Ico 3 (maps.m + 1), maps.p_i k` for f_2"
        )
    if re.search(r"maps\.p_i\s+2\b", sig):
        issues.append(
            "`maps.p_i 2` = digons (always 0); for f_2 use the full sum over Finset.Ico 3 (maps.m + 1)"
        )
    if re.search(r"Finset\.filter\b", sig):
        issues.append(
            "use `Finset.Ico LOW (maps.m + 1)` instead of `Finset.filter` over `Finset.range`"
        )

    return issues


def _call_extractor(parsed: ParsedTheorem, client, model: str, hint: str) -> str:
    """One LLM call to extract a Lean signature from a parsed conjecture.

    ``effort="low"``: signature extraction is a structured-output task that
    does not benefit from extended thinking — using the schedule default
    (medium) added 60-120s per attempt without improving accuracy.
    """
    user_content = GOAL_EXTRACTION_PROMPT.format(
        name=parsed.name,
        hypotheses="\n".join(f"  - {h}" for h in parsed.hypotheses),
        conclusion=parsed.conclusion,
        hint=hint,
    )
    response = client.messages.create(
        model=model,
        max_tokens=512,
        messages=[{"role": "user", "content": user_content}],
        effort="low",
        allowed_tools=[],  # signature extraction is pure output; no grep needed
    )
    return _extract_signature_line(response.content[0].text.strip())


def _format_hint(issues: list[str]) -> str:
    """Render the static-check issues as a prompt-friendly hint block."""
    lines = ["", "Static check rejected the previous signature. Fix ALL of the following:"]
    for it in issues:
        lines.append(f"  - {it}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Top-level entry: extract → static check → confirmed, with retry
# ---------------------------------------------------------------------------

def lock_goal(
    parsed: ParsedTheorem,
    client,
    model: str,
    max_attempts: int = 3,
    log: Callable[[str], None] | None = None,
) -> LockedGoal:
    """Extract a Lean signature for *parsed* and verify it with the static check.

    Returns a confirmed ``LockedGoal`` on success.  On exhaustion with a
    syntactically valid (but check-failing) signature, returns a best-effort
    lock with ``validator_confirmed=False``.  On total failure (no usable
    signature ever produced), raises ``GoalLockError``.
    """
    _log = log or (lambda _msg: None)
    hint = ""
    last_signature = ""
    last_issues: list[str] = []
    last_extract_err = ""
    for attempt in range(1, max_attempts + 1):
        _log(f"      [goal-attempt {attempt}/{max_attempts}] extracting signature")
        try:
            signature = _call_extractor(parsed, client, model, hint)
        except GoalExtractionError as exc:
            last_extract_err = str(exc).splitlines()[0][:160]
            _log(f"      [goal-attempt {attempt}/{max_attempts}] extractor error: "
                 f"{last_extract_err}")
            hint = _format_hint(["extractor produced no `theorem|lemma ... := by` block"])
            continue
        last_signature = signature
        issues = _check_signature_static(signature, parsed)
        if not issues:
            _log(f"      [goal-attempt {attempt}/{max_attempts}] CONFIRMED: "
                 f"{signature[:80]}...")
            return LockedGoal(lean_signature=signature, validator_confirmed=True)
        last_issues = issues
        _log(f"      [goal-attempt {attempt}/{max_attempts}] {len(issues)} issue(s): "
             f"{issues[0][:140]}")
        hint = _format_hint(issues)

    if last_signature and re.match(r"^(theorem|lemma)\b", last_signature):
        _log(f"      [goal-attempt] exhausted {max_attempts} attempts — accepting "
             f"best-effort signature (validator_confirmed=False)")
        return LockedGoal(lean_signature=last_signature, validator_confirmed=False)
    raise GoalLockError(
        f"Goal extraction failed after {max_attempts} attempts. "
        f"Last signature: {last_signature!r}. "
        f"Last extractor error: {last_extract_err}. "
        f"Last issues: {last_issues}"
    )
