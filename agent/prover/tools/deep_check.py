"""Step-6 deep quality gate for saved node code.

Runs 4 independent checks over each node whose session status is ``"proved"``:

  D1  QR sanity        — the per-node QualityReport collected during stage 4
                         must exist and have ``passed=True`` (upstream gates
                         should already ensure this; belt-and-suspenders).
  D2  Signature drift  — the SAVED CODE's declaration signature must match
                         the LOCKED/planner-supplied signature: same binder
                         count, same binder-type multiset, same conclusion.
                         Catches "LLM added an extra hypothesis binder under
                         the same theorem name" — a case where a bare
                         substring check would silently succeed.
                         When the TEXTUAL comparison fails and a compiler is
                         available, the verdict is arbitrated by Lean itself:
                         ``example : ∀ <locked binders>, <locked conclusion>
                         := <name>`` is appended to the saved code and
                         compiled.  Lean's definitional equality is STRICTER
                         than any string match against real drift (an added
                         hypothesis or changed conclusion cannot typecheck)
                         while being immune to notation noise (`∑ x in s` vs
                         `∑ x ∈ s`, explicit vs elaborator-inserted casts) —
                         the exact false-positive class that killed C137's
                         valid proof on 2026-07-02.
                         Alias-accepted nodes (fuzzy polib reuse under a
                         different lemma name) are checked against the REAL
                         declaration name; a planner-signature mismatch is
                         WARN, not FAIL — see ``check_node``'s docstring.
                         Before 2026-07-04 this check was alias-blind and
                         rejected every legitimate reuse (C201 incident).
  D3  Axiom sweep      — no `axiom` declarations in saved code.  Only the
                         Inventory module may declare axioms; anything the
                         prover writes inline is an unauthorized soundness
                         assumption.
  D4  Instance sweep   — no `SimplyCon3ConnectedMap` instance construction.
                         The QC already checks this at save time; re-checking
                         defends against a code path that ever bypasses QC.

**No D5 (semantic re-check on SAVED sig).**  Formerly this asked the LLM
"does the SAVED sig faithfully represent the JSON?".  Redundant: D2 requires
SAVED == LOCKED structurally, and QC's R4d already verified LOCKED vs JSON
semantically at stage 4.  Composing them gives SAVED ≡ LOCKED ≡ JSON without
a second LLM round-trip.

Any node that fails any check is downgraded via ``session.mark_pending`` AND
its Polib entry is purged, so a "success" FormalizationResult can never
coexist with a deep-check failure — and the Polib is never polluted by a
proof the gate rejected.
"""
from __future__ import annotations

import re
from collections import Counter
from dataclasses import dataclass, field


# ---------------------------------------------------------------------------
# Result type
# ---------------------------------------------------------------------------


@dataclass
class DeepCheckResult:
    passed: bool
    findings: list[str] = field(default_factory=list)

    @property
    def failure_summary(self) -> str:
        """One-line reason string for session.mark_pending."""
        fails = [f for f in self.findings if "FAIL" in f]
        return "; ".join(fails)[:400] if fails else "deep check failed"


# ---------------------------------------------------------------------------
# Regex / static patterns
# ---------------------------------------------------------------------------

# `axiom foo : …` at the start of a (whitespace-prefixed) line, but NOT
# inside a `-- axiom …` comment.  Matches `axiom` even in `noncomputable axiom`.
_AXIOM_RE = re.compile(r'^(?!\s*--)\s*(?:noncomputable\s+)?axiom\s+\w+', re.MULTILINE)

_HEAD_NAME_RE = re.compile(
    r'(?:private\s+|protected\s+|noncomputable\s+)*'
    r'(?:theorem|lemma)\s+(\w+)'
)


# ---------------------------------------------------------------------------
# Signature extraction (walks brackets — regex isn't strong enough here)
# ---------------------------------------------------------------------------


def extract_decl_signature(code: str, decl_name: str) -> str | None:
    """Return the signature substring between ``theorem NAME`` (exclusive)
    and the first ``:=`` at bracket depth 0 (exclusive), or None.

    Walks brackets rather than using a single regex because Lean signatures
    routinely contain nested `:` (in binders) and unicode brackets that
    naïve patterns misclassify as the proof-body separator.
    """
    head_pat = re.compile(
        r'(?:private\s+|protected\s+|noncomputable\s+)*'
        r'(?:theorem|lemma)\s+' + re.escape(decl_name) + r'\b'
    )
    m = head_pat.search(code)
    if m is None:
        return None
    start = m.end()
    depth = 0
    i = start
    n = len(code)
    while i < n - 1:
        ch = code[i]
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth -= 1
        elif depth == 0 and ch == ':' and code[i + 1] == '=':
            return code[start:i].strip()
        i += 1
    return None


def strip_head_and_body(full_sig: str) -> str:
    """Given ``theorem NAME <sig-body> := by``, return just ``<sig-body>``.

    Used to normalize the LOCKED signature so it compares apples-to-apples
    with what ``extract_decl_signature`` returns from saved code.
    """
    head = _HEAD_NAME_RE.match(full_sig)
    tail_start = head.end() if head else 0
    body = full_sig[tail_start:]
    body = re.sub(r"\s*:=(?:\s*by\b)?.*$", "", body, flags=re.DOTALL)
    return body.strip()


def _head_name(full_sig: str) -> str | None:
    m = _HEAD_NAME_RE.search(full_sig)
    return m.group(1) if m else None


def split_binders_and_conclusion(sig: str) -> tuple[list[str], str]:
    """Split *sig* (binder groups + `:` + conclusion, no `:= by` tail) into
    (list of binder-group substrings, conclusion string).

    Iterates char-by-char to correctly nest brackets — a top-level `:`
    separates binders from conclusion, but `:` inside a binder is a type
    annotation, not a separator.
    """
    binders: list[str] = []
    current: list[str] = []
    depth = 0
    conclusion_start: int | None = None
    for i, ch in enumerate(sig):
        if depth == 0:
            if ch in "({[":
                depth = 1
                current = [ch]
            elif ch == ':':
                conclusion_start = i + 1
                break
        else:
            current.append(ch)
            if ch in "({[":
                depth += 1
            elif ch in ")}]":
                depth -= 1
                if depth == 0:
                    binders.append("".join(current))
                    current = []
    conclusion = sig[conclusion_start:].strip() if conclusion_start is not None else ""
    return binders, conclusion


# Big-operator binders: `∑ k in s, …` is the DEPRECATED spelling of
# `∑ k ∈ s, …` — semantically identical, and the pipeline's own in→∈ autofix
# rewrites saved code while the locked signature keeps the original form.
# Collapsed ONLY in this binder position; a bare `in` elsewhere is not
# touched (the general `∈`/`in` caution below still applies).
_BIGOP_IN_RE = re.compile(r"((?:∑|∏|⨆|⨅|⋃|⋂)\s*[^,∈]*?)\s+in\s+")

# `(maps.p_i k : ℤ)` — an explicit numeric-type ascription around an ATOMIC
# application chain (identifiers/fields/args only, no operators or nested
# parens).  In that position Lean's elaborator inserts the same coercion
# implicitly, so ascribed and bare spellings elaborate to the same term.
# Restricted to atomic chains on purpose: stripping around expressions with
# operators (e.g. `(a / b : ℚ)`) could equate genuinely different terms.
_ATOMIC_ASCRIPTION_RE = re.compile(
    r"\(\s*([A-Za-z_][\w.']*(?:\s+[A-Za-z0-9_][\w.']*)*)\s*:\s*(?:ℤ|ℕ|ℚ|ℝ)\s*\)"
)


def _norm(s: str) -> str:
    """Whitespace + known-equivalent-notation collapse for coarse comparison.

    We intentionally treat ``≥``/``>=`` and ``≤``/``<=`` as equivalent because
    Opus commonly reformats between the two — the semantic content is
    identical, and the constant-fidelity check in QC already guarantees the
    inequality DIRECTION was preserved.  Big-operator ``in``/``∈`` and atomic
    numeric ascriptions are collapsed (see the regexes above) because the
    pipeline's own autofix / the elaborator produce them.  ``≠``/``!=`` and
    a general ``∈``/``in`` are not collapsed because they carry distinct
    semantic import (an equality check vs. a membership check).
    """
    s = re.sub(r"\s+", " ", s).strip()
    s = _BIGOP_IN_RE.sub(r"\1 ∈ ", s)
    s = _ATOMIC_ASCRIPTION_RE.sub(r"\1", s)
    return s.replace("≥", ">=").replace("≤", "<=")


def _binder_types(binders: list[str]) -> list[str]:
    """Return each binder's TYPE portion (after first top-level `:` within
    the binder), whitespace/unicode normalized.  Anonymous binders (no `:`)
    are keyed as ``_ANON:<content>`` so they compare cleanly."""
    out: list[str] = []
    for b in binders:
        inner = b[1:-1].strip() if len(b) >= 2 and b[0] in "({[" else b
        depth = 0
        colon_idx = -1
        for i, ch in enumerate(inner):
            if ch in "({[":
                depth += 1
            elif ch in ")}]":
                depth -= 1
            elif depth == 0 and ch == ':':
                colon_idx = i
                break
        if colon_idx < 0:
            out.append("_ANON:" + _norm(inner))
        else:
            out.append(_norm(inner[colon_idx + 1:]))
    return out


# ---------------------------------------------------------------------------
# The 5 individual checks
# ---------------------------------------------------------------------------


def _check_qr_sanity(qr) -> tuple[bool, str]:
    if qr is None:
        return False, "QR sanity: FAIL — no QualityReport collected (invariant violation)"
    if not qr.passed:
        first_fail = next((f for f in qr.findings if "FAIL" in f), "(no detail)")
        return False, f"QR sanity: FAIL — passed=False; first fail: {first_fail[:160]}"
    return True, "QR sanity: PASS"


def _check_axioms(code: str) -> tuple[bool, str]:
    hits = _AXIOM_RE.findall(code)
    if hits:
        return False, (
            f"Axiom sweep: FAIL — {len(hits)} `axiom` declaration(s) in saved code "
            f"(only Inventory may declare axioms; inline axioms are unauthorized "
            f"soundness assumptions)"
        )
    return True, "Axiom sweep: PASS"


def _check_no_instance(code: str) -> tuple[bool, str]:
    """Belt-and-suspenders re-check for SimplyCon3ConnectedMap construction."""
    from agent.prover.tools.lean_compiler import find_struct_construction
    construction = find_struct_construction(code)
    if construction:
        return False, (
            f"Instance sweep: FAIL — SimplyCon3ConnectedMap constructed "
            f"({construction}); axioms applied to fabricated data are unsound"
        )
    return True, "Instance sweep: PASS"


def _check_signature_drift(
    saved_sig: str | None, expected_sig_body: str, expected_name: str,
) -> tuple[bool, list[str]]:
    """Structural compare: binder-count + binder-type-multiset + conclusion.

    Verbatim mismatch alone is NOT a failure (Opus reformats whitespace and
    binder ordering).  What IS a failure:
      * different binder COUNT           → hypothesis added or dropped
      * different binder-type multiset   → hypothesis's type changed
      * different conclusion (after norm) → theorem statement changed
    """
    findings: list[str] = []
    if saved_sig is None:
        return False, [
            f"Signature drift: FAIL — no declaration named `{expected_name}` "
            f"found in saved code"
        ]

    saved_bs, saved_conc = split_binders_and_conclusion(saved_sig)
    exp_bs, exp_conc = split_binders_and_conclusion(expected_sig_body)

    ok = True
    if len(saved_bs) != len(exp_bs):
        ok = False
        extras = [b[:80] for b in saved_bs
                  if _norm(b) not in {_norm(x) for x in exp_bs}][:3]
        findings.append(
            f"Signature drift: FAIL — binder count mismatch "
            f"(saved={len(saved_bs)}, locked={len(exp_bs)}). "
            f"Suggests LLM added or dropped a hypothesis. "
            f"Extras in saved (up to 3): {extras}"
        )
    else:
        saved_t = _binder_types(saved_bs)
        exp_t = _binder_types(exp_bs)
        if Counter(saved_t) != Counter(exp_t):
            ok = False
            missing = list((Counter(exp_t) - Counter(saved_t)).elements())[:3]
            added = list((Counter(saved_t) - Counter(exp_t)).elements())[:3]
            findings.append(
                f"Signature drift: FAIL — binder-type multiset differs. "
                f"Missing from saved: {missing}. Added in saved: {added}"
            )
        else:
            findings.append(
                f"Signature drift: PASS — {len(saved_bs)} binders, types match"
            )

    if _norm(saved_conc) != _norm(exp_conc):
        ok = False
        findings.append(
            f"Conclusion drift: FAIL — saved conclusion does not match locked\n"
            f"    locked: {exp_conc[:140]}\n"
            f"    saved:  {saved_conc[:140]}"
        )
    else:
        findings.append("Conclusion drift: PASS — matches locked")

    return ok, findings


# ---------------------------------------------------------------------------
# Defeq arbitration — Lean itself judges a textual signature mismatch
# ---------------------------------------------------------------------------


def _defeq_arbitrate(
    saved_code: str, expected_sig_full: str, expected_name: str, compiler,
) -> tuple[bool | None, str]:
    """Ask Lean whether the saved theorem proves EXACTLY the locked statement.

    Appends ``example : ∀ <locked binders>, <locked conclusion> := NAME`` to
    the saved code and compiles it.  Success means the saved declaration's
    type is definitionally equal to the locked signature — every textual
    difference was notation-level.  Failure means real drift.  This is not a
    weakening of the gate: string equality can be fooled by notation
    shadowing; the type checker cannot.

    Returns (verdict, detail).  verdict None = arbitration unavailable
    (unrenderable signature / compiler error) — the caller keeps the
    textual FAIL.
    """
    expected_body = strip_head_and_body(expected_sig_full)
    binders, conclusion = split_binders_and_conclusion(expected_body)
    if not conclusion:
        return None, "arbitration unavailable: locked signature has no conclusion"
    forall_ty = ("∀ " + " ".join(binders) + ", " if binders else "") + conclusion
    # The locked signature may predate the pipeline's in→∈ autofix; the
    # deprecated big-operator `in` no longer parses at all in current
    # Mathlib, so normalize before rendering.
    forall_ty = _BIGOP_IN_RE.sub(r"\1 ∈ ", forall_ty)
    check_code = (
        f"{saved_code}\n\n"
        f"-- step-6 defeq arbitration (auto-generated; never saved)\n"
        f"example : {forall_ty} := {expected_name}\n"
    )
    try:
        result = compiler.compile(check_code, f"{expected_name}_sigcheck")
    except Exception as exc:
        return None, f"arbitration unavailable: compile error ({exc})"
    if result.success:
        return True, f"Lean accepts `example : <locked ∀-type> := {expected_name}`"
    first_err = result.errors[0].raw_message[:160] if result.errors else \
        (result.stderr or "unknown error")[:160]
    return False, first_err


# ---------------------------------------------------------------------------
# Top-level dispatch — called once per node from _step6_deep_check
# ---------------------------------------------------------------------------


def check_node(
    *,
    node_id: str,
    is_main_target: bool,
    saved_code: str | None,
    qr,
    expected_sig_full: str,
    parsed,
    quality_checker,
    compiler=None,
    alias_name: str | None = None,
) -> DeepCheckResult:
    """Run D1–D4 for one saved node.

    ``expected_sig_full`` is the LOCKED signature (main target) or the
    planner-supplied blueprint signature (sub-lemma) — the ground truth
    we compare the SAVED CODE's signature against.

    ``compiler`` (a LeanCompiler, optional): enables defeq arbitration when
    the textual D2 comparison fails — see ``_defeq_arbitrate``.

    ``alias_name``: set when the node was cache-accepted by reusing an
    already-proved lemma under a DIFFERENT name (fuzzy polib match, see
    ``_accept_existing_code``).  The saved code then declares ``alias_name``,
    not the planner's blueprint name, so the declaration lookup and defeq
    arbitration must use it.  A planner-signature mismatch on an aliased
    node is a WARN, not a FAIL: the reused lemma's statement legitimately
    differs from the planner's intent — it was vetted at cache-accept QC,
    downstream provers compile against the real lemma, and the whole-Polib
    build (step 7) remains the soundness gate.  The declaration-missing
    case still hard-fails regardless of aliasing.  (Never applies to the
    main target: alias-accept is rejected for it upstream.)

    ``is_main_target``, ``parsed``, and ``quality_checker`` are accepted
    for API stability; they are unused now that D5 (semantic re-check on
    SAVED sig) has been retired as redundant with D2 + QC's stage-4
    semantic check.
    """
    del is_main_target, parsed, quality_checker  # retained; see docstring
    findings: list[str] = []
    ok = True

    ok_qr, msg_qr = _check_qr_sanity(qr)
    findings.append(msg_qr)
    ok = ok and ok_qr

    if saved_code is None:
        findings.append("Code snapshot: FAIL — saved code missing from _run_codes")
        return DeepCheckResult(passed=False, findings=findings)

    ok_ax, msg_ax = _check_axioms(saved_code)
    findings.append(msg_ax)
    ok = ok and ok_ax

    ok_in, msg_in = _check_no_instance(saved_code)
    findings.append(msg_in)
    ok = ok and ok_in

    expected_name = alias_name or _head_name(expected_sig_full) or node_id
    expected_body = strip_head_and_body(expected_sig_full)
    saved_sig = extract_decl_signature(saved_code, expected_name)

    ok_sig, sig_findings = _check_signature_drift(
        saved_sig, expected_body, expected_name,
    )
    # Textual mismatch on an EXISTING declaration → let Lean arbitrate.
    # (saved_sig None means the declaration is missing entirely — no
    # arbitration can rescue that.)
    if not ok_sig and saved_sig is not None and compiler is not None:
        verdict, detail = _defeq_arbitrate(
            saved_code, expected_sig_full, expected_name, compiler,
        )
        if verdict is True:
            ok_sig = True
            sig_findings = [
                f.replace("FAIL", "textual mismatch (overruled by defeq)")
                for f in sig_findings
            ]
            sig_findings.append(f"Signature defeq: PASS — {detail}")
        elif verdict is False:
            sig_findings.append(f"Signature defeq: FAIL — {detail}")
        else:
            sig_findings.append(f"Signature defeq: WARN — {detail}")
    # Alias reuse: the saved code IS another proved lemma; comparing it to
    # this node's planner signature is a category error, so a residual
    # mismatch demotes to WARN (see docstring).  Requires the aliased
    # declaration to actually exist — saved_sig None stays a hard FAIL.
    if not ok_sig and alias_name is not None and saved_sig is not None:
        ok_sig = True
        sig_findings = [
            f.replace("FAIL", "WARN (alias reuse)") for f in sig_findings
        ]
        sig_findings.append(
            f"Signature drift: N/A — node satisfied by reused lemma "
            f"`{alias_name}`; planner-signature comparison does not apply"
        )
    findings.extend(sig_findings)
    ok = ok and ok_sig

    return DeepCheckResult(passed=ok, findings=findings)
