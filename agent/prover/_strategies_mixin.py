"""Fix-loop strategies (mixin for FormalizerAgent).

Contains every method that takes a failed compile result + node and returns a
candidate next-attempt Lean source.  Two flavours:

* LLM-driven (``_targeted_fix``, ``_targeted_fix_strict``,
  ``_targeted_fix_decompose``, ``_targeted_fix_sorry_removal``) — wrap the
  current lean source + structured error into a prompt and ask Claude.
* Mechanical (``_try_mechanical_error_fix``, ``_try_mechanical_tactics``,
  ``_inventory_template_probe``, ``_fuzzy_polib_names``) — pure-Python
  substitutions that try the obvious one-tactic swap before burning an LLM
  call.

``_partial_solver`` is the small composer that wires generation +
inv-probe + compile-loop together for a fresh proof attempt.

Class-level constants (``_ESCALATION_*``, ``_MECHANICAL_TACTICS``,
``_MECH_ERROR_REPLACEMENTS``, ``_INVENTORY_TEMPLATES``) live here too — they
are tuning data for the strategies, not for the rest of FormalizerAgent.

These methods rely on ``self._sdk``, ``self._sdk_fast``, ``self._config``,
``self._compiler``, ``self._polib_search``, ``self._log``,
``self._generate_lean``, ``self._compile_loop``, ``self._local_refs_block``,
``self._get_error_specific_hints``, and ``self._format_dep_signatures_block``
— all defined elsewhere on FormalizerAgent.
"""
from __future__ import annotations

import os
import re
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import TYPE_CHECKING

from agent.prover import lean_codegen
from agent.prover.prompts.lean_generation import FIX_LOOP_POLIB_REF

if TYPE_CHECKING:
    from agent.prover.tools.blueprint import BlueprintNode
    from agent.prover.tools.goal_lock import GoalLock


class StrategiesMixin:
    # ── Escalation tuning ────────────────────────────────────────────────────
    _ESCALATION_HINT_REFRESH = 4
    _ESCALATION_DECOMPOSE = 7
    _ESCALATION_DECIDE = 10
    # After this many total failed rounds, ask LLM whether to decompose.
    # Set above max_rounds_per_node so decompose never fires during the main loop.
    _DECOMPOSE_CHECK_AFTER = 10

    # ── Mechanical tactic closer ─────────────────────────────────────────────
    _MECHANICAL_TACTICS: list[str] = [
        "decide",
        "trivial",
        "aesop",
        "omega",
        "norm_num",
        "simp",
        "tauto",
        "ring",
    ]

    # ─── Mechanical error-fix templates ──────────────────────────────────────
    # Maps an error-pattern keyword found in `raw_message` to an ordered list
    # of replacement tactics. Applied surgically at the error's reported line
    # (LeanError.line) — see _try_mechanical_error_fix.
    #
    # Design rule: cover ONLY tactic-class errors where a one-tactic swap is
    # the obvious fix. Do NOT include strategy-level fixes (those go to LLM).
    _MECH_ERROR_REPLACEMENTS: list[tuple[str, str, list[str]]] = [
        ("`simp` made no progress", "simp",
         ["omega", "decide", "trivial", "linarith", "ring",
          "push_cast at *; linarith", "push_cast at *; omega",
          "first | omega | linarith | decide"]),
        ("simp made no progress", "simp",
         ["omega", "decide", "trivial", "linarith", "ring",
          "push_cast at *; linarith", "push_cast at *; omega"]),
        ("linarith failed", "linarith",
         ["omega", "nlinarith", "push_cast at *; linarith",
          "push_cast at *; omega", "polyrith"]),
        ("`linarith` failed", "linarith",
         ["omega", "nlinarith", "push_cast at *; linarith",
          "push_cast at *; omega"]),
        ("omega could not", "omega",
         ["push_cast at *; omega", "push_cast at *; linarith",
          "nlinarith", "decide"]),
        ("`omega` could not", "omega",
         ["push_cast at *; omega", "push_cast at *; linarith", "nlinarith"]),
        ("ring failed", "ring",
         ["ring_nf", "field_simp; ring", "push_cast; ring", "linear_combination"]),
    ]

    # Inventory-based proof templates tried before LLM generation.
    # Each entry is a tactic block injected after `:= by`.
    _INVENTORY_TEMPLATES: list[str] = [
        "  have h := P6EdgeCountEquation maps hM\n  push_cast\n  linarith",
        "  have h := Juc_EulerFormula maps hM\n  push_cast\n  linarith",
        "  have h := P6InequalityPart maps hM hm\n  linarith",
        "  have h := Juc_InequalityPart maps hM hm\n  linarith",
        "  have h1 := P6EdgeCountEquation maps hM\n  have h2 := P6InequalityPart maps hM hm\n  push_cast\n  linarith",
        "  have h1 := Juc_EulerFormula maps hM\n  have h2 := Juc_InequalityPart maps hM hm\n  linarith",
        "  have he := euler_formula maps hM\n  have hh := handshake maps hM\n  have hr := regularity maps hM\n  push_cast\n  linarith",
        "  exact (JucovicTheorem maps hM h1).1",
        "  have h := P6EdgeCountEquation maps hM\n  push_cast at *\n  omega",
        "  have h1 := P6EdgeCountEquation maps hM\n  have he := euler_formula maps hM\n  have hh := handshake maps hM\n  push_cast\n  linarith",
    ]

    # ── Phase router ─────────────────────────────────────────────────────────
    def _escalation_phase(self, round_num: int) -> int:
        if round_num < self._ESCALATION_HINT_REFRESH: return 0
        elif round_num < self._ESCALATION_DECOMPOSE:  return 1
        elif round_num < self._ESCALATION_DECIDE:     return 2
        else:                                          return 3

    # ── LLM-driven fix strategies ────────────────────────────────────────────
    def _targeted_fix(
        self,
        lean_code: str,
        result: "CompileResult",
        node: "BlueprintNode",
        hints: list[str],
        round_num: int,
        banned_ids: set[str] | None = None,
    ) -> str:
        """Send structured errors + full source to Claude and ask for a targeted fix."""
        error_block = lean_codegen.format_errors_for_prompt(result.errors)
        hints_str = "\n".join(f"  - {h}" for h in hints) or "  (none)"
        local_refs = self._local_refs_block(node)
        specific_hints = self._get_error_specific_hints(result.errors)
        banned_block = ""
        if banned_ids:
            banned_list = ", ".join(f"`{x}`" for x in sorted(banned_ids))
            banned_block = (
                f"## ⛔ IDENTIFIERS THAT DO NOT EXIST — NEVER USE THESE\n"
                f"The following names were rejected by Lean as unknown. They do NOT exist\n"
                f"in Lean, Mathlib, or Inventory. Do NOT use any of them:\n"
                f"  {banned_list}\n"
                f"Instead use the geometric axiom lemmas (standalone, not structure fields;\n"
                f"hM : IsMap maps comes from the theorem's hypotheses):\n"
                f"  euler_formula maps hM, handshake maps hM, regularity maps hM,\n"
                f"  kgon_occupation_bound maps hM, occupation_bound maps hM, equality_family n\n\n"
            )
        dep_sigs_block = self._format_dep_signatures_block(node.dependencies)
        prompt = (
            f"Fix this Lean 4 compilation error. Round {round_num + 1}.\n\n"
            f"## Node\n{node.node_id}: {node.description}\n\n"
            f"## Compilation Error\n```\n{error_block}\n```\n\n"
            f"## Current Lean 4 Source\n```lean\n{lean_code}\n```\n\n"
            + dep_sigs_block
            + local_refs
            + banned_block
            + specific_hints
            + FIX_LOOP_POLIB_REF + "\n"
            + f"## Available Mathlib Lemmas\n{hints_str}\n\n"
            f"## Lean 4 Finset API — verified correct names:\n"
            f"- Split Finset.Ico sum at midpoint: `Finset.sum_Ico_consecutive` (needs a ≤ b, b ≤ c)\n"
            f"- Combine disjoint sums: `Finset.sum_union` (needs `Disjoint s t`)\n"
            f"- Prove Ico disjointness: `simp [Finset.disjoint_left, Finset.mem_Ico]; omega`\n"
            f"- Ico membership: `Finset.mem_Ico`, filter membership: `Finset.mem_filter`\n"
            f"- Cast in sums: `push_cast`, `Nat.cast_mul`, `Nat.cast_sum`\n"
            f"- ⚠ DOES NOT EXIST — NEVER USE: `Finset.disjoint_Ico_Ico`, "
            f"`Finset.Ico_disjoint_Ico.mpr`, `Finset.sum_Ico_split`\n\n"
            f"Instructions:\n"
            f"- Read the error message carefully and locate the exact problem\n"
            f"- Make the minimal targeted change to fix it\n"
            f"- Do NOT change the theorem statement or its type signature\n"
            f"- ALWAYS use `import Mathlib` (umbrella). NEVER use specific submodule\n"
            f"  paths like `import Mathlib.Algebra.BigOperators.Basic` — they are\n"
            f"  version-dependent and will break the build\n"
            f"- ⚡ If you cannot fix the error, try using Inventory lemmas:\n"
            f"  P6EdgeCountEquation, P6InequalityPart, Juc_EulerFormula (see Inventory reference above).\n"
            f"- Do NOT write sorry — the system rejects sorry and will ask you to fix it.\n"
            f"- Return ONLY the complete corrected Lean 4 file inside a ```lean fence.\n"
            f"  Do not write any prose or explanation outside the fence."
        )
        raw = self._sdk_fast._call(prompt)
        fixed = lean_codegen.normalize_lean(lean_codegen.strip_markdown(raw))
        fixed = lean_codegen.ensure_preamble(fixed)
        return fixed if fixed.strip() else lean_code

    def _targeted_fix_sorry_removal(
        self,
        lean_code: str,
        node: "BlueprintNode",
        hints: list[str],
        round_num: int,
    ) -> str:
        """Ask Claude to remove all sorry from successfully-compiled code by using Inventory lemmas.

        Called when the code compiles but contains sorry that the prover refuses to accept.
        """
        sorry_blocks = lean_codegen.find_sorry_blocks(lean_code)
        n_sorry = len(sorry_blocks)
        hints_str = "\n".join(f"  - {h}" for h in hints) or "  (none)"
        sorry_list = "\n".join(
            f"  {i+1}. {b['desc'][:300]}" for i, b in enumerate(sorry_blocks)
        )
        local_refs = self._local_refs_block(node)
        dep_sigs_block = self._format_dep_signatures_block(node.dependencies)
        prompt = (
            f"This Lean 4 code compiles successfully but contains {n_sorry} sorry(s). "
            f"The system requires zero sorry in the final proof. "
            f"Your job: REMOVE ALL sorry by replacing them with real proofs.\n\n"
            f"## Node\n{node.node_id}: {node.description}\n\n"
            f"## Sorry blocks to fix (must ALL be replaced)\n{sorry_list}\n\n"
            f"## Current Lean 4 Source (compiles, but has sorry)\n```lean\n{lean_code}\n```\n\n"
            + dep_sigs_block
            + local_refs
            + FIX_LOOP_POLIB_REF + "\n"
            + f"## Key Inventory lemmas to use instead of sorry (hM : IsMap maps required):\n"
            f"- `P6EdgeCountEquation maps hM`   (proved): 3*p₃ = 12*(1-g) - 2*p₄ - p₅ + Σ_{{k≥7}}(k-6)*p_k\n"
            f"  → rearranges to: 3*p₃ + 2*p₄ + p₅ = 12*(1-g) + Σ_{{k≥7}}(k-6)*p_k\n"
            f"  → call: `have h := P6EdgeCountEquation maps hM; linarith`\n"
            f"- `Juc_EulerFormula maps hM`      (proved, g=0): 3*p₃ = 12 - 2*p₄ - p₅ + Σ_{{k≥7}}(k-6)*p_k\n"
            f"- `P6InequalityPart maps hM hm`   (PROVED): 3*p₆ ≥ 12*(1-g) - 2*p₄ - 3*p₅ + Σ_{{k≥7}}((k+1)/2-6)*p_k\n"
            f"  → hm : maps.m ≥ 6 is required; derive from hypotheses or add as hypothesis\n"
            f"- `Juc_InequalityPart maps hM hm` (PROVED, g=0): same bound\n"
            f"- `Barnette_P6Bound maps hM hm hsum` (g=0): 2*p₆ ≥ 4 + p₃ - p₅ - 2*Σ_{{k≥7}} p_k; "
            f"requires hsum : Σ_{{k≥7}} p_k ≥ 3\n"
            f"- `euler_formula maps hM`, `handshake maps hM`, `regularity maps hM` (axioms)\n"
            f"- `occupation_conservation maps hM hm`, `occupation_bound maps hM k hk`, "
            f"`quad_occ_cancellation maps hM hm` (axioms; hm : maps.m ≥ 6)\n\n"
            f"## Strategy\n"
            f"1. For each sorry, identify what fact is needed.\n"
            f"2. Find an Inventory lemma that provides it (see list above).\n"
            f"3. Replace `sorry` with `have h := <Inventory lemma>; linarith` or `exact h`.\n"
            f"4. Calling Inventory lemmas is NOT a new sorry — they are the accepted axiom base.\n"
            f"5. ⛔ NEVER fix a sorry by writing a NEW sorried helper — the axiom base is closed; "
            f"such files are rejected.\n\n"
            f"## Available Mathlib Lemmas\n{hints_str}\n\n"
            f"## Instructions\n"
            f"- Replace EVERY sorry with a real proof or Inventory lemma call\n"
            f"- Do NOT write any new sorry under any circumstances\n"
            f"- Do NOT change the theorem statement or its type signature\n"
            f"- Return ONLY the complete Lean 4 file inside a ```lean fence."
        )
        # Haiku-first escalation (mirrors _generate_lean). Sonnet calls on the
        # large fix prompts consistently exceed 300s on slow networks, burning
        # 18 min wallclock per node across 3 attempts. Haiku handles ~70% of
        # mechanical fixes (tactic swaps, push_cast insertion, hypothesis
        # renaming) in 30-60s; Sonnet gets the harder ones on escalation.
        raw = self._sdk._call(
            prompt,
            fast_model=self._config.model_fast,
            timeout=int(os.environ.get("PROVER_FIX_TIMEOUT", "240")),
        )
        fixed = lean_codegen.normalize_lean(lean_codegen.strip_markdown(raw))
        fixed = lean_codegen.ensure_preamble(fixed)
        return fixed if fixed.strip() else lean_code

    def _targeted_fix_strict(
        self,
        lean_code: str,
        result: "CompileResult",
        node: "BlueprintNode",
        hints: list[str],
        round_num: int,
        banned_ids: set[str] | None = None,
    ) -> str:
        """Phase 1: strict fix — only verified hint names, Sonnet for higher accuracy."""
        error_block = lean_codegen.format_errors_for_prompt(result.errors)
        hints_str = "\n".join(f"  - {h}" for h in hints) or "  (none)"
        local_refs = self._local_refs_block(node)
        specific_hints = self._get_error_specific_hints(result.errors)
        banned_block = ""
        if banned_ids:
            banned_list = ", ".join(f"`{x}`" for x in sorted(banned_ids))
            banned_block = (
                f"## ⛔ IDENTIFIERS THAT DO NOT EXIST — NEVER USE THESE\n"
                f"These names do NOT exist anywhere in Lean/Mathlib/Inventory:\n"
                f"  {banned_list}\n"
                f"Use only names from the verified list below or the structure fields.\n\n"
            )
        dep_sigs_block = self._format_dep_signatures_block(node.dependencies)
        prompt = (
            f"CRITICAL: Only use lemma names from the verified list below. "
            f"When uncertain, use omega/simp/linarith/ring instead of guessing names.\n\n"
            f"Fix this Lean 4 compilation error. Round {round_num + 1}.\n\n"
            f"## Node\n{node.node_id}: {node.description}\n\n"
            f"## Compilation Error\n```\n{error_block}\n```\n\n"
            f"## Current Lean 4 Source\n```lean\n{lean_code}\n```\n\n"
            + dep_sigs_block
            + local_refs
            + banned_block
            + specific_hints
            + FIX_LOOP_POLIB_REF + "\n"
            + f"## Verified Mathlib Lemmas (ONLY use names from this list)\n{hints_str}\n\n"
            f"Instructions:\n"
            f"- ONLY reference lemma names that appear in the Inventory reference or verified list above\n"
            f"- You MAY also use lemma names that appear verbatim in the Reference proofs above\n"
            f"- When you cannot find the right lemma, use omega, simp, linarith, or ring\n"
            f"- Do NOT invent or guess lemma names\n"
            f"- Do NOT change the theorem statement or its type signature\n"
            f"- ⚡ If the proof cannot be fixed with standard tactics, try Inventory lemmas:\n"
            f"  P6EdgeCountEquation, P6InequalityPart, Juc_EulerFormula, etc.\n"
            f"- Do NOT write sorry — the system rejects sorry and will ask you to fix it.\n"
            f"- Return ONLY the complete corrected Lean 4 file inside a ```lean fence."
        )
        # STRICT branch: ONE Sonnet attempt only, no retry escalation, exception
        # swallowed. Runs in parallel with _targeted_fix (Haiku-first); first
        # compile-OK wins. Rationale: Haiku reliably handles mechanical tactic
        # swaps but cycles (omega ↔ linarith) when the real fix requires
        # intermediate `have h := <Inventory>; linarith` reasoning. Sonnet gives
        # those harder fixes a real shot — but we cap it at ONE attempt because
        # the parallel `.result()` join would otherwise drag round wallclock to
        # the worst-case 3-retry Sonnet timeout (1080s = 18 min). On timeout the
        # branch falls back to lean_code so the Haiku branch is the floor.
        try:
            raw = self._sdk._call(
                prompt,
                timeout=int(os.environ.get("PROVER_FIX_TIMEOUT", "240")),
                max_attempts=1,
            )
        except Exception:
            return lean_code  # Sonnet failed; let Haiku branch carry the round
        fixed = lean_codegen.normalize_lean(lean_codegen.strip_markdown(raw))
        fixed = lean_codegen.ensure_preamble(fixed)
        return fixed if fixed.strip() else lean_code

    def _targeted_fix_decompose(
        self,
        lean_code: str,
        result: "CompileResult",
        node: "BlueprintNode",
        hints: list[str],
        round_num: int,
        banned_ids: set[str] | None = None,
    ) -> str:
        """Phase 2: rewrite proof as a chain of `have` sub-steps, each closed by one tactic."""
        error_block = lean_codegen.format_errors_for_prompt(result.errors)
        hints_str = "\n".join(f"  - {h}" for h in hints) or "  (none)"
        local_refs = self._local_refs_block(node)
        specific_hints = self._get_error_specific_hints(result.errors)
        banned_block = ""
        if banned_ids:
            banned_list = ", ".join(f"`{x}`" for x in sorted(banned_ids))
            banned_block = (
                f"## ⛔ IDENTIFIERS THAT DO NOT EXIST — NEVER USE THESE\n"
                f"Lean rejected these names as unknown. They do NOT exist:\n"
                f"  {banned_list}\n"
                f"Do NOT use them in any `have` step. Use only structure fields and the\n"
                f"verified lemmas listed below.\n\n"
            )
        dep_sigs_block = self._format_dep_signatures_block(node.dependencies)
        prompt = (
            f"Rewrite this Lean 4 proof as a chain of `have` sub-steps where each step "
            f"is provable by a single tactic (omega / simp / linarith / ring / norm_num).\n\n"
            f"## Node\n{node.node_id}: {node.description}\n\n"
            f"## Compilation Error\n```\n{error_block}\n```\n\n"
            f"## Current Lean 4 Source\n```lean\n{lean_code}\n```\n\n"
            + dep_sigs_block
            + local_refs
            + banned_block
            + specific_hints
            + FIX_LOOP_POLIB_REF + "\n"
            + f"## Available Mathlib Lemmas\n{hints_str}\n\n"
            f"Instructions:\n"
            f"- Break the proof body into small `have h : ... := by ...` steps\n"
            f"- Each step must be dischargeable by exactly one tactic: omega, simp, linarith, ring, or norm_num\n"
            f"- Use the Inventory geometric axiom lemmas listed above as building blocks\n"
            f"- You MAY reuse helper lemmas shown verbatim in the Reference proofs above\n"
            f"- Do NOT change the theorem statement or type signature\n"
            f"- ALWAYS use `import Mathlib` (umbrella), never specific submodule paths\n"
            f"- Return ONLY the complete Lean 4 file inside a ```lean fence."
        )
        # Haiku-first escalation — see _targeted_fix above for rationale.
        raw = self._sdk._call(
            prompt,
            fast_model=self._config.model_fast,
            timeout=int(os.environ.get("PROVER_FIX_TIMEOUT", "240")),
        )
        fixed = lean_codegen.normalize_lean(lean_codegen.strip_markdown(raw))
        fixed = lean_codegen.ensure_preamble(fixed)
        return fixed if fixed.strip() else lean_code

    def _insert_sorry(
        self,
        lean_code: str,
        result: "CompileResult",
        node: "BlueprintNode",
    ) -> str:
        """Replace the first failing tactic with a structured sorry block as last resort."""
        raw_msg = result.errors[0].raw_message[:120] if result.errors else "build failed"
        err_class = result.errors[0].error_class if result.errors else "A"

        # Replace the entire proof body of the target declaration with sorry.
        # Patching a single line is unreliable when there are multiple errors
        # (e.g. several unknown identifiers). Replacing the whole body guarantees
        # the sorry'd file compiles cleanly.
        # Lazy .*? with DOTALL matches through multi-line signatures (which contain `:`)
        # without stopping at the first colon like [^:=\n]* would.
        _decl_re = re.compile(
            r"^((?:(?:private|noncomputable|protected)\s+)*(?:lemma|theorem|def|abbrev)\s+"
            + re.escape(node.node_id)
            + r"\b.*?)"
            r"(\s*:=\s*by\b)(.*)",
            re.DOTALL | re.MULTILINE,
        )
        sorry_body = (
            f"  -- [SORRY] class: {err_class}\n"
            f"  -- [SORRY] reason: {raw_msg.replace(chr(10), ' ')}\n"
            f"  -- [SORRY] impact: blocks {node.node_id}\n"
            f"  -- [SORRY] suggested_next: fix compilation error then remove sorry\n"
            f"  sorry"
        )
        replaced = _decl_re.sub(
            lambda m: m.group(1) + " := by\n" + sorry_body + "\n",
            lean_code,
            count=1,
        )
        if replaced != lean_code:
            return replaced

        # Fallback: find the FIRST `:= by` after the declaration header (not rfind,
        # which would land inside a `have` clause and produce broken code).
        _decl_start_re = re.compile(
            r"^(?:(?:private|noncomputable|protected)\s+)*(?:lemma|theorem|def|abbrev)\s+"
            + re.escape(node.node_id)
            + r"\b",
            re.MULTILINE,
        )
        _m = _decl_start_re.search(lean_code)
        if _m:
            _after = lean_code[_m.start():]
            _idx = _after.find(":= by")
            if _idx != -1:
                _cut = _m.start() + _idx
                return lean_code[:_cut] + ":= by\n" + sorry_body + "\n"

        idx = lean_code.find(":= by")
        if idx != -1:
            return lean_code[:idx] + ":= by\n" + sorry_body + "\n"

        return lean_code + f"\n{sorry_body}\n"

    # ── Mechanical strategies (no LLM call) ──────────────────────────────────
    def _fuzzy_polib_names(self, bad_name: str, k: int = 3) -> list[str]:
        """Return up to ``k`` polib entry names most similar to ``bad_name`` by
        SequenceMatcher ratio. Used when an ``Unknown identifier`` error names
        a symbol that doesn't exist but a close one does (typical pattern:
        planner named a dep ``XInstance`` but Polib has ``X``).
        """
        try:
            from difflib import get_close_matches
            pool = [e.node_id for e in getattr(self._polib_search, "_entries", [])]
            pool += [e.theorem_name for e in getattr(self._polib_search, "_entries", [])
                     if getattr(e, "theorem_name", None)]
            pool = list(dict.fromkeys(p for p in pool if p))
            return get_close_matches(bad_name, pool, n=k, cutoff=0.6)
        except Exception:
            return []

    def _try_mechanical_error_fix(
        self,
        lean_code: str,
        errors: list,
        node_id: str,
        verbose: bool = True,
    ) -> str | None:
        """Try template-based substitutions for common Lean compile errors.

        Runs BEFORE the parallel LLM fix to save 60-240s on what should be a
        one-tactic substitution (``simp`` → ``omega``, ``linarith`` → ``omega``, …)
        or a fuzzy identifier rename. Returns fixed code if any candidate
        compiles, else None.

        Candidates are tried with bounded parallelism (≤3 concurrent compiles).
        Each compile uses a unique node_id suffix so Lake's cache doesn't
        collide. Stops at first successful (sorry-free) compile.
        """
        if not errors:
            return None

        candidates: list[tuple[str, str]] = []

        # Iterate over ALL errors (not just errors[0]) — Lean often reports
        # the most informative error second/third, with a generic
        # "unsolved goals" wrapping it. Try patterns against each in order.
        for err in errors:
            err_msg = err.raw_message
            err_line = getattr(err, "line", 0) or 0
            if err_line < 1:
                continue

            for keyword, target_tactic, alternatives in self._MECH_ERROR_REPLACEMENTS:
                if keyword in err_msg:
                    for tac in alternatives:
                        fixed = lean_codegen.substitute_tactic_at_line(
                            lean_code, err_line, target_tactic, tac
                        )
                        if fixed:
                            candidates.append((f"{target_tactic}→{tac}", fixed))
                    break

            if "Unknown identifier" in err_msg:
                m = re.search(r"Unknown identifier `(\w+)`", err_msg)
                if m:
                    bad_name = m.group(1)
                    for new_name in self._fuzzy_polib_names(bad_name):
                        fixed = re.sub(
                            rf"\b{re.escape(bad_name)}\b", new_name, lean_code
                        )
                        if fixed and fixed != lean_code:
                            candidates.append((f"name:{bad_name}→{new_name}", fixed))

        _seen: set[tuple[str, str]] = set()
        _dedup: list[tuple[str, str]] = []
        for lbl, c in candidates:
            key = (lbl, c[:200])
            if key not in _seen:
                _seen.add(key)
                _dedup.append((lbl, c))
        candidates = _dedup

        if not candidates:
            return None

        max_workers = min(3, len(candidates))
        with ThreadPoolExecutor(max_workers=max_workers) as ex:
            futs = {
                ex.submit(self._compiler.compile, code,
                          f"{node_id}_mech_{i}"): (label, code)
                for i, (label, code) in enumerate(candidates)
            }
            for fut in as_completed(futs):
                label, code = futs[fut]
                try:
                    res = fut.result()
                except Exception:
                    continue
                if res.success and not lean_codegen.has_sorry(code):
                    self._log(verbose,
                        f"  [mech-fix] {node_id}: applied `{label}`, compiled")
                    for f in futs:
                        if not f.done():
                            f.cancel()
                    return code
        labels = ", ".join(lbl for lbl, _ in candidates[:5])
        self._log(verbose,
            f"  [mech-fix] {node_id}: tried {len(candidates)} candidate(s) "
            f"({labels}{'…' if len(candidates) > 5 else ''}), none compiled — "
            f"falling through to LLM")
        return None

    def _try_mechanical_tactics(
        self,
        lean_code: str,
        node_id: str,
        verbose: bool = True,
    ) -> str | None:
        """Replace 'exact sorry' with each mechanical tactic in turn.

        Returns the first version of lean_code that compiles successfully,
        or None if no mechanical tactic closes all sorrys.
        This runs BEFORE any Claude API call in the sorry-elimination loop,
        saving API budget for genuinely hard goals.
        """
        sorry_re = re.compile(r"\bexact\s+sorry\b|\bsorry\b")

        def has_sorry(code: str) -> bool:
            return any(
                sorry_re.search(line)
                for line in code.splitlines()
                if not line.strip().startswith("--")
            )

        if not has_sorry(lean_code):
            return lean_code

        for tactic in self._MECHANICAL_TACTICS:
            candidate = re.sub(
                r"(?m)^(\s*)--\s*\[SORRY\].*\n(?:.*--\s*\[SORRY\].*\n)*\s*exact\s+sorry",
                lambda m: m.group(1) + tactic,
                lean_code,
            )
            candidate = re.sub(r"\bexact\s+sorry\b", tactic, candidate)
            candidate = re.sub(r"(?<!\w)sorry(?!\w)", tactic, candidate)

            try:
                result = self._compiler.compile(
                    lean_codegen.normalize_lean(candidate),
                    node_id + f"_mech_{tactic}",
                )
                if result.success:
                    self._log(
                        verbose,
                        f"  [mechanical] {node_id}: sorry closed by `{tactic}`",
                    )
                    return candidate
            except Exception:
                continue

        return None

    def _inventory_template_probe(
        self, lean_code: str, node_id: str, verbose: bool
    ) -> tuple[str, bool]:
        """Try to prove this node using Inventory lemma templates compiled in parallel.

        Takes the LLM-generated code, finds where the proof body starts (':= by'),
        replaces it with each template, and compiles all candidates concurrently.
        Returns ``(proved_code, True)`` on first success, ``(lean_code, False)``
        if all fail.
        """
        by_matches = list(re.finditer(r':=\s*by\b', lean_code))
        if not by_matches:
            return lean_code, False
        last_by = by_matches[-1]
        before_proof = lean_code[:last_by.end()]

        candidates = [
            (before_proof + "\n" + tmpl + "\n", tmpl)
            for tmpl in self._INVENTORY_TEMPLATES
        ]

        with ThreadPoolExecutor(max_workers=min(len(candidates), 4)) as pool:
            futures = {
                pool.submit(self._compiler.compile, code, node_id + "_inv"): (code, tmpl)
                for code, tmpl in candidates
            }
            for fut in as_completed(futures):
                code, tmpl = futures[fut]
                try:
                    result = fut.result()
                except Exception:
                    continue
                if result.success and not lean_codegen.has_sorry(code):
                    self._log(verbose,
                        f"  [inv-probe] {node_id}: proved by Inventory template "
                        f"({tmpl.strip()[:60]}...)")
                    return code, True

        return lean_code, False

    # ── Composer: generate + probe + compile-loop ────────────────────────────
    def _partial_solver(
        self,
        node: "BlueprintNode",
        goal_lock: "GoalLock",
        hints: list[str],
        proven_node_ids: list[str],
        proven_dep_imports: dict[str, str],
        category: str,
        node_id: str,
        verbose: bool,
        existing_code: str | None = None,
        cross_run_errors: list[dict] | None = None,
    ) -> tuple[str, bool, list]:
        """Generate a fresh proof, compile through the fix loop, and return."""
        lean_code = self._generate_lean(
            node, goal_lock.goal, hints, proven_node_ids,
            proven_dep_imports=proven_dep_imports,
            existing_code=existing_code,
            cross_run_errors=cross_run_errors,
        )

        # Fast Inventory-first probe: try simple Inventory lemma + linarith templates
        # before entering the full fix loop.  No LLM call needed — pure compilation.
        probe_code, probe_ok = self._inventory_template_probe(lean_code, node_id, verbose)
        if probe_ok:
            return probe_code, True, []

        lean_code, compile_ok, last_errors = self._compile_loop(
            lean_code, node, hints, node_id, verbose,
            goal_signature=goal_lock.goal.lean_signature,
        )

        return lean_code, compile_ok, last_errors
