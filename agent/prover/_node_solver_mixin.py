"""Per-node solver (mixin for FormalizerAgent).

The proof-generation core lives in ``agent/prover/proof_agent.py`` (one
LLM session, one MCP ``lean_compile`` tool).  What's left here:

* ``_compute_parallel_levels`` — topo-sort → parallel level grouping.
* ``_verify_polib_builds``    — post-save guard for the polib transaction.
* ``_process_node``           — per-node dispatcher: try cached/saved code
  first, then delegate to ``proof_agent.prove_node`` and save the result.
"""
from __future__ import annotations

import re
from pathlib import Path
from typing import TYPE_CHECKING

from agent.exceptions import BlueprintError, GoalTamperedError, PolibSaveError
from agent.prover import lean_codegen
from agent.prover.tools.blueprint import Blueprint, BlueprintNode
from agent.prover.tools.goal_lock import LockedGoal
from agent.prover.tools.search import SavedEntry

if TYPE_CHECKING:
    from agent.prover.tools.parsed_theorem import ParsedTheorem


_TRIVIAL_TYPE_RE = re.compile(
    r'(?:lemma|theorem)\s+\S[^:]*:\s*(?:True|False|Prop)\s*(?::=|where)'
)

_DECL_NAME_RE = re.compile(
    r'(?:private\s+|protected\s+|noncomputable\s+)*'
    r'(?:theorem|lemma|def|abbrev)\s+(\w+)'
)

# Lean-3 → Lean-4 syntax fix for big-operator binders:
# `∑ k in Finset.…` / `∏ k in …` / `⋃ k in …` / `⋂ k in …`  →  use `∈`.
# Lean 4 with modern Mathlib rejects the keyword `in` in these positions
# with `unexpected token 'in'; expected ','`.  Planner LLMs sometimes emit
# the Lean-3 form because it dominates their training corpus.
_BIGOP_IN_RE = re.compile(r"([∑∏⋃⋂])\s*(\w+)\s+in\s+")


def _autofix_lean_sig(sig: str) -> str:
    """Return *sig* with common Lean-4 syntax slips corrected."""
    return _BIGOP_IN_RE.sub(r"\1 \2 ∈ ", sig)


def _expected_decl_name(node: BlueprintNode, node_locked: LockedGoal) -> str:
    """Return the Lean identifier the proof file's target decl must use.

    Extracted from ``node_locked.lean_signature`` — the LLM is told to
    prove that signature verbatim, so the first ``theorem|lemma|def|abbrev``
    name in it is the name our acceptance check must look for.
    Falls back to ``node.node_id`` if the signature can't be parsed.
    """
    m = _DECL_NAME_RE.search(node_locked.lean_signature)
    return m.group(1) if m else node.node_id


class NodeSolverMixin:
    # ------------------------------------------------------------------
    # Parallel level grouping (called by pipeline _step4_node_loop)
    # ------------------------------------------------------------------

    def _compute_parallel_levels(self, blueprint: Blueprint) -> list[list[str]]:
        """Group ``blueprint.topo_order`` into parallel levels.

        All nodes at the same level have all their dependencies at lower
        levels and can therefore be compiled concurrently.
        """
        node_level: dict[str, int] = {}
        for node_id in blueprint.topo_order:
            node = blueprint.get_node(node_id)
            missing = [d for d in node.dependencies if d not in node_level]
            if missing:
                raise BlueprintError(
                    f"_compute_parallel_levels: node {node_id!r} has dependencies "
                    f"{missing} not yet assigned a level (topo-sort failure)."
                )
            node_level[node_id] = (
                max((node_level[d] for d in node.dependencies), default=-1) + 1
            )
        max_level = max(node_level.values(), default=0)
        levels: list[list[str]] = [[] for _ in range(max_level + 1)]
        for node_id in blueprint.topo_order:
            levels[node_level[node_id]].append(node_id)
        return levels

    # ------------------------------------------------------------------
    # Post-save Polib build guard
    # ------------------------------------------------------------------

    def _verify_polib_builds(self, node_id: str, verbose: bool) -> bool:
        """Compile a minimal file ``import Polib`` to check the package still
        builds cleanly.  Must actually import Polib (not just Inventory) —
        otherwise a broken save would slip through and only surface at the
        end-of-run PolibValidator.
        """
        result = self._compiler.compile(
            "import Mathlib\nimport Inventory\nimport Polib\n",
            f"_polib_verify_{node_id}",
        )
        if result.success:
            return True
        err = (
            result.errors[0].raw_message[:80] if result.errors
            else (result.stderr or "build failed")[:80]
        )
        self._log(verbose, f"  [polib-broken] {node_id}: Polib.lean build failed: {err}")
        return False

    def _signature_compiles(self, lean_signature: str, node_id: str, verbose: bool) -> bool:
        """Compile ``{lean_signature} sorry`` to verify the planner-supplied
        sub-lemma signature is syntactically + type-correct.

        Catches:
          * Malformed Lean syntax in the planner output
          * References to non-existent Inventory/Mathlib types or fields
          * Wrong arity / namespace mistakes (e.g. ``p_4 maps`` vs ``maps.p_4``)

        Applies a small Lean-3→Lean-4 auto-fix pass first (mainly ``∑ k in`` →
        ``∑ k ∈``) so a single-character syntax slip by the planner doesn't
        blow up a whole node.  If the sig still doesn't compile after the
        auto-fix, we fail fast rather than burning 1500s of proof_agent.
        """
        sig = _autofix_lean_sig(lean_signature)
        if sig != lean_signature:
            self._log(verbose,
                f"  [sig-autofix] {node_id}: applied `in`→`∈` fix to sum notation")
        # Strip trailing `:= by` / `:=` so we can append our own `:= by sorry`.
        sig_no_body = re.sub(r"\s*:=\s*by\s*$", "", sig)
        sig_no_body = re.sub(r"\s*:=\s*$", "", sig_no_body)
        test_code = (
            "import Mathlib\nimport Inventory\nimport Polib\n\n"
            f"{sig_no_body} := by sorry\n"
        )
        result = self._compiler.compile(test_code, f"_sigcheck_{node_id}")
        if result.success:
            return True
        err = (
            result.errors[0].raw_message[:160] if result.errors
            else (result.stderr or "build failed")[:160]
        )
        self._log(verbose,
            f"  [bad-sig] {node_id}: planner signature does NOT compile — "
            f"failing fast instead of burning 1500s on a broken target. Error: {err}")
        return False

    # ------------------------------------------------------------------
    # Cache-accept helpers — keep the 3 "already proved" paths DRY
    # ------------------------------------------------------------------

    def _record_skip(
        self, node_id: str, code: str, parsed, locked, is_main_target: bool,
        verbose: bool, log_tag: str,
    ) -> bool:
        """Cache-accept gate: run QC on *code* against the CURRENT conjecture.

        Returns True iff the report passes; caller MUST NOT mark_done on False.
        The cached code has drifted from the current conjecture (e.g. the JSON
        was edited between runs) and must be re-proved.  Previously this helper
        ran the check but silently discarded the verdict — a stale Polib entry
        whose signature no longer matched the current JSON would then be
        reported as "proved" and slip through to a "success" FormalizationResult
        with a semantically inconsistent .lean file.
        """
        report = self._quality.check(parsed, locked, code, is_main_target=is_main_target)
        if not report.passed:
            fail = next((f for f in report.findings if "FAIL" in f), "no detail")
            self._log(verbose,
                f"  [{log_tag}-reject] {node_id}: cached code fails current QC — {fail[:160]}")
            return False
        with self._run_codes_lock:
            self._run_codes[node_id] = code
            self._run_quality_reports[node_id] = report
            self._run_skipped_nodes.add(node_id)
        return True

    def _accept_existing_code(
        self,
        node: BlueprintNode,
        node_id: str,
        existing: SavedEntry,
        parsed: "ParsedTheorem",
        locked: "LockedGoal",
        verbose: bool,
        log_tag: str,
    ) -> str | None:
        """Try to skip *node* by reusing ``existing.node_id``'s saved code.

        Returns ``"proved"`` on a successful skip, or None if the existing
        entry can't be used.  Partial entries (containing sorry) are NEVER
        accepted — strict no-new-sorry policy means any cached partial is
        a stale artifact from before the policy and must be re-proved.
        When the entry's name differs from ``node_id``, an alias is
        registered so downstream dep-resolution surfaces the real Lean
        identifier.
        """
        if existing.status != "proved":
            self._log(verbose,
                f"  [{log_tag}-skip] {node_id} → {existing.node_id} "
                f"(status={existing.status}, no-new-sorry policy — will re-prove)")
            return None

        if existing.node_id != node_id:
            # The main target IS the conjecture — never alias it to a sub-lemma
            # (or anything else). C124 fuzzy-matching its own C124_SumSplit
            # sub-lemma silently registered an alias and marked the conjecture
            # "proved" without actually proving it.
            if node.is_main_target:
                self._log(verbose,
                    f"  [alias-reject] {node_id} → {existing.node_id} "
                    f"(main target must be proved under its own name)")
                return None
            n_tok = lean_codegen.face_count_tokens(node_id)
            e_tok = lean_codegen.face_count_tokens(existing.node_id)
            if n_tok and e_tok and not (n_tok & e_tok):
                self._log(verbose,
                    f"  [alias-reject] {node_id} → {existing.node_id} "
                    f"(face-count mismatch: {sorted(n_tok)} vs {sorted(e_tok)})")
                return None
            self._polib_search.register_alias(node_id, existing.node_id)

        code = self._load_polib_code(existing.node_id)
        if not code:
            return None
        if lean_codegen.has_sorry(code):
            self._log(verbose,
                f"  [{log_tag}-skip] {node_id} matched polib but code has sorry "
                f"(no-new-sorry policy — will re-prove)")
            return None
        # QC gate BEFORE mark_done: cached code may have been proved under a
        # prior JSON that no longer matches the current parsed conjecture.
        if not self._record_skip(
            node_id, code, parsed, locked, node.is_main_target, verbose, log_tag,
        ):
            return None
        self._session.mark_done(node_id, "proved")
        return "proved"

    # ------------------------------------------------------------------
    # Main per-node dispatcher
    # ------------------------------------------------------------------

    def _process_node(
        self,
        node_id: str,
        blueprint: Blueprint,
        locked: "LockedGoal",
        parsed: "ParsedTheorem",
        category: str,
        proven_node_ids: list[str],
        verbose: bool,
        proven_dep_imports: dict[str, str] | None = None,
    ) -> str:
        """Process one blueprint node. Returns ``"proved" | "partial" | "pending"``."""
        node = blueprint.get_node(node_id)

        # ── Cache-accept stage ────────────────────────────────────────
        # (a) Session says done — try the exact-name code, then fuzzy fallback.
        if self._session.is_done(node_id):
            code = self._load_polib_code(node_id)
            if code and self._record_skip(
                node_id, code, parsed, locked, node.is_main_target,
                verbose, "session-skip",
            ):
                self._log(verbose, f"  [skip] {node_id} (proved, session)")
                return "proved"
            # Either code was missing, or QC rejected it as inconsistent with
            # the current parsed conjecture.  Either way the session is stale;
            # try fuzzy polib recovery, else fall through to a fresh prove.
            fallback = self._polib_search.search(node, parsed)
            if fallback is not None:
                status = self._accept_existing_code(
                    node, node_id, fallback, parsed, locked, verbose, "skip-recover",
                )
                if status is not None:
                    return status
            stale_reason = ("cached code fails current QC" if code
                            else "session proved but code missing")
            self._log(verbose, f"  [skip-stale] {node_id}: {stale_reason} — re-proving")
            self._session.mark_pending(node_id, 0, f"stale session: {stale_reason}")

        # (b) Session not done — try exact polib lookup (catches "session went
        #     stale during a prior run but Polib.lean does have it").
        existing = self._polib_search.find_by_node_id(node_id)
        if existing is not None:
            status = self._accept_existing_code(
                node, node_id, existing, parsed, locked, verbose, "skip",
            )
            if status is not None:
                return status

        # (c) No exact match — guard: deps must be settled before we attempt this node.
        failed_deps = [d for d in node.dependencies if d not in proven_node_ids]
        if failed_deps:
            self._log(verbose, f"  [dep-fail] {node_id} — unresolved deps: {failed_deps}")
            self._session.mark_pending(node_id, 0, f"unresolved deps: {failed_deps}")
            return "pending"

        # (d) Last cache-accept chance: fuzzy polib search.
        fuzzy = self._polib_search.search(node, parsed)
        if fuzzy is not None:
            status = self._accept_existing_code(
                node, node_id, fuzzy, parsed, locked, verbose, "found",
            )
            if status is not None:
                return status

        # ── Fresh prove via the single-session proof_agent ────────────
        # Per-node LockedGoal: main target uses the conjecture's step-2 lock;
        # sub-lemmas use their planner-supplied lean_signature.  Sub-lemmas
        # without a lean_signature CANNOT be proved — the LLM would receive
        # the main theorem's signature and write `theorem C104` for every
        # sub-node, which our acceptance check then (correctly) rejects.
        if node.is_main_target:
            node_locked = locked
        elif node.lean_signature:
            fixed_sig = _autofix_lean_sig(node.lean_signature)
            node_locked = LockedGoal(
                lean_signature=fixed_sig,
                validator_confirmed=True,
            )
            # Sig pre-check: compile `{sig} sorry` BEFORE handing it to Opus.
            # If the planner-supplied signature is malformed (bad Lean syntax,
            # references a non-existent type / lemma, wrong arity, …) Opus
            # would spend its 1500s budget chasing the same error forever.
            # Catching it here saves 25 minutes per bad node.
            if not self._signature_compiles(fixed_sig, node_id, verbose):
                # Evict blueprint cache so step 5 retry (or the next full run)
                # re-decomposes with the planner getting fresh feedback,
                # instead of processing the same broken blueprint forever.
                self._evict_blueprint_for_bad_sig(node_id, verbose)
                self._session.mark_pending(
                    node_id, 0,
                    "planner-supplied lean_signature does not compile (with sorry body); "
                    "blueprint cache evicted — next run will re-decompose",
                )
                return "pending"
        else:
            self._log(verbose,
                f"  [bad-blueprint] {node_id}: planner omitted lean_signature for "
                f"non-main node — cannot prove without a target signature")
            self._session.mark_pending(
                node_id, 0,
                "planner blueprint missing `lean_signature` for non-main-target node",
            )
            return "pending"

        if self._flog:
            self._flog.start_node(node_id, node.node_type, node.description)

        from agent.prover.proof_agent import prove_node as _prove_node
        try:
            attempt = _prove_node(
                node=node,
                locked_goal=node_locked,
                compiler=self._compiler,
                project_root=Path(self._config.polib_path).parent,
                proven_dep_ids=list(node.dependencies),
                model=self._config.model_main,
                effort=self._config.proof_agent_effort,
                max_turns=self._config.proof_agent_max_turns,
                timeout_seconds=self._config.proof_agent_timeout_seconds,
                log_fn=lambda msg: self._log(verbose, msg),
            )
        except GoalTamperedError:
            raise
        except Exception as exc:
            self._log(verbose, f"  [proof-agent-exc] {node_id}: {exc}")
            self._session.mark_pending(node_id, 0, str(exc))
            if self._flog:
                self._flog.finish_node(node_id, "failed", sorry_count=0)
            return "pending"

        return self._finalise_attempt(node, node_id, attempt, parsed, node_locked, category, verbose)

    # ------------------------------------------------------------------
    # Quality-check + save the proof_agent's output
    # ------------------------------------------------------------------

    def _finalise_attempt(
        self,
        node: BlueprintNode,
        node_id: str,
        attempt,
        parsed: "ParsedTheorem",
        locked: "LockedGoal",
        category: str,
        verbose: bool,
    ) -> str:
        lean_code = attempt.code
        report = self._quality.check(parsed, locked, lean_code, is_main_target=node.is_main_target)
        with self._run_codes_lock:
            self._run_quality_reports[node_id] = report

        # Reject imports-only (the false-positive that burned P6GenusG before).
        # Search for the EXPECTED declaration name extracted from the locked
        # signature — for sub-lemmas this is the planner-supplied name (often
        # equal to node_id), for the main target it's the conjecture's lean name.
        expected_name = _expected_decl_name(node, locked)
        has_target_decl = bool(re.search(
            r'^(?:private\s+|protected\s+|noncomputable\s+)*'
            r'(?:lemma|theorem|def|abbrev)\s+' + re.escape(expected_name) + r'\b',
            lean_code, re.MULTILINE,
        ))
        if not has_target_decl:
            self._log(verbose,
                f"  [decl-missing] {node_id}: expected `{expected_name}` not found in proved code")
        # Reject trivially-degenerate main targets — `theorem X : True := by trivial`
        # proves nothing about the conjecture.  No more "accept partial if Polib
        # already has it" backdoor — those stale entries are evicted on next run
        # via _load_cached_blueprint's evict path.
        if node.is_main_target and _TRIVIAL_TYPE_RE.search(lean_code):
            self._log(verbose,
                f"  [trivial-type] {node_id}: main target has degenerate return type "
                f"(True/False/Prop) — failing node")
            return self._fail_node(node_id, lean_code, report,
                                   reason=f"trivial main-target type: {attempt.reason}",
                                   verbose=verbose)

        sorry_free = attempt.success and report.sorry_count == 0 and has_target_decl and report.passed

        if sorry_free:
            # No "already in polib" short-circuit: store.save does
            # _remove_node_section before writing, so re-saving is safe AND
            # necessary — a stale partial entry under this node_id must be
            # OVERWRITTEN by the new clean proof, otherwise the sorry-tainted
            # version persists in Polib.
            return self._save_proved(node, node_id, lean_code, report, category, verbose)

        if attempt.success and report.sorry_count > 0:
            return self._fail_node(node_id, lean_code, report,
                                   reason=f"compiled with {report.sorry_count} sorry(s) — sorry not accepted",
                                   verbose=verbose)

        return self._fail_node(node_id, lean_code, report,
                               reason=attempt.reason or "compile failed",
                               verbose=verbose)

    def _save_proved(
        self, node: BlueprintNode, node_id: str, lean_code: str, report, category: str, verbose: bool,
    ) -> str:
        """Transactional save: write the entry, verify Polib still builds,
        roll back on failure.  Updates session + dep_graph on success.

        Caller has already verified ``report.sorry_count == 0`` (no-new-sorry
        policy) — ``store.save`` will therefore always classify the entry as
        ``"proved"``, never ``"partial"``.
        """
        try:
            with self._polib_store.transaction() as store:
                entry = store.save(node, lean_code, report, category)
                # Verify inside the transaction: no other thread can modify
                # Polib between save and verify, so any build failure is
                # unambiguously caused by this entry.
                if not self._verify_polib_builds(node_id, verbose):
                    store.remove(node_id)
                    raise PolibSaveError(
                        f"Node {node_id!r}: entry broke Polib.lean build, rolled back"
                    )
            assert entry.status == "proved", (
                f"_save_proved invariant violated: store.save returned status="
                f"{entry.status!r} but caller guaranteed sorry-free code"
            )
            with self._save_lock:
                self._dep_graph.record_edges(entry.node_id, lean_code)
                self._dep_graph.save()
            self._session.mark_done(node_id, "proved")
            self._maybe_regenerate_explorer()
            self._log(verbose, f"  [saved] {node_id} → polib (proved)")
            with self._run_codes_lock:
                self._run_codes[node_id] = lean_code
            if self._flog:
                self._flog.finish_node(node_id, "proved", sorry_count=0)
            return "proved"
        except PolibSaveError as exc:
            return self._fail_node(node_id, lean_code, report,
                                   reason=str(exc), verbose=verbose)

    def _fail_node(
        self, node_id: str, lean_code: str, report,
        reason: str, verbose: bool,
    ) -> str:
        """Mark *node_id* as pending with *reason* and record the failed code."""
        self._log(verbose, f"  [fail] {node_id} — {reason[:160]}")
        self._session.mark_pending(
            node_id, self._config.max_rounds_per_node, reason,
            failed_code=lean_code or None,
        )
        if self._flog:
            self._flog.finish_node(node_id, "failed", sorry_count=report.sorry_count if report else 0)
        return "pending"

    def _maybe_regenerate_explorer(self) -> None:
        """Best-effort HTML explorer regeneration after each successful save."""
        try:
            from visualizer.generate import generate_explorer
            generate_explorer(
                Path(self._config.store_path),
                Path(self._config.polib_path) / "proof_explorer.html",
            )
        except Exception:
            pass

    def _evict_blueprint_for_bad_sig(self, node_id: str, verbose: bool) -> None:
        """Clear the blueprint cache when a planner-supplied signature is
        malformed.  Without eviction, step 5 retry + subsequent runs would
        keep pulling the same broken blueprint out of ``store.json`` and
        the sub-lemma would fail sig-check forever.

        Best-effort: any store I/O error is swallowed with a log, since
        this is a recovery path, not the primary flow.
        """
        try:
            blueprints = dict(self._store.get("blueprints") or {})
            n_cleared = len(blueprints)
            if n_cleared:
                self._store.update("blueprints", {})
                self._log(verbose,
                    f"  [cache-evict] blueprint cache cleared "
                    f"({n_cleared} entries) after bad sig on {node_id} — "
                    f"next run will re-decompose")
        except Exception as exc:
            self._log(verbose,
                f"  [cache-evict-err] failed to clear blueprint cache: {exc}")
