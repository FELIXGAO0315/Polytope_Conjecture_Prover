"""Per-node solver (mixin for FormalizerAgent).

Contains the two largest methods in the formalization pipeline:

* ``_compile_loop`` — the retry orchestrator.  Compiles a single node, and on
  failure cycles through fix strategies + stagnation detection + escalation
  phases until the node compiles, a sub-lemma decomposition is requested, or
  the round budget is exhausted.
* ``_process_node`` — the per-node entry point used by the parallel level
  scheduler.  Handles caching/aliasing, dispatches to ``_partial_solver``,
  takes the sub-lemma decomposition branch when ``_compile_loop`` signals it,
  runs the quality check, and saves to Polib (or fails the node).

Plus supporting helpers:

* ``_compute_parallel_levels`` — topo-sort → parallel level grouping.
* ``_verify_polib_builds`` — minimal-file compile guarding the save→verify
  transaction.
* ``_try_sorry_save`` — fallback path for nodes that compiled standalone
  but broke Polib when added.
* ``_get_partial_dep_code`` — read partial-dep code from ``output/Output/``.
* ``_llm_decide_decompose``, ``_prove_sub_lemma``, ``_prove_sub_lemmas_parallel``,
  ``_assemble_with_sub_lemmas`` — the LLM-driven sub-lemma decomposition path,
  triggered when ``_compile_loop`` cannot close the node within budget.

These methods rely on attributes/methods defined elsewhere on
FormalizerAgent (``self._compiler``, ``self._sdk``, ``self._polib_store``,
``self._session``, ``self._run_codes``, ``self._quality``, ``self._log``,
``self._inject_pattern_hints``, ``self._rank_and_trim_hints``,
``self._regen_hints_from_bad_name``, ``self._generate_lean``,
``self._partial_solver``, ``self._targeted_fix*`` strategies via
StrategiesMixin, ``self._llm_hint_generator``, ``self._reasoning_hint_generator``,
``self._hint_generator``, ``self._polib_search``, ``self._format_dep_signatures_block``,
``self._local_refs_block``, ``self._write_output``, ``self._flog``,
``self._thread_local``, ``self._run_codes_lock``, ``self._save_lock``,
``self._config``).
"""
from __future__ import annotations

import os
import re
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import TYPE_CHECKING

from agent.exceptions import GoalTamperedError, PolibSaveError
from agent.prover import lean_codegen
from agent.prover.tools.blueprint import Blueprint, BlueprintNode
from agent.prover.tools.llm_hint_generator import FailureRecord

if TYPE_CHECKING:
    from agent.prover.tools.goal_lock import GoalLock
    from agent.prover.tools.latex_parser import ParsedTheorem


class NodeSolverMixin:
    def _compute_parallel_levels(self, blueprint: Blueprint) -> list[list[str]]:
        """Group topo_order into parallel levels based on dependencies.

        All nodes at the same level have all their dependencies at lower levels
        and can therefore be compiled concurrently.
        """
        node_level: dict[str, int] = {}
        for node_id in blueprint.topo_order:
            node = blueprint.get_node(node_id)
            if not node.dependencies:
                node_level[node_id] = 0
            else:
                missing_deps = [dep for dep in node.dependencies if dep not in node_level]
                if missing_deps:
                    raise BlueprintError(
                        f"_compute_parallel_levels: node '{node_id}' has dependencies "
                        f"{missing_deps} that were not assigned a level. "
                        f"This indicates a topological sort failure."
                    )
                node_level[node_id] = max(
                    (node_level[dep] for dep in node.dependencies),
                    default=0,
                ) + 1

        max_level = max(node_level.values(), default=0)
        levels: list[list[str]] = [[] for _ in range(max_level + 1)]
        for node_id in blueprint.topo_order:
            levels[node_level[node_id]].append(node_id)
        return levels


    def _verify_polib_builds(self, node_id: str, verbose: bool) -> bool:
        """Compile a minimal file importing Polib to check the package still builds cleanly.

        Must actually `import Polib`: compile() goes through `lake build`, which
        rebuilds the (just-modified) Polib.lean — a save that broke Polib fails
        here and triggers rollback. (The previous version only imported
        Inventory, so this gate was vacuous and broken saves persisted until
        the end-of-run PolibValidator.)"""
        _result = self._compiler.compile(
            "import Mathlib\nimport Inventory\nimport Polib\n", f"_polib_verify_{node_id}"
        )
        if not _result.success:
            err = (_result.errors[0].raw_message[:80] if _result.errors
                   else (_result.stderr or "build failed")[:80])
            self._log(verbose, f"  [polib-broken] {node_id}: Polib.lean build failed: {err}")
            return False
        return True


    def _try_sorry_save(
        self,
        lean_code: str,
        node: "BlueprintNode",
        node_id: str,
        parsed: "ParsedTheorem",
        goal_lock: "GoalLock",
        category: str,
        verbose: bool,
        reason: str,
    ) -> "str | None":
        """Insert sorry into lean_code, try to save to Polib, verify build.

        Returns "partial" on success, None on failure.
        Used as a fallback when a compiled proof breaks the Polib build.
        """
        from agent.prover.tools.lean_compiler import CompileResult as _CR
        _dummy = _CR(
            success=False, exit_code=1, stdout="", stderr=reason,
            errors=[], warnings=[], compile_time_seconds=0.0, module_name=node_id,
        )
        _sorried = self._insert_sorry(lean_code, _dummy, node)
        _sr = self._compiler.compile(_sorried, node_id)
        if not _sr.success:
            self._log(verbose, f"  [sorry-save-err] {node_id}: sorry'd version also failed to compile")
            return None
        try:
            _sr_report = self._quality.check(parsed, goal_lock.goal, _sorried, is_main_target=node.is_main_target)
            with self._polib_store.transaction() as store:
                store.save(node, _sorried, _sr_report, category, parsed)
                if not self._verify_polib_builds(node_id, verbose):
                    store.remove(node_id)
                    self._log(verbose, f"  [sorry-save-err] {node_id}: sorry'd version also broke Polib")
                    return None
            self._session.mark_partial(node_id, self._config.max_rounds_per_node, f"sorry-fallback: {reason}")
            with self._run_codes_lock:
                self._run_codes[node_id] = _sorried
            if self._flog:
                self._flog.finish_node(node_id, "partial", sorry_count=_sr_report.sorry_count)
            self._log(verbose, f"  [sorry-saved] {node_id}: saved sorry fallback to Polib (partial)")
            return "partial"
        except Exception as _se:
            self._log(verbose, f"  [sorry-save-err] {node_id}: {_se}")
            return None


    def _get_partial_dep_code(self, dep_id: str) -> str | None:
        """Return cleaned Lean code for a partial (not-yet-proved) dependency, or None."""
        output_file = self._output_root / "Output" / f"{dep_id}.lean"
        if not output_file.exists():
            return None
        code = output_file.read_text(encoding="utf-8")
        # Strip import lines — caller provides its own preamble
        lines = [l for l in code.splitlines() if not l.startswith("import ")]
        return "\n".join(lines).strip() or None


    def _llm_decide_decompose(
        self,
        lean_code: str,
        result: "CompileResult",
        node: BlueprintNode,
        hints: list[str],
    ) -> list[dict] | None:
        """Ask the LLM whether to decompose this node into sub-lemmas.

        Returns a list of sub-lemma dicts (name, statement, description,
        proof_hint) if decomposition is recommended, else None.
        """
        error_block = lean_codegen.format_errors_for_prompt(result.errors, max_chars=2000)
        hints_str = "\n".join(f"  - {h}" for h in hints) or "  (none)"
        # Collect proved dependencies available in Polib so the LLM can reference them
        proved_deps: list[str] = []
        for dep_id in node.dependencies:
            entry = self._polib_search.find_by_node_id(dep_id)
            if entry and entry.status == "proved":
                proved_deps.append(dep_id)
        proved_deps_str = "\n".join(f"  - {d}" for d in proved_deps) or "  (none)"
        prompt = (
            f"A Lean 4 proof has failed to compile after several attempts.\n\n"
            f"## Node\n{node.node_id}: {node.description}\n\n"
            f"## Compilation Error\n```\n{error_block}\n```\n\n"
            f"## Current Lean 4 Source\n```lean\n{lean_code}\n```\n\n"
            f"## Proved dependencies available to call directly\n{proved_deps_str}\n\n"
            f"## Available Mathlib Lemmas\n{hints_str}\n\n"
            f"Decide: should this lemma be decomposed into smaller independent sub-lemmas "
            f"that are each easier to prove?\n\n"
            f"CRITICAL RULES for sub-lemma statements:\n"
            f"1. Each sub-lemma must be CONSISTENT with the parent lemma's hypotheses — "
            f"do NOT add hypotheses that contradict the parent (e.g. if parent has `hm : m ≥ 6`, "
            f"a sub-lemma must not have `hm : m < 6`).\n"
            f"2. Each sub-lemma must cover a REAL step in the proof that the proved dependencies "
            f"above cannot directly handle.\n"
            f"3. Sub-lemma statements must be valid Lean 4 that can compile independently.\n\n"
            f"If YES — respond with JSON listing the sub-lemmas. Each sub-lemma must be a "
            f"`private lemma` or `private def` that can be proved INDEPENDENTLY.\n\n"
            f"If NO — respond with {{\"should_decompose\": false}}.\n\n"
            f"JSON schema when decomposing:\n"
            f"{{\n"
            f'  "should_decompose": true,\n'
            f'  "reason": "one sentence",\n'
            f'  "sub_lemmas": [\n'
            f'    {{\n'
            f'      "name": "CamelCaseName",\n'
            f'      "statement": "private lemma CamelCaseName ... : ... := by\\n  sorry",\n'
            f'      "description": "what this sub-lemma proves",\n'
            f'      "proof_hint": "key tactic or approach"\n'
            f'    }}\n'
            f'  ]\n'
            f"}}\n\n"
            f"Respond ONLY with valid JSON. No prose outside the JSON."
        )
        # Haiku-first escalation — decompose-decision is short structured JSON,
        # Haiku handles it reliably and saves Sonnet wallclock for the actual
        # sub-lemma proofs.
        raw = self._sdk._call(
            prompt,
            fast_model=self._config.model_fast,
            timeout=int(os.environ.get("PROVER_FIX_TIMEOUT", "240")),
        )
        # Extract JSON from response
        raw = raw.strip()
        m = re.search(r"\{.*\}", raw, re.DOTALL)
        if not m:
            return None
        try:
            data = json.loads(m.group(0))
        except json.JSONDecodeError:
            return None
        if not data.get("should_decompose"):
            return None
        subs = data.get("sub_lemmas", [])
        if not subs or not isinstance(subs, list):
            return None
        return subs


    def _prove_sub_lemma(
        self,
        sub: dict,
        parent_node: BlueprintNode,
        hints: list[str],
        verbose: bool,
    ) -> tuple[str, str, bool]:
        """Prove one sub-lemma. Returns (name, lean_code, success)."""
        name = sub.get("name", "SubLemma")
        stmt = sub.get("statement", "")
        desc = sub.get("description", "")
        hint_extra = sub.get("proof_hint", "")

        # Pass `stmt` as lean_signature so _generate_lean uses the locked-goal
        # path (L2.B). `stmt` already contains the full Lean declaration header
        # from the dynamic-decompose schema, e.g.
        # `private lemma X (maps : ...) : ... := by sorry`. Strip the trailing
        # `sorry` (and any trailing whitespace) so the signature matches the
        # convention used by goal_lock (ends at `:= by`).
        sub_sig: str | None = None
        if stmt and stmt.strip():
            sub_sig = re.sub(r"\bsorry\b\s*$", "", stmt.strip()).rstrip() or None
        sub_node = BlueprintNode(
            node_id=name,
            node_type="lemma",
            description=desc,
            latex_fragment=parent_node.latex_fragment,
            dependencies=[],
            is_main_target=False,
            lean_signature=sub_sig,
        )
        sub_hints = ([hint_extra] if hint_extra else []) + hints

        # Wrap statement in a compilable file
        code = (
            f"import Mathlib\nimport Inventory\n\n"
            f"{stmt}\n"
        )
        code = lean_codegen.normalize_lean(code)

        self._log(verbose, f"    [sub-prove] {name}: {desc[:60]}")
        lean_code, ok, _ = self._compile_loop(
            code, sub_node, sub_hints, name, verbose=False,
            _allow_decompose=False,
        )
        # Sub-lemma must be truly sorry-free — Lean compiles sorry as a warning,
        # so ok=True from _compile_loop does not guarantee the proof is complete.
        if ok and (lean_codegen.has_sorry(lean_code) or lean_codegen.find_sorry_blocks(lean_code)):
            ok = False
        status = "ok" if ok else "FAILED"
        self._log(verbose, f"    [sub-{status}] {name}")
        return name, lean_code, ok


    def _prove_sub_lemmas_parallel(
        self,
        sub_specs: list[dict],
        parent_node: BlueprintNode,
        hints: list[str],
        verbose: bool,
    ) -> list[tuple[str, str, bool]]:
        """Prove sub-lemmas in parallel. Returns list of (name, code, success)."""
        n = len(sub_specs)
        self._log(verbose, f"  [decompose] {parent_node.node_id} → {n} sub-lemma(s):")
        for i, s in enumerate(sub_specs, 1):
            self._log(verbose, f"      [{i}/{n}] {s.get('name','?')}: {s.get('description','')[:70]}")
        self._log(verbose, f"  [sub-prove] launching {n} parallel workers...")

        results: list[tuple[str, str, bool]] = []
        with ThreadPoolExecutor(max_workers=n) as executor:
            future_to_sub = {
                executor.submit(self._prove_sub_lemma, sub, parent_node, hints, verbose): sub
                for sub in sub_specs
            }
            for future in as_completed(future_to_sub):
                try:
                    results.append(future.result())
                except Exception as exc:
                    sub = future_to_sub[future]
                    name = sub.get("name", "?")
                    self._log(verbose, f"    [sub-err] {name}: {exc}")
                    results.append((name, "", False))
        return results


    def _assemble_with_sub_lemmas(
        self,
        node: BlueprintNode,
        sub_results: list[tuple[str, str, bool]],
        hints: list[str],
        verbose: bool,
    ) -> tuple[str, bool]:
        """Generate the main lemma given proved sub-lemmas. Returns (code, success)."""
        # If every sub-lemma failed there is nothing to assemble — skip to avoid a
        # pointless (and slow) LLM call that would just produce more sorry placeholders.
        if not any(ok for _, _, ok in sub_results):
            self._log(verbose, f"  [assemble-skip] {node.node_id}: all sub-lemmas failed, skipping assembly")
            return "", False
        self._log(verbose, f"  [assemble] {node.node_id}: assembling from sub-lemmas")

        # Collect ONLY proved sub-lemma bodies (failed ones bloat the prompt with useless code)
        sub_bodies: list[str] = []
        for name, code, ok in sub_results:
            if not ok or not code:
                continue
            # Strip import lines
            body_lines = [
                l for l in code.splitlines()
                if not l.startswith("import ") and l.strip() != ""
            ]
            sub_bodies.append("\n".join(body_lines))

        proved_names = [name for name, _, ok in sub_results if ok]
        failed_names = [name for name, _, ok in sub_results if not ok]

        hints_str = "\n".join(f"  - {h}" for h in hints) or "  (none)"
        proved_str = "\n\n".join(sub_bodies) if sub_bodies else "(none proved)"
        prompt = (
            f"Complete the Lean 4 proof of the main lemma using the sub-lemmas below.\n\n"
            f"## Main Node\n{node.node_id}: {node.description}\n\n"
            f"## Proved Sub-lemmas (include these verbatim before the main lemma)\n"
            f"```lean\n{proved_str}\n```\n\n"
            + (f"## Sub-lemmas that FAILED (use sorry for these if needed)\n"
               f"{', '.join(failed_names)}\n\n" if failed_names else "")
            + f"## Available Mathlib Lemmas\n{hints_str}\n\n"
            f"Instructions:\n"
            f"- Start with `import Mathlib\\nimport Inventory`\n"
            f"- Include all proved sub-lemma code verbatim\n"
            f"- Then write the main lemma `{node.node_id}` calling the sub-lemmas\n"
            f"- Use `∑ x ∈ s, f x` notation (∈ not `in`)\n"
            f"- Return ONLY the complete Lean 4 file inside a ```lean fence."
        )
        # Assembly prompts are large (multiple sub-lemmas); use a longer timeout.
        # Haiku-first escalation — assembly is mostly stitching proved sub-lemma
        # bodies, often within Haiku's reach.
        try:
            raw = self._sdk._call(
                prompt,
                fast_model=self._config.model_fast,
                timeout=int(os.environ.get("PROVER_FIX_TIMEOUT", "240")),
            )
        except Exception as exc:
            self._log(verbose, f"  [assemble-timeout] {node.node_id}: assembly call failed ({exc}), returning failure")
            return "", False
        code = lean_codegen.normalize_lean(lean_codegen.strip_markdown(raw))
        code = lean_codegen.ensure_preamble(code)
        if not code.strip():
            return "", False

        result = self._compiler.compile(code, node.node_id)
        self._write_output(code, node.node_id, result.success)
        if result.success:
            self._log(verbose, f"  [assemble-ok] {node.node_id}: assembled proof compiled")
            return code, True

        # Fix loop: up to 3 rounds of targeted_fix_strict + compile
        for fix_round in range(3):
            err = (result.errors[0].raw_message[:80] if result.errors
                   else (result.stderr or "build failed")[:80])
            self._log(verbose, f"  [assemble-err] {node.node_id} fix {fix_round}: {err}")
            # Parallel: run targeted_fix and targeted_fix_strict simultaneously
            with ThreadPoolExecutor(max_workers=2) as _aex:
                _ff = _aex.submit(self._targeted_fix, code, result, node, hints, fix_round)
                _fs = _aex.submit(self._targeted_fix_strict, code, result, node, hints, fix_round)
                _fixed0, _fixed1 = _ff.result(), _fs.result()
            with ThreadPoolExecutor(max_workers=2) as _aex:
                _rr0 = _aex.submit(self._compiler.compile, _fixed0, node.node_id)
                _rr1 = _aex.submit(self._compiler.compile, _fixed1, node.node_id)
                _res0, _res1 = _rr0.result(), _rr1.result()
            self._write_output(_fixed0, node.node_id, _res0.success)
            self._write_output(_fixed1, node.node_id, _res1.success)
            if _res0.success or _res1.success:
                code = _fixed0 if _res0.success else _fixed1
                self._log(verbose, f"  [assemble-ok] {node.node_id}: fixed after {fix_round + 1} pass(es)")
                return code, True
            # Take the one with fewer errors for the next fix round
            code, result = (
                (_fixed0, _res0) if len(_res0.errors) <= len(_res1.errors)
                else (_fixed1, _res1)
            )
        return code, False


    def _compile_loop(
        self,
        lean_code: str,
        node: BlueprintNode,
        hints: list[str],
        node_id: str,
        verbose: bool,
        _allow_decompose: bool = True,
        goal_signature: str = "",
    ) -> tuple[str, bool, list]:
        """Run the compile + targeted-fix retry loop with escalation phases.

        Returns (best_lean_code, compile_ok, last_errors).
        """
        compile_ok = False
        last_errors: list = []
        active_hints = list(hints)
        detector = StagnationDetector()
        _phase1_refreshed = False
        _decompose_checked = False
        _meta_hints_generated = False  # call LLMHintGenerator at most once per node
        current_strategy = "initial_generation"
        failure_history: list[FailureRecord] = []
        # Accumulate identifiers that Lean rejected as unknown/invalid across all rounds.
        # These are injected into every fix prompt so the LLM stops re-inventing them.
        banned_ids: set[str] = set()
        # Count rounds whose primary error class is "unknown identifier / invalid field".
        # Used for cross-identifier stagnation: even if the LLM switches to a different
        # non-existent name each round, the error *class* is the same → escalate sooner.
        _unknown_id_rounds = 0
        _fix_attempt = 0  # counts fix attempts across all rounds

        for round_num in range(self._config.max_rounds_per_node):
            result = self._compiler.compile(lean_code, node_id)
            self._write_output(lean_code, node_id, result.success)
            if self._flog:
                self._flog.log_compile_round(node_id, "compile_loop", current_strategy, lean_code, result)

            if result.success:
                if not lean_codegen.has_sorry(lean_code):
                    compile_ok = True
                    self._log(verbose, f"  [ok]  {node_id} compiled (round {round_num})")
                    break
                # Compiled with sorry — try mechanical tactics first, then sorry-removal fix.
                n_sorry = len(lean_codegen.find_sorry_blocks(lean_code))
                self._log(verbose,
                    f"  [sorry] {node_id} round {round_num}: compiled with {n_sorry} sorry(s), attempting removal")
                mechanical = self._try_mechanical_tactics(lean_code, node_id, verbose)
                if mechanical is not None and not lean_codegen.has_sorry(mechanical):
                    lean_code = mechanical
                    compile_ok = True
                    self._log(verbose, f"  [ok]  {node_id}: sorry removed by mechanical tactic")
                    break
                if round_num < self._config.max_rounds_per_node - 1:
                    _fix_attempt += 1
                    self._log(verbose, f"  [fix]  {node_id} round {round_num}, fix #{_fix_attempt}: attempting sorry removal")
                    fixed = self._targeted_fix_sorry_removal(lean_code, node, active_hints, round_num)
                    if fixed and fixed.strip() != lean_code.strip():
                        lean_code = fixed
                        current_strategy = "sorry_removal"
                        continue
                # No more rounds or fix unchanged — sorry could not be removed, node fails
                self._log(verbose, f"  [sorry-fail] {node_id}: sorry could not be removed, failing node")
                break

            last_errors = result.errors
            error_summary = (result.errors[0].raw_message[:80] if result.errors
                             else (result.stderr or "build failed")[:80])
            self._log(verbose, f"  [err] {node_id} round {round_num}: {error_summary}")

            # Collect banned identifiers from all errors in this round
            _this_round_unknown = False
            _retry_after_strip = False
            for err in result.errors:
                if err.error_class == "F":
                    raise GoalTamperedError(
                        f"Class F error in node '{node_id}': {err.raw_message}"
                    )
                # "already been declared" means a name is already in Polib.lean.
                if "has already been declared" in err.raw_message:
                    # Extract which name was already declared
                    _decl_m = re.search(r"`(\w+)` has already been declared", err.raw_message)
                    _decl_name = _decl_m.group(1) if _decl_m else None

                    if _decl_name and _decl_name != node_id:
                        # The LLM inlined a proved dependency — strip that definition and retry.
                        lean_code = lean_codegen.strip_named_declaration(lean_code, _decl_name)
                        self._log(verbose,
                            f"  [strip-inline] {node_id}: removed inlined `{_decl_name}` "
                            f"(already in Polib), retrying")
                        _retry_after_strip = True
                        break  # break inner err loop, then continue outer round loop

                    # The current node itself is already declared in Polib → load it.
                    existing_code = self._load_polib_code(node_id)
                    if existing_code and not lean_codegen.has_sorry(existing_code):
                        self._log(verbose,
                            f"  [already-proved] {node_id}: name exists in Polib.lean, treating as proved")
                        return existing_code, True, []
                    if existing_code:
                        # Partial already in Polib — accept it rather than cascade-failing deps.
                        self._log(verbose,
                            f"  [already-partial] {node_id}: partial in Polib, accepting existing")
                        return existing_code, True, []
                    # Name exists but code not loadable — fail (no sorry insertion)
                    self._log(verbose,
                        f"  [already-declared] {node_id}: name conflict, failing node")
                    return lean_code, False, result.errors
                # Track unknown/invalid identifiers for the banned list
                # Pattern handles both `Foo` and dotted names `Foo.bar_baz`.
                for pat in (
                    r"Unknown identifier `([\w.]+)`",
                    r"Unknown constant `([\w.]+)`",  # Mathlib name hallucination
                    r"Invalid field `([\w.]+)`",
                ):
                    m = re.search(pat, err.raw_message)
                    if m:
                        banned_ids.add(m.group(1))
                        _this_round_unknown = True
                        # Change 4: error-conditioned hint regen for Mathlib
                        # name hallucinations. When LLM invents
                        # `Finset.sum_Ico_succ` (doesn't exist), query Loogle
                        # with the bad name's tokens and inject real candidates
                        # into next-round hints. Saves a round of Sonnet just
                        # to "find the real name".
                        if "Unknown constant" in err.raw_message or "." in m.group(1):
                            new_hints = self._regen_hints_from_bad_name(
                                m.group(1), active_hints, verbose
                            )
                            if new_hints:
                                # Prepend so they appear first in next round
                                active_hints = new_hints + [
                                    h for h in active_hints if h not in new_hints
                                ]
            if _retry_after_strip:
                continue  # restart the round with the stripped code (don't count as a new round)
            if _this_round_unknown:
                _unknown_id_rounds += 1

            # Record this failure for the meta-hint generator.
            failure_history.append(FailureRecord(
                round_num=round_num,
                strategy=current_strategy,
                error_classes=[e.error_class for e in result.errors],
                primary_error=(result.errors[0].raw_message if result.errors
                               else (result.stderr or "build failed"))[:200],
                lean_excerpt=(result.errors[0].lean_excerpt if result.errors else ""),
                banned_ids=list(banned_ids),
            ))

            if round_num == self._config.max_rounds_per_node - 1:
                # All rounds exhausted without a sorry-free proof — fail the node
                self._log(verbose, f"  [fail] {node_id}: max rounds exhausted, no sorry-free proof found")
                break

            # Stagnation detection via hash-based counting (Fix 4 + Fix 8).
            # Normalises line/col and identifier names so the same logical error
            # hashes identically across rounds even if the LLM cycles identifiers.
            primary_hash = lean_codegen.hash_primary_error(result.errors)
            is_stagnant = detector.record(primary_hash)
            detector.mark_strategy(current_strategy)

            # Cross-identifier stagnation: LLM keeps inventing non-existent names.
            if _unknown_id_rounds >= 2 and not is_stagnant:
                is_stagnant = True
                self._log(verbose,
                    f"  [id-stagnant] {node_id}: {_unknown_id_rounds} rounds with unknown "
                    f"identifier errors — banned: {sorted(banned_ids)}")

            # Stagnant after round 1 — no more fix attempts, fail the node
            if round_num >= 1 and is_stagnant:
                self._log(verbose,
                    f"  [stagnant-fail] {node_id}: stagnant at round {round_num}, failing node")
                break

            # Early decompose check: after DECOMPOSE_CHECK_AFTER failures, ask LLM
            if (
                _allow_decompose
                and not _decompose_checked
                and round_num + 1 >= self._DECOMPOSE_CHECK_AFTER
            ):
                _decompose_checked = True
                self._log(verbose,
                    f"  [decompose?] {node_id}: asking LLM after {round_num + 1} failed rounds")
                sub_specs = self._llm_decide_decompose(lean_code, result, node, active_hints)
                if sub_specs:
                    # Signal _process_node to run the decompose path
                    self._thread_local.pending_decompose = sub_specs
                    break

            if is_stagnant:
                effective_round = max(round_num, self._ESCALATION_HINT_REFRESH)
                self._log(verbose,
                    f"  [stagnant] {node_id}: hash threshold reached, "
                    f"escalating to phase {self._escalation_phase(effective_round)}")
                # Ask the meta-hint generator for a strategic pivot (once per node).
                if not _meta_hints_generated and len(failure_history) >= 2:
                    self._log(verbose, f"  [meta-hint] {node_id}: calling LLMHintGenerator")
                    meta_hints = self._llm_hint_generator.generate(
                        node, goal_signature, failure_history
                    )
                    if meta_hints:
                        active_hints = meta_hints + active_hints
                        self._log(verbose,
                            f"  [meta-hint] {node_id}: injected {len(meta_hints)} strategic hint(s)")
                    _meta_hints_generated = True
                detector.reset()
            else:
                effective_round = round_num

            phase = self._escalation_phase(effective_round)

            if phase in (0, 1):
                # ── Mechanical error-fix first (cheap, no LLM) ─────────────
                # Pattern-based substitutions for common tactic errors (`simp`
                # made no progress, linarith failed, …) and fuzzy name fixes
                # for Unknown identifier. Saves a 60-240s Sonnet call when
                # the fix is just `simp → omega` or similar.
                _mech_fixed = self._try_mechanical_error_fix(
                    lean_code, result.errors, node_id, verbose
                )
                if _mech_fixed is not None and _mech_fixed.strip() != lean_code.strip():
                    lean_code = _mech_fixed
                    current_strategy = "mechanical_error_fix"
                    continue  # next round; will recompile and proceed

                # Run targeted_fix and targeted_fix_strict in parallel; compile both.
                if phase == 1 and not _phase1_refreshed:
                    fresh = self._hint_generator.generate(node)
                    _lv = getattr(self, '_loogle_validator', None)
                    active_hints = _lv.filter_existing(fresh) if _lv else fresh
                    _phase1_refreshed = True
                _fix_attempt += 1
                self._log(verbose, f"  [fix]  {node_id} round {round_num}, fix #{_fix_attempt}: trying targeted_fix + targeted_fix_strict in parallel")
                with ThreadPoolExecutor(max_workers=2) as _pex:
                    _f0 = _pex.submit(self._targeted_fix, lean_code, result, node, active_hints, round_num, banned_ids)
                    _f1 = _pex.submit(self._targeted_fix_strict, lean_code, result, node, active_hints, round_num, banned_ids)
                    _c0, _c1 = _f0.result(), _f1.result()
                with ThreadPoolExecutor(max_workers=2) as _pex:
                    _r0 = _pex.submit(self._compiler.compile, _c0, node_id)
                    _r1 = _pex.submit(self._compiler.compile, _c1, node_id)
                    _res0, _res1 = _r0.result(), _r1.result()
                self._write_output(_c0, node_id, _res0.success)
                self._write_output(_c1, node_id, _res1.success)
                if _res0.success or _res1.success:
                    _best_code = _c0 if _res0.success else _c1
                    _winner = "targeted_fix_parallel" if _res0.success else "targeted_fix_strict_parallel"
                    if not lean_codegen.has_sorry(_best_code):
                        lean_code = _best_code
                        compile_ok = True
                        self._log(verbose, f"  [ok]  {node_id} compiled via parallel fix ({_winner}, round {round_num}, fix #{_fix_attempt})")
                        if self._flog:
                            self._flog.log_compile_round(node_id, "compile_loop", _winner, lean_code,
                                                         _res0 if _res0.success else _res1)
                        break
                    # Parallel fix succeeded but still has sorry — treat as needing removal
                    lean_code = _best_code
                    current_strategy = _winner
                # Neither succeeded — use the one with fewer errors for the next round
                fixed, next_strategy = (
                    (_c0, "targeted_fix_parallel") if len(_res0.errors) <= len(_res1.errors)
                    else (_c1, "targeted_fix_strict_parallel")
                )
            elif phase == 2:
                _fix_attempt += 1
                self._log(verbose, f"  [escalate] {node_id}: decomposing into sub-steps (round {round_num}, fix #{_fix_attempt})")
                fixed = self._targeted_fix_decompose(lean_code, result, node, active_hints, round_num, banned_ids)
                next_strategy = "targeted_fix_decompose"
            else:
                # phase 3: try mechanical tactics; if they fail, fail the node (no sorry)
                mechanical = self._try_mechanical_tactics(lean_code, node_id, verbose)
                if mechanical is not None and not lean_codegen.has_sorry(mechanical):
                    lean_code = mechanical
                    current_strategy = "mechanical_tactic"
                    continue
                self._log(verbose, f"  [fail] {node_id}: phase3 exhausted, no sorry-free proof found")
                break

            if fixed and fixed.strip() != lean_code.strip():
                lean_code = fixed
                current_strategy = next_strategy
            else:
                self._log(verbose, f"  [fix-skip] {node_id} round {round_num}: no change from Claude, failing node")
                break

        # Expose banned_ids so _process_node can use them in the structure-augment fallback
        self._thread_local.last_banned_ids = banned_ids
        return lean_code, compile_ok, last_errors


    def _process_node(
        self,
        node_id: str,
        blueprint: Blueprint,
        goal_lock: GoalLock,
        parsed: ParsedTheorem,
        category: str,
        proven_node_ids: list[str],
        verbose: bool,
        proven_dep_imports: dict[str, str] | None = None,
    ) -> str:
        """Process one blueprint node. Returns 'proved' | 'partial' | 'pending'.

        All nodes (new or partial) go through _partial_solver, which handles
        sorry elimination and fresh generation in a unified way.
        Proved nodes are skipped immediately.
        """
        node = blueprint.get_node(node_id)

        # Skip fully proved nodes — only if code can actually be recovered.
        # If session says "done" but code is missing from Polib.lean (stale
        # session state), fall through and re-prove rather than returning
        # "proved" with no code, which causes "code missing" in assembly.
        if self._session.is_done(node_id):
            self._log(verbose, f"  [skip] {node_id} (proved)")
            code = self._load_polib_code(node_id)
            if not code:
                # Exact name not in Polib.lean; recover via fuzzy polib search
                fallback = self._polib_search.search(node, parsed)
                # Same face-count discriminator as the main fuzzy-match site
                # to prevent silent type-mismatch from P6-bound aliased to P3-bound.
                if fallback and fallback.node_id != node_id:
                    n_tok = lean_codegen.face_count_tokens(node_id)
                    e_tok = lean_codegen.face_count_tokens(fallback.node_id)
                    if n_tok and e_tok and not (n_tok & e_tok):
                        self._log(verbose,
                            f"  [alias-reject] {node_id} → {fallback.node_id} "
                            f"(face-count mismatch: {sorted(n_tok)} vs {sorted(e_tok)})")
                        fallback = None
                if fallback and fallback.status == "proved":
                    code = self._load_polib_code(fallback.node_id)
                    if code:
                        # Same alias propagation as the main fuzzy-match site
                        # below — register so downstream prompts see real name.
                        if fallback.node_id != node_id:
                            self._polib_search.register_alias(node_id, fallback.node_id)
                        self._log(verbose, f"  [skip-recover] {node_id} code recovered via {fallback.node_id}")
            if code:
                _skip_report = self._quality.check(parsed, goal_lock.goal, code, is_main_target=node.is_main_target)
                with self._run_codes_lock:
                    self._run_codes[node_id] = code
                    self._run_quality_reports[node_id] = _skip_report
                    self._run_skipped_nodes.add(node_id)
                return "proved"
            # Code not found despite session saying proved — stale state.
            # Clear it and fall through to re-prove.
            self._log(verbose, f"  [skip-stale] {node_id} session proved but code missing — re-proving")
            self._session.mark_pending(node_id, 0, "stale session: code missing from polib")


        # Exact-name polib lookup: handles stale session state where is_done()
        # returns False but the node was proved in a previous run. This catches
        # the "has already been declared" failure mode where Polib.lean already
        # contains the definition but the session wasn't updated.
        _polib_exact = self._polib_search.find_by_node_id(node_id)
        if _polib_exact:
            code = self._load_polib_code(node_id)
            if _polib_exact.status == "proved" and code and not lean_codegen.has_sorry(code):
                self._log(verbose, f"  [skip] {node_id} (proved in polib, session stale)")
                self._session.mark_done(node_id, "proved")
                _skip_report = self._quality.check(parsed, goal_lock.goal, code, is_main_target=node.is_main_target)
                with self._run_codes_lock:
                    self._run_codes[node_id] = code
                    self._run_quality_reports[node_id] = _skip_report
                    self._run_skipped_nodes.add(node_id)
                return "proved"
            elif _polib_exact.status == "partial" and code:
                self._log(verbose, f"  [skip] {node_id} (partial in polib, session stale)")
                self._session.mark_partial(node_id, 0, "recovered from polib")
                _skip_report = self._quality.check(parsed, goal_lock.goal, code, is_main_target=node.is_main_target)
                with self._run_codes_lock:
                    self._run_codes[node_id] = code
                    self._run_quality_reports[node_id] = _skip_report
                    self._run_skipped_nodes.add(node_id)
                return "partial"

        # Guard: all declared dependencies must be proved/partial
        failed_deps = [d for d in node.dependencies if d not in proven_node_ids]
        if failed_deps:
            reason = f"unresolved deps: {failed_deps}"
            self._log(verbose, f"  [dep-fail] {node_id} — {reason}")
            self._session.mark_pending(node_id, 0, reason)
            return "pending"

        # Polib search: accept proved (sorry-free) or partial hits
        existing = self._polib_search.find_by_node_id(node_id) or self._polib_search.search(node, parsed)
        # Discriminator: fuzzy TF-IDF can be fooled when planner's description
        # literally mentions another already-proved lemma name (e.g. "Combine
        # the proved lemma C104_P3LowerBound (...) with ..."). The resulting
        # match silently aliases a p_6-bound node to a p_3-bound lemma, and
        # downstream cascade-fails on type mismatch. To prevent: when fuzzy
        # match would create an alias (names differ), require that the
        # SUBJECT face-count tokens in both node_ids agree.
        if existing and existing.node_id != node_id:
            node_face_tokens = lean_codegen.face_count_tokens(node_id)
            entry_face_tokens = lean_codegen.face_count_tokens(existing.node_id)
            # Reject the alias if both sides have face-count tokens AND they
            # don't share any (e.g. {P6} vs {P3}). If one side has no tokens
            # (e.g. a structural helper), allow the match.
            if (node_face_tokens and entry_face_tokens
                    and not (node_face_tokens & entry_face_tokens)):
                self._log(verbose,
                    f"  [alias-reject] {node_id} → {existing.node_id} "
                    f"(face-count mismatch: {sorted(node_face_tokens)} vs "
                    f"{sorted(entry_face_tokens)})")
                existing = None  # fall through to fresh proof generation
        if existing:
            # If fuzzy search resolved to a DIFFERENT name than the planner used,
            # register an alias so downstream dep-resolution (agent.py:554) can
            # surface the real Lean identifier in generation prompts. Without
            # this, the LLM is told the dep name is `node_id` (planner's name)
            # but Polib.lean has the lemma under `existing.node_id` → Unknown
            # identifier error at compile time.
            if existing.node_id != node_id:
                self._polib_search.register_alias(node_id, existing.node_id)
                self._log(verbose,
                    f"  [alias] {node_id} → {existing.node_id} (fuzzy match)")
            code = self._load_polib_code(existing.node_id)
            if existing.status == "proved" and code and not lean_codegen.has_sorry(code):
                self._log(verbose, f"  [found] {node_id} in polib (proved)")
                self._session.mark_done(node_id, "proved")
                _skip_report = self._quality.check(parsed, goal_lock.goal, code, is_main_target=node.is_main_target)
                with self._run_codes_lock:
                    self._run_codes[node_id] = code
                    self._run_quality_reports[node_id] = _skip_report
                    self._run_skipped_nodes.add(node_id)
                return "proved"
            elif existing.status == "partial" and code:
                self._log(verbose, f"  [found] {node_id} in polib (partial)")
                self._session.mark_partial(node_id, 0, "recovered from polib")
                _skip_report = self._quality.check(parsed, goal_lock.goal, code, is_main_target=node.is_main_target)
                with self._run_codes_lock:
                    self._run_codes[node_id] = code
                    self._run_quality_reports[node_id] = _skip_report
                    self._run_skipped_nodes.add(node_id)
                return "partial"
            elif existing.status == "proved":
                self._log(verbose, f"  [found] {node_id} matched polib but code has sorry — will re-prove")

        if self._flog:
            self._flog.start_node(node_id, node.node_type, node.description)

        # CombinedHintGenerator: one Haiku call + all Loogle queries in parallel.
        # All returned names come directly from Loogle so no post-validation needed.
        # Sized to cover the common case (≥3 hints back). We previously fired the
        # reasoning-hint generator speculatively in a background thread to overlap
        # latency — but ≥80% of runs landed in the `len(hints) ≥ 3` branch and
        # discarded the result, while the orphan thread kept running for ~3 minutes
        # and printed misleading `[claude_sdk escalate]` lines. Switched to
        # demand-driven: only invoke reasoning-hint when CombinedHintGenerator
        # actually came back sparse.
        goal_sig = goal_lock.goal.lean_signature if goal_lock and goal_lock.goal else ""
        hints = self._hint_generator.generate(node)
        self._log(verbose, f"  [hints] {node_id}: {len(hints)} (combined, verified)")

        if len(hints) < 3:
            self._log(verbose,
                f"  [reasoning-hint] {node_id}: only {len(hints)} hint(s), "
                f"invoking LLM proof sketch synchronously")
            try:
                sketch_hints = self._reasoning_hint_generator.generate(node, goal_sig)
            except Exception as exc:
                self._log(verbose,
                    f"  [reasoning-hint] {node_id}: sketch generation failed ({exc})")
                sketch_hints = []
            if sketch_hints:
                hints = hints + sketch_hints
                self._log(verbose, f"  [reasoning-hint] {node_id}: proof sketch added")

        # For partial nodes: ask the LLM whether current hints are sufficient to
        # complete the proof.  Skip and reuse the existing sorry-code if not.
        existing_code: str | None = None
        if self._session.is_partial(node_id):
            existing_code = self._load_polib_code(node_id, category)
            if existing_code:
                feasible, assess_sketch = self._reasoning_hint_generator.assess_and_sketch_partial(
                    node, existing_code, hints, goal_sig
                )
                if not feasible:
                    self._log(verbose, f"  [skip] {node_id} (partial — LLM assessed infeasible)")
                    with self._run_codes_lock:
                        self._run_codes[node_id] = existing_code
                    return "partial"
                # Feasible: prepend the completion sketch so the retry model sees it
                if assess_sketch:
                    hints = assess_sketch + hints
                self._log(verbose, f"  [partial-assess] {node_id}: LLM assessed feasible, retrying")

        mode = "retry-partial" if self._session.is_partial(node_id) else "gen"
        self._log(verbose,
            f"  [{mode}] {node_id} — {len(hints)} hints (validated)")

        hints = self._inject_pattern_hints(node, hints)
        # Change 2a: rank hints by goal-similarity, keep top 8. Reduces
        # prompt noise → fewer assistant turns consumed by Sonnet's
        # filtering thinking. See _rank_and_trim_hints docstring.
        hints = self._rank_and_trim_hints(
            hints, node,
            goal_signature=(goal_lock.goal.lean_signature if goal_lock and goal_lock.goal else ""),
            max_keep=8,
        )

        # For retry-partial: if the node already has a section in Polib.lean,
        # remove it before the compile attempt.  Without this, the temp file
        # does `import Inventory` + redefines the lemma → "has already been
        # declared" on round 0, so no LLM-generated code ever gets tested.
        # Save a backup so we can restore if the retry completely fails (keeps
        # the node as partial for downstream dependency resolution).
        _partial_backup: str | None = None
        if existing_code is not None and self._polib_store.lean_path.exists():
            _pc = self._polib_store.read()
            if f"\n-- === {node_id} " in _pc:
                _partial_backup = existing_code
                with self._polib_store.transaction() as store:
                    store.remove(node_id)
                self._log(verbose,
                    f"  [pre-remove] {node_id}: removed old partial from Polib before retry")

        # Load cross-run failure history so the LLM can avoid repeating past mistakes
        cross_run_errors = self._session.get_cross_run_errors(node_id) or None

        self._thread_local.pending_decompose = None
        try:
            lean_code, compile_ok, last_errors = self._partial_solver(
                node, goal_lock, hints, proven_node_ids, proven_dep_imports,
                category, node_id, verbose, existing_code,
                cross_run_errors=cross_run_errors,
            )
        except GoalTamperedError:
            raise  # always propagate goal-tamper errors
        except Exception as _solver_exc:
            # Any unexpected exception (API timeout, network error, etc.) — fail the node.
            self._log(verbose, f"  [solver-exc] {node_id}: {_solver_exc}")
            self._session.mark_pending(node_id, 0, str(_solver_exc))
            if self._flog:
                self._flog.finish_node(node_id, "failed", sorry_count=0)
            return "pending"

        # ── Decompose path: LLM decided to split into sub-lemmas ──────
        if not compile_ok and getattr(self._thread_local, 'pending_decompose', None):
            sub_specs = self._thread_local.pending_decompose
            self._thread_local.pending_decompose = None
            sub_results = self._prove_sub_lemmas_parallel(sub_specs, node, hints, verbose)
            assembled_code, assemble_ok = self._assemble_with_sub_lemmas(node, sub_results, hints, verbose)
            if assemble_ok:
                lean_code = assembled_code
                compile_ok = True
                last_errors = []
            elif assembled_code and assembled_code.strip():
                # Assembly failed to compile — node fails (no sorry insertion)
                self._log(verbose, f"  [assemble-fail] {node_id}: assembled code failed to compile, failing node")

        # ── Phase 4: quality check + save ─────────────────────────────
        report = self._quality.check(
            parsed, goal_lock.goal, lean_code, is_main_target=node.is_main_target
        )
        with self._run_codes_lock:
            self._run_quality_reports[node_id] = report
        # Reject imports-only files: an empty body compiles with 0 sorrys but
        # contains no actual proof — accepting it would mark the node as proved
        # with no code (the false-positive that burned P6GenusG).
        _has_target_decl = bool(re.search(
            r'^(?:private\s+|protected\s+|noncomputable\s+)*'
            r'(?:lemma|theorem|def|abbrev)\s+' + re.escape(node_id),
            lean_code, re.MULTILINE,
        ))
        sorry_free = compile_ok and report.sorry_count == 0 and _has_target_decl and report.passed

        # Reject trivially-degenerate proofs: a declaration whose return type is
        # bare `True`, `False`, or `Prop` proves nothing about the conjecture.
        # This catches the failure mode where the LLM falls back to `lemma X : True`.
        _trivial_type = bool(re.search(
            r'(?:lemma|theorem)\s+\S[^:]*:\s*(?:True|False|Prop)\s*(?::=|where)',
            lean_code,
        ))
        if _trivial_type and node.is_main_target:
            # If this trivial sorry is already saved in Polib from a previous run
            # (e.g. from an earlier nuclear-sorry), accept it as partial rather than
            # failing: any new compile would hit "already been declared" anyway.
            # Use _load_polib_code rather than polib_search since the entry may not
            # be in the index (polib_index only covers indexed saves, not all sections).
            _existing_in_polib = self._load_polib_code(node_id)
            if _existing_in_polib:
                self._log(verbose,
                    f"  [trivial-type-partial] {node_id}: trivial type already in Polib — "
                    f"accepting existing as partial")
                self._session.mark_partial(
                    node_id, self._config.max_rounds_per_node, "trivial type, already in Polib")
                with self._run_codes_lock:
                    self._run_codes[node_id] = lean_code
                if self._flog:
                    self._flog.finish_node(node_id, "partial", sorry_count=report.sorry_count)
                return "partial"
            self._log(verbose,
                f"  [trivial-type] {node_id}: main target has degenerate return type "
                f"(True/False/Prop) — treating as failed")
            compile_ok = False
            sorry_free = False

        # If the node is already present in Polib (e.g. an [already-proved] path loaded
        # existing code), skip the duplicate save — re-saving would cause a
        # "has already been declared" build failure and roll back to [fail].
        if sorry_free and compile_ok:
            _pc_now = self._polib_store.read()
            if f"\n-- === {node_id} " in _pc_now:
                self._log(verbose, f"  [already-in-polib] {node_id}: skipping duplicate save")
                self._session.mark_done(node_id, "proved")
                with self._run_codes_lock:
                    self._run_codes[node_id] = lean_code
                if self._flog:
                    self._flog.finish_node(node_id, "proved", sorry_count=0)
                return "proved"

        if sorry_free:
            try:
                with self._polib_store.transaction() as store:
                    entry = store.save(node, lean_code, report, category, parsed)
                    # Verify inside the transaction: no other thread can modify Polib
                    # between save and verify, so a build failure is unambiguously
                    # caused by this entry and not by a concurrent write.
                    if not self._verify_polib_builds(node_id, verbose):
                        store.remove(node_id)
                        raise PolibSaveError(f"Node '{node_id}': entry broke Polib.lean build, rolled back")
                with self._save_lock:
                    self._dep_graph.record_edges(entry.node_id, lean_code, parsed)
                    self._dep_graph.save()
                self._session.mark_done(node_id, entry.status)
                try:
                    from visualizer.generate import generate_explorer
                    generate_explorer(
                        Path(self._config.store_path),
                        Path(self._config.polib_path) / "proof_explorer.html",
                    )
                except Exception:
                    pass
                self._log(verbose, f"  [saved] {node_id} → polib ({entry.status})")
                with self._run_codes_lock:
                    self._run_codes[node_id] = lean_code
                if self._flog:
                    self._flog.finish_node(node_id, entry.status, sorry_count=0)
                return entry.status
            except PolibSaveError as exc:
                self._log(verbose, f"  [save-err] {node_id}: {exc} — failing node")
                self._session.mark_pending(node_id, self._config.max_rounds_per_node, str(exc))
                if self._flog:
                    self._flog.finish_node(node_id, "failed", sorry_count=report.sorry_count)
                return "pending"

        elif compile_ok and report.sorry_count > 0:
            # Code compiled but still has sorry — reject as failure (no new sorry accepted)
            last_err_msg = f"compiled with {report.sorry_count} sorry(s) — sorry not accepted"
            self._log(verbose, f"  [sorry-reject] {node_id} — {report.sorry_count} sorry(s), failing node")
            self._session.mark_pending(node_id, self._config.max_rounds_per_node, last_err_msg, failed_code=lean_code)
            if self._flog:
                self._flog.finish_node(node_id, "failed", sorry_count=report.sorry_count)
            return "pending"

        else:
            last_err_msg = last_errors[0].raw_message[:120] if last_errors else "compile failed"
            self._session.mark_pending(node_id, self._config.max_rounds_per_node, last_err_msg, failed_code=lean_code)
            self._log(verbose, f"  [fail] {node_id} — saved to output/ for inspection")
            if self._flog:
                self._flog.finish_node(node_id, "failed", sorry_count=report.sorry_count)
            return "pending"
