"""
Thin wrapper around the `claude-agent-sdk` Python package.

The subprocess `claude -p` path returns 403 inside pipeline runs even when the
same command works in a shell (verified 2026-06-18). Switching to the SDK's
in-process `query()` resolved it. Keeps the same `_call` / `.messages.create`
interface so tool classes need no changes.
"""
from __future__ import annotations

import asyncio
import os
import random
import threading
import time
from dataclasses import dataclass
from typing import Any

from pathlib import Path as _Path

from claude_agent_sdk import (
    AssistantMessage,
    ClaudeAgentOptions,
    ResultMessage,
    TextBlock,
    query,
)


# Limits concurrent in-flight SDK queries across all threads. Holds back the
# burst that otherwise builds up when multiple search tracks all hit the LLM
# at once.
_CLAUDE_SDK_SEM: threading.Semaphore = threading.Semaphore(3)

# Read-only tools the prover lets every Claude call use autonomously.
# Read / Grep / Glob give the LLM the ability to explore Polib.lean,
# Inventory.lean, and the Mathlib source tree (under
# polib/.lake/packages/mathlib/) so it can verify lemma names and discover
# applicable lemmas instead of guessing from a pre-baked hint list.
# Bash etc. are intentionally NOT here — we want exploration, not execution.
_TOOL_ALLOWLIST: list[str] = ["Read", "Grep", "Glob"]

# Project root inferred from this file's location (agent/claude_sdk.py →
# repo root is two parents up). The SDK subprocess is launched with this as
# cwd so relative paths in Read/Grep/Glob calls resolve predictably.
_PROJECT_ROOT: _Path = _Path(__file__).resolve().parent.parent


@dataclass
class _ContentBlock:
    text: str
    type: str = "text"


@dataclass
class _Response:
    content: list[_ContentBlock]
    stop_reason: str = "end_turn"


class _MessagesNamespace:
    def __init__(self, client: "ClaudeSDKClient"):
        self._client = client

    def create(
        self,
        model: str,
        max_tokens: int,
        messages: list[dict],
        system: str = "",
        **_kwargs: Any,
    ) -> _Response:
        """Sync façade over ``ClaudeSDKClient._call``.

        Extra kwargs forwarded to ``_call`` when present:
        * ``effort`` — caller-controlled thinking depth.  JSON-schema tasks
          (goal extraction, blueprint decomposition) should pass ``"low"``
          to disable extended thinking and avoid 60-180s thinking phases
          on prompts that don't need them.
        * ``timeout`` — per-call timeout override.
        * ``allowed_tools`` — list of tools the LLM may call.  Pass ``[]``
          for pure JSON / signature output tasks: leaving the default
          (Read/Grep/Glob) tempts the LLM into "let me double-check by
          grepping…" detours that add 30-120s per call.
        """
        prompt_parts: list[str] = []
        if system:
            prompt_parts.append(f"[System]\n{system}\n")
        for msg in messages:
            role = msg.get("role", "user")
            content = msg.get("content", "")
            if isinstance(content, list):
                content = "\n".join(
                    b.get("text", "") if isinstance(b, dict) else str(b)
                    for b in content
                )
            prompt_parts.append(f"[{role.capitalize()}]\n{content}")

        prompt = "\n\n".join(prompt_parts)
        text = self._client._call(
            prompt,
            model=model,
            timeout=_kwargs.get("timeout"),
            effort=_kwargs.get("effort"),
            allowed_tools=_kwargs.get("allowed_tools"),
        )
        return _Response(content=[_ContentBlock(text=text)])


class ClaudeSDKClient:
    """Wraps `claude_agent_sdk.query` so the rest of the codebase stays sync."""

    def __init__(self, model: str = "claude-sonnet-4-6", claude_bin: str = "claude"):
        self.model = model
        self._bin = claude_bin  # accepted for back-compat; SDK resolves its own CLI
        self.messages = _MessagesNamespace(self)

    @staticmethod
    def _trim_prompt(prompt: str, attempt: int) -> str:
        """Strip expensive sections from the prompt on retries to reduce latency."""
        if attempt == 0:
            return prompt

        if attempt == 1:
            for header in ("## Reference Lean 4 formalizations from GitHub",
                           "## Reference Lean 4 Formalizations from GitHub"):
                start = prompt.find(f"\n{header}")
                if start != -1:
                    next_section = prompt.find("\n##", start + 1)
                    if next_section != -1:
                        prompt = prompt[:start] + prompt[next_section:]
                    else:
                        prompt = prompt[:start]
            for header in ("## Shared module content", "## Shared Module Content"):
                start = prompt.find(f"\n{header}")
                if start != -1:
                    next_section = prompt.find("\n##", start + 1)
                    if next_section != -1:
                        prompt = prompt[:start] + prompt[next_section:]
                    else:
                        prompt = prompt[:start]
            return prompt

        keep_headers = (
            "## Node",
            "## Description",
            "## Lean signature",
            "## Dependencies",
            "## Mathlib",
            "## Required",
        )
        lines = prompt.splitlines(keepends=True)
        kept: list[str] = []
        inside_kept = True
        for line in lines:
            if line.startswith("## "):
                inside_kept = any(line.startswith(h) for h in keep_headers)
            if inside_kept:
                kept.append(line)
        return "".join(kept) or prompt

    async def _query_once(
        self,
        prompt: str,
        model: str,
        system: str | None,
        effort: str | None,
        stop_event: threading.Event | None,
        max_turns: int = 20,
        allowed_tools: list[str] | None = None,
    ) -> str:
        opts_kwargs: dict[str, Any] = {
            "model": model,
            # `max_turns` is now ADAPTIVE per attempt — see _call's
            # `_ESCALATION_SCHEDULE`. Default 20 if called directly.
            "max_turns": max_turns,
            # Read-only tool access lets the LLM verify lemma names against
            # the real Polib / Inventory / Mathlib sources before using them.
            # Caller can pass `allowed_tools=[]` to disable tools entirely
            # (used by JSON-output tasks like decomposer / goal extractor —
            # they don't need to grep, and tool-access tempts costly detours).
            "allowed_tools": allowed_tools if allowed_tools is not None else _TOOL_ALLOWLIST,
            # Auto-approve tool use. The allowlist is already restrictive
            # (read-only); without bypass the SDK would block at the first
            # tool call waiting for human approval.
            "permission_mode": "bypassPermissions",
            # cwd anchors relative paths inside the tools.
            "cwd": str(_PROJECT_ROOT),
        }
        if system:
            opts_kwargs["system_prompt"] = system
        if effort:
            opts_kwargs["effort"] = effort
        # Neutralize env markers that tell the bundled CLI "you're inside a
        # parent Claude Code session". When the pipeline runs inside a
        # VSCode Claude Code session those markers point at a session id this
        # subprocess can't attach to, and the CLI exits with
        # is_error=True / subtype="success" (`Claude Code returned an error
        # result: success`). The SDK uses `_bundled/claude` directly so the
        # ~/.local/bin/claude wrapper's unset list doesn't run — must do it
        # here. CRITICAL: the SDK does
        #   process_env = {**os.environ, **options.env, ...}
        # in subprocess_cli.py — merely OMITTING these keys from options.env
        # leaves the inherited values in process_env. Must OVERWRITE with
        # empty strings so the merge overrides inherited values. The bundled
        # CLI treats empty string as absent for these markers.
        # CLAUDE_EFFORT is also blanked so explicit per-call effort wins over
        # an inherited CLAUDE_EFFORT=xhigh from the parent harness.
        # CRITICAL: do NOT blank CLAUDE_CODE_ENTRYPOINT / CLAUDE_AGENT_SDK_VERSION.
        # The SDK sets CLAUDE_CODE_ENTRYPOINT="sdk-py" *before* `**options.env`
        # in subprocess_cli.py; blanking it from our side overwrites "sdk-py" to
        # empty and the bundled CLI silently switches to interactive/OAuth mode,
        # then tries to attach to whatever session id is around → is_error=True,
        # subtype=success. Only blank the session-attach markers.
        opts_kwargs["env"] = {
            **os.environ,
            "CLAUDE_EFFORT": "",
            "CLAUDECODE": "",
            "CLAUDE_CODE_SESSION_ID": "",
            "CLAUDE_CODE_EXECPATH": "",
            "CLAUDE_CODE_ENABLE_SDK_FILE_CHECKPOINTING": "",
            "CLAUDE_CODE_SSE_PORT": "",  # VSCode IPC port pointing at a dead session
            "AI_AGENT": "",
        }
        options = ClaudeAgentOptions(**opts_kwargs)

        text_parts: list[str] = []
        result: ResultMessage | None = None

        # Explicit aclose on the async generator. Without it, when
        # asyncio.wait_for cancels this coroutine on timeout, the `async for`
        # exits via CancelledError but the query() generator is NOT
        # auto-closed (PEP 533 was deferred; the SDK's own client.py:76-83
        # notes the same trap). Its `finally: await query.close()` then runs
        # only via asyncgen GC during loop shutdown, by which point the
        # subprocess termination await can be dropped and CLI children
        # accumulate — making the *next* asyncio.run pay spawn/socket cost
        # and the round time out at 180s again. Explicit aclose forces the
        # SDK's transport.close() (SIGTERM → SIGKILL with 5s+5s grace) to
        # run synchronously inside this loop while it's still alive.
        gen = query(prompt=prompt, options=options)
        try:
            async for msg in gen:
                if stop_event is not None and stop_event.is_set():
                    raise RuntimeError("call aborted: stop_event set")
                if isinstance(msg, AssistantMessage):
                    for block in msg.content:
                        if isinstance(block, TextBlock):
                            text_parts.append(block.text)
                elif isinstance(msg, ResultMessage):
                    result = msg
        finally:
            try:
                await gen.aclose()
            except Exception:
                pass

        if result is None:
            raise RuntimeError("claude SDK returned no ResultMessage")
        if result.is_error:
            raise RuntimeError(
                f"claude SDK error: subtype={result.subtype} "
                f"stop_reason={result.stop_reason}"
            )
        return "".join(text_parts)

    # ───────────────────────────────────────────────────────────────
    # Adaptive escalation schedule for (effort, max_turns) across retry attempts.
    # Sonnet 4.6 with extended thinking can fragment a single logical proof
    # generation across many "assistant turns" — observed up to 5+ on complex
    # Lean fixes. Starting tight (e.g. max_turns=5) too often blocks valid
    # in-progress fixes; starting loose (max_turns=35) wastes wallclock on
    # trivial swaps. Empirical sweet spot: start moderate, escalate ONLY when
    # the previous attempt actually saturated the turn budget (Change 1,
    # 2026-06-29 post-mortem).
    #
    # Each tuple = (effort, max_turns). `effort` controls extended-thinking
    # depth; "medium" thinks for seconds, "high" thinks for ~minute, "xhigh"
    # for several minutes.
    # Re-tiered (2026-06-29 evening, post c104_rerun16 timeout audit): the
    # always-high flattening — adopted for bundled-CLI cold-start tolerance —
    # over-corrected. In practice cold-start failures fail FAST (RuntimeError
    # "no ResultMessage" within seconds), while genuine effort=high+35-turns
    # Sonnet calls on the large _generate_lean sandwich prompt routinely
    # exceed 300s, burning 18 min wallclock per node across 3 retries even
    # when the underlying proof is small. Restored tiered schedule:
    #   attempt 0: medium-20 — covers the majority of sub-lemma proofs in
    #              ~60-120s when L2.B has supplied a locked sub-signature
    #              (no signature drift to fix, no big surface area to think
    #              about).
    #   attempt 1: high-35 — escalation when medium hit max_turns OR timeout.
    #   attempt 2: high-35 — final retry at warm CLI.
    # If attempt 0 completes, total wallclock per node drops 3-5x compared
    # to always-high. If it doesn't, we still get one full high-effort try.
    # Each tool call costs 2 assistant turns (the call itself + reading the
    # result). With Read/Grep/Glob now in the allowlist, the LLM can easily
    # use 5-10 tool calls per proof attempt → 10-20 turns just for tool use,
    # on top of the actual reasoning. The schedule is bumped accordingly.
    _ESCALATION_SCHEDULE: list[tuple[str, int]] = [
        ("medium", 40),
        ("high", 60),
        ("high", 60),
    ]

    @staticmethod
    def _is_max_turns_error(exc: Exception) -> bool:
        """Detect the bundled CLI's `Reached maximum number of turns (N)` error.
        This is the ONLY error class that triggers escalation — other errors
        (timeout, API failure) get normal backoff retry without scaling budget.
        """
        msg = str(exc)
        return "Reached maximum number of turns" in msg

    def _call(self, prompt: str, model: str | None = None, timeout: int | None = None,
              fast_model: str | None = None, system: str | None = None,
              stop_event: threading.Event | None = None, max_attempts: int = 3,
              effort: str | None = None, verbose_escalation: bool = True,
              allowed_tools: list[str] | None = None) -> str:
        """Call the claude SDK with adaptive (effort, max_turns) escalation.

        Behavior:
          - Attempt 0: uses _ESCALATION_SCHEDULE[0] = ("medium", 10).
            80% of calls land here on the cheap path.
          - On `Reached maximum number of turns` error specifically, the
            NEXT attempt steps up to the next entry in the schedule. Other
            errors retry with the SAME schedule entry (just standard backoff).
          - Caller-provided `effort` argument OVERRIDES the schedule
            (preserves backward compat for callers that want explicit control).

        Args:
            timeout: per-attempt timeout, defaults to CLAUDE_TIMEOUT env (150s).
            fast_model: used for attempt 0 only (Haiku tiering for cheap retries).
            stop_event: set to abort the query early.
            max_attempts: retry budget; max(1, max_attempts).
            effort: explicit effort override — if set, the schedule's effort
                    is ignored. Pass to caller-control thinking depth.
            verbose_escalation: log when escalation kicks in (default True).
        """
        if timeout is None:
            timeout = int(os.environ.get("CLAUDE_TIMEOUT", "240"))

        MAX_PROMPT_CHARS = 48_000
        if len(prompt) > MAX_PROMPT_CHARS:
            cutoff = prompt.rfind("\n##", 0, MAX_PROMPT_CHARS)
            if cutoff == -1:
                cutoff = MAX_PROMPT_CHARS
            prompt = prompt[:cutoff] + "\n\n[prompt truncated to fit token budget]\n"

        _PRE_TRIM_THRESHOLD = 28_000
        if len(prompt) > _PRE_TRIM_THRESHOLD:
            prompt = self._trim_prompt(prompt, attempt=1)

        last_exc: Exception | None = None
        max_attempts = max(1, max_attempts)
        # `schedule_index` advances only when a max_turns error occurred —
        # other errors retry with same budget (just standard backoff). This
        # decouples the escalation tier from the retry counter.
        schedule_index = 0

        for attempt in range(max_attempts):
            if stop_event is not None and stop_event.is_set():
                raise RuntimeError("call aborted: stop_event set")

            attempt_timeout = timeout + 60 * attempt
            trimmed = self._trim_prompt(prompt, attempt)
            effective_model = (
                (fast_model if fast_model and attempt == 0 else None)
                or model
                or self.model
            )

            # Resolve (effort, max_turns) from schedule, allowing caller override
            sched_effort, sched_turns = self._ESCALATION_SCHEDULE[
                min(schedule_index, len(self._ESCALATION_SCHEDULE) - 1)
            ]
            effective_effort = effort or sched_effort
            effective_turns = sched_turns

            # Opt-in diagnostic: print the SDK's _ACTIVE_CHILDREN count before
            # each call.
            if os.environ.get("CLAUDE_SDK_DIAG_CHILDREN") == "1":
                try:
                    from claude_agent_sdk._internal.transport.subprocess_cli import (
                        _ACTIVE_CHILDREN as _children,
                    )
                    print(f"[claude_sdk diag] _ACTIVE_CHILDREN before call: "
                          f"{len(_children)}", flush=True)
                except Exception:
                    pass

            with _CLAUDE_SDK_SEM:
                time.sleep(random.uniform(0, 0.5))
                try:
                    return asyncio.run(
                        asyncio.wait_for(
                            self._query_once(
                                trimmed,
                                model=effective_model,
                                system=system,
                                effort=effective_effort,
                                stop_event=stop_event,
                                max_turns=effective_turns,
                                allowed_tools=allowed_tools,
                            ),
                            timeout=attempt_timeout,
                        )
                    )
                except asyncio.TimeoutError:
                    last_exc = RuntimeError(
                        f"claude SDK timed out after {attempt_timeout}s"
                    )
                except Exception as exc:
                    last_exc = exc

            # Advance schedule index for next attempt (now mostly a no-op
            # since all tiers are identical — kept for log-symmetry and
            # future tunability).
            if last_exc is not None and schedule_index < len(self._ESCALATION_SCHEDULE) - 1:
                old_eff, old_turns = self._ESCALATION_SCHEDULE[schedule_index]
                schedule_index += 1
                if verbose_escalation:
                    next_eff, next_turns = self._ESCALATION_SCHEDULE[schedule_index]
                    # Include the actual error message tail so log readers
                    # can distinguish "timed out" vs "no ResultMessage" vs
                    # "max_turns" vs CLI cold-start race.
                    err_class = ("max_turns" if self._is_max_turns_error(last_exc)
                                 else type(last_exc).__name__)
                    err_msg = str(last_exc)[:140].replace("\n", " ")
                    print(
                        f"[claude_sdk escalate] attempt {attempt} failed "
                        f"({err_class}: \"{err_msg}\"); next try: "
                        f"effort={next_eff}, max_turns={next_turns}",
                        flush=True,
                    )

            if attempt < max_attempts - 1:
                # Error-class-conditional backoff: API rate-limit/timeout
                # errors need real backoff; CLI cold-start RuntimeErrors
                # are transient and benefit from immediate retry (sleeping
                # doesn't help spawn a fresh subprocess any sooner).
                is_max_turns = (last_exc is not None
                                and self._is_max_turns_error(last_exc))
                is_timeout = (last_exc is not None
                              and "timed out" in str(last_exc))
                if is_max_turns or is_timeout:
                    # Genuine resource-bound failure — back off longer
                    backoff = 8 * (attempt + 1) + random.uniform(0, 3)
                else:
                    # Likely transient (CLI race, transient SDK error) —
                    # retry fast. Saves ~25s per node compared to old
                    # 10*(attempt+1) backoff.
                    backoff = 1.5 + random.uniform(0, 1.5)
                time.sleep(backoff)
                continue
            raise last_exc

        raise last_exc or RuntimeError("claude SDK call failed without exception")
