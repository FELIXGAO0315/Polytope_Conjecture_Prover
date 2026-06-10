"""
Thin wrapper around the `claude` CLI binary (Claude Code SDK).
Provides a .messages.create()-compatible interface so tool classes need
minimal changes, while avoiding any ANTHROPIC_API_KEY requirement.
"""
from __future__ import annotations

import json
import os
import random
import signal
import subprocess
import threading
import time
from dataclasses import dataclass
from typing import Any

# Global semaphore: limit concurrent `claude` CLI subprocesses across ALL threads.
# Running too many simultaneously causes session-file conflicts → "claude CLI exited 1".
# 4 concurrent calls gives meaningful parallelism without overloading the CLI.
_CLAUDE_CLI_SEM: threading.Semaphore = threading.Semaphore(3)


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
        # Build a single prompt string from the messages list.
        # For simple user/assistant turns we just take the last user message.
        prompt_parts: list[str] = []
        if system:
            prompt_parts.append(f"[System]\n{system}\n")
        for msg in messages:
            role = msg.get("role", "user")
            content = msg.get("content", "")
            if isinstance(content, list):
                # Content blocks
                content = "\n".join(
                    b.get("text", "") if isinstance(b, dict) else str(b)
                    for b in content
                )
            prompt_parts.append(f"[{role.capitalize()}]\n{content}")

        prompt = "\n\n".join(prompt_parts)
        timeout = _kwargs.get("timeout")
        text = self._client._call(prompt, model=model, timeout=timeout)
        return _Response(content=[_ContentBlock(text=text)])


class ClaudeSDKClient:
    """Calls `claude -p <prompt> --output-format json` for every LLM request."""

    def __init__(self, model: str = "claude-sonnet-4-6", claude_bin: str = "claude"):
        self.model = model
        self._bin = claude_bin
        self.messages = _MessagesNamespace(self)

    @staticmethod
    def _trim_prompt(prompt: str, attempt: int) -> str:
        """Strip expensive sections from the prompt on retries to reduce latency."""
        if attempt == 0:
            return prompt

        if attempt == 1:
            # Drop the GitHub reference formalizations section
            for header in ("## Reference Lean 4 formalizations from GitHub",
                           "## Reference Lean 4 Formalizations from GitHub"):
                start = prompt.find(f"\n{header}")
                if start != -1:
                    next_section = prompt.find("\n##", start + 1)
                    if next_section != -1:
                        prompt = prompt[:start] + prompt[next_section:]
                    else:
                        prompt = prompt[:start]
            # Drop the shared module content block
            for header in ("## Shared module content", "## Shared Module Content"):
                start = prompt.find(f"\n{header}")
                if start != -1:
                    next_section = prompt.find("\n##", start + 1)
                    if next_section != -1:
                        prompt = prompt[:start] + prompt[next_section:]
                    else:
                        prompt = prompt[:start]
            return prompt

        # attempt >= 2: keep only the minimal essential sections
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
        inside_kept = True  # keep preamble before first ##
        for line in lines:
            if line.startswith("## "):
                inside_kept = any(line.startswith(h) for h in keep_headers)
            if inside_kept:
                kept.append(line)
        return "".join(kept) or prompt

    def _call(self, prompt: str, model: str | None = None, timeout: int | None = None,
              fast_model: str | None = None, system: str | None = None,
              stop_event: threading.Event | None = None) -> str:
        """Call the claude CLI binary.

        timeout defaults to the CLAUDE_TIMEOUT env var (default 240s).
        Pass timeout explicitly to override per-call.
        fast_model: if provided, used for attempt 0 only; attempts 1+ use the main model.
        stop_event: if set, kills the subprocess immediately so the call can return fast.
        """
        if timeout is None:
            timeout = int(os.environ.get("CLAUDE_TIMEOUT", "150"))

        # Hard prompt length cap to keep CLI response time bounded.
        # Set high enough that sorry-elim full-file prompts (often 40K+) are not truncated.
        MAX_PROMPT_CHARS = 48_000
        if len(prompt) > MAX_PROMPT_CHARS:
            cutoff = prompt.rfind("\n##", 0, MAX_PROMPT_CHARS)
            if cutoff == -1:
                cutoff = MAX_PROMPT_CHARS
            prompt = prompt[:cutoff] + "\n\n[prompt truncated to fit token budget]\n"

        # Pre-trim large prompts even on attempt 0 to reduce inference latency.
        _PRE_TRIM_THRESHOLD = 28_000
        if len(prompt) > _PRE_TRIM_THRESHOLD:
            prompt = self._trim_prompt(prompt, attempt=1)

        last_exc: Exception | None = None
        stdout, stderr = "", ""
        for attempt in range(3):
            # Abort immediately if stop_event was already set before we start
            if stop_event is not None and stop_event.is_set():
                raise RuntimeError("call aborted: stop_event set")

            # Scale attempt timeouts from the caller-supplied timeout.
            # Retries get MORE time, not less — if attempt 0 timed out, retrying
            # with a smaller budget is guaranteed to fail again. The prompt is
            # also trimmed harder on retries, so time↑ + prompt↓ gives the retry
            # a real chance.
            attempt_timeout = timeout + 60 * attempt
            trimmed = self._trim_prompt(prompt, attempt)
            # Attempt 0 uses fast_model (haiku) when provided; later attempts escalate to main model.
            effective_model = (fast_model if fast_model and attempt == 0 else None) or model or self.model
            attempt_cmd = [self._bin, "-p", trimmed, "--output-format", "json", "--model", effective_model, "--tools", ""]
            if system:
                attempt_cmd += ["--system-prompt", system]
            # Acquire global semaphore before launching subprocess.
            # Prevents session-file races when many threads call the claude CLI in parallel.
            with _CLAUDE_CLI_SEM:
                # Small jitter so all workers don't hammer the CLI at exactly the same time.
                time.sleep(random.uniform(0, 0.5))
                try:
                    # Use Popen + setsid so we can kill the whole process group on timeout.
                    proc = subprocess.Popen(
                        attempt_cmd,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                        text=True,
                        preexec_fn=os.setsid,
                    )

                    # Watchdog: if stop_event fires, kill the subprocess immediately.
                    def _kill_on_stop(p=proc):
                        if stop_event is not None:
                            stop_event.wait()
                            try:
                                os.killpg(os.getpgid(p.pid), signal.SIGKILL)
                            except Exception:
                                pass

                    _watchdog: threading.Thread | None = None
                    if stop_event is not None:
                        _watchdog = threading.Thread(target=_kill_on_stop, daemon=True)
                        _watchdog.start()

                    try:
                        stdout, stderr = proc.communicate(timeout=attempt_timeout)
                    finally:
                        if _watchdog is not None:
                            _watchdog.join(timeout=1)

                except subprocess.TimeoutExpired:
                    try:
                        os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    # Drain pipes before wait() to avoid pipe-buffer deadlock,
                    # then enforce a hard 10s wait timeout as final safety net.
                    try:
                        _out, _err = proc.communicate(timeout=10)
                    except (subprocess.TimeoutExpired, Exception):
                        pass
                    try:
                        proc.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        pass
                    last_exc = RuntimeError(f"claude CLI timed out after {attempt_timeout}s")
                    if attempt < 2:
                        time.sleep(10 * (attempt + 1) + random.uniform(0, 5))
                        continue
                    raise last_exc

                # stop_event killed the process — abort without retrying
                if stop_event is not None and stop_event.is_set():
                    raise RuntimeError("call aborted: stop_event set")

                # Retry on non-zero exit code (transient errors: rate limit, OOM, etc.)
                if proc.returncode != 0:
                    last_exc = RuntimeError(
                        f"claude CLI exited {proc.returncode}:\n{stderr[:500]}"
                    )
                    if attempt < 2:
                        time.sleep(10 * (attempt + 1) + random.uniform(0, 5))
                        continue
                    raise last_exc
            break  # success

        if proc.returncode != 0:
            raise RuntimeError(
                f"claude CLI exited {proc.returncode}:\n{stderr[:500]}"
            )

        try:
            data = json.loads(stdout)
        except json.JSONDecodeError as exc:
            raise RuntimeError(
                f"claude CLI returned non-JSON: {stdout[:300]}"
            ) from exc

        if data.get("is_error") or data.get("subtype") != "success":
            raise RuntimeError(f"claude CLI error response: {data}")

        return data["result"]
