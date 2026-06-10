from __future__ import annotations

import re
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path

# Strip ANSI/VT100 escape codes that lake may emit even to pipes.
_ANSI_ESCAPE_RE = re.compile(r'\x1b\[[0-9;]*[A-Za-z]|\x1b\][^\x07]*\x07')


# ── Soundness guard: ban construction of SimplyCon3ConnectedMap instances ────
# The structure is pure data; the geometric axioms (euler_formula, handshake, …)
# are sorried statements that hold only for maps arising from real polytopes.
# Instantiating the structure with arbitrary data and applying an axiom to it
# yields false equations (e.g. v=0,e=0 ⟹ euler_formula gives 0 = 2 → False),
# from which anything is provable. Such proofs compile but are mathematically
# meaningless, so they are rejected before compilation on every code path.
_STRUCT_CONSTRUCTION_PATTERNS: list[tuple[re.Pattern, str]] = [
    (re.compile(r"SimplyCon3ConnectedMap\.mk\b"), "explicit .mk constructor"),
    (re.compile(r":\s*SimplyCon3ConnectedMap\b[^:\n]*:=\s*[{⟨]"), "structure literal with type ascription"),
    (re.compile(r":\s*SimplyCon3ConnectedMap\b[^:=\n]*\bwhere\b"), "`where`-style instance definition"),
    (re.compile(r"⟨[^⟩]*⟩\s*:\s*SimplyCon3ConnectedMap\b"), "anonymous constructor ascribed to the structure type"),
    (re.compile(r"\{[^{}]*\bp_i\s*:=", re.S), "structure literal assigning the p_i field"),
]


def find_struct_construction(lean_code: str) -> str | None:
    """Return a short description + offending snippet if the code constructs a
    SimplyCon3ConnectedMap instance, else None. Comment lines are ignored."""
    stripped = "\n".join(
        line for line in lean_code.splitlines()
        if not line.strip().startswith("--")
    )
    for pat, label in _STRUCT_CONSTRUCTION_PATTERNS:
        m = pat.search(stripped)
        if m:
            snippet = m.group(0).replace("\n", " ")[:120]
            return f"{label}: `{snippet}`"
    return None


@dataclass
class LeanError:
    line: int
    column: int
    error_class: str  # "A"|"B"|"C"|"D"|"E"|"F"
    raw_message: str
    lean_excerpt: str

    def to_dict(self) -> dict:
        return {
            "line": self.line,
            "column": self.column,
            "error_class": self.error_class,
            "raw_message": self.raw_message,
            "lean_excerpt": self.lean_excerpt,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "LeanError":
        return cls(
            line=d["line"],
            column=d["column"],
            error_class=d["error_class"],
            raw_message=d["raw_message"],
            lean_excerpt=d["lean_excerpt"],
        )


@dataclass
class CompileResult:
    success: bool
    exit_code: int
    stdout: str
    stderr: str
    errors: list[LeanError]
    warnings: list[str]
    compile_time_seconds: float
    module_name: str

    def to_dict(self) -> dict:
        return {
            "success": self.success,
            "exit_code": self.exit_code,
            "stdout": self.stdout,
            "stderr": self.stderr,
            "errors": [e.to_dict() for e in self.errors],
            "warnings": self.warnings,
            "compile_time_seconds": self.compile_time_seconds,
            "module_name": self.module_name,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "CompileResult":
        return cls(
            success=d["success"],
            exit_code=d["exit_code"],
            stdout=d["stdout"],
            stderr=d["stderr"],
            errors=[LeanError.from_dict(e) for e in d["errors"]],
            warnings=d["warnings"],
            compile_time_seconds=d["compile_time_seconds"],
            module_name=d["module_name"],
        )


# Error classification rules — applied in order, first match wins.
# Each entry: (class_label, list_of_regex_patterns)
_ERROR_RULES: list[tuple[str, list[str]]] = [
    ("F", [
        r"unknown identifier 'sorry'",
        r"type mismatch.*goal",           # compiler closes a different goal
    ]),
    ("A", [
        r"tactic 'simp' failed",
        r"linarith failed",
        r"\bomega\b.*failed",
        r"ring_nf failed",
        r"norm_num failed",
        r"tactic failed",
    ]),
    ("B", [
        r"type mismatch",
        r"expected type",
        r"application type mismatch",
        r"failed to unify",
    ]),
    ("C", [
        r"unknown identifier",
        r"unknown constant",
        r"declaration uses sorry",
    ]),
    ("D", [
        r"failed to synthesize",
        r"\binstance\b",
        r"\btypeclass\b",
    ]),
    ("E", [
        r"deep recursion",
        r"elaboration timeout",
        r"maximum recursion depth",
    ]),
]

_COMPILED_RULES: list[tuple[str, list[re.Pattern]]] = [
    (cls, [re.compile(p, re.IGNORECASE) for p in patterns])
    for cls, patterns in _ERROR_RULES
]

# Regex to parse error/warning location lines from Lean/lake output.
# lake prefixes with "error: " then the file location, e.g.:
#   error: Polib/_Temp/Foo.lean:4:0: unexpected identifier
# Lean direct output omits the leading "error: ", e.g.:
#   Polib/_Temp/Foo.lean:4:0: error: unknown identifier
_ERROR_LINE_RE = re.compile(
    r"^(?:error:\s+)?(?P<file>[^:\n]+):(?P<line>\d+):(?P<col>\d+):\s+error:\s+(?P<msg>.+)$"
)
_WARNING_LINE_RE = re.compile(
    r"^(?:warning:\s+)?(?P<file>[^:\n]+):(?P<line>\d+):(?P<col>\d+):\s+warning:\s+(?P<msg>.+)$"
)

# Linter warnings that must be fixed (not just noted). Maps regex → human hint.
_FIXABLE_WARNINGS: list[tuple[re.Pattern, str]] = [
    (re.compile(r"unused variable", re.IGNORECASE),
     "unused variable — prefix parameter name with `_` e.g. `(_h : T)` instead of `(h : T)`"),
    (re.compile(r"tactic does nothing", re.IGNORECASE),
     "unnecessary tactic — remove it (e.g. `push_cast` before `ring` when ring works alone)"),
    (re.compile(r"remove line break", re.IGNORECASE),
     "style: remove the line break inside the theorem/lemma signature"),
]


class ErrorClassifier:
    @staticmethod
    def classify(raw_error: str, line: int = 0, col: int = 0) -> LeanError:
        for error_class, patterns in _COMPILED_RULES:
            for pattern in patterns:
                if pattern.search(raw_error):
                    return LeanError(
                        line=line,
                        column=col,
                        error_class=error_class,
                        raw_message=raw_error,
                        lean_excerpt="",
                    )
        # Default: class A (generic tactic failure)
        return LeanError(
            line=line,
            column=col,
            error_class="A",
            raw_message=raw_error,
            lean_excerpt="",
        )


def _sanitize_module_name(raw: str) -> str:
    """Allow only alphanumeric and underscores to prevent path traversal."""
    sanitized = re.sub(r"[^A-Za-z0-9_]", "_", raw)
    # Lean module names must start with a letter
    if sanitized and not sanitized[0].isalpha():
        sanitized = "M_" + sanitized
    return sanitized or "Module"


class LeanCompiler:
    def __init__(self, workspace: Path, timeout: int = 120, keep_on_failure: bool = False, lake_binary: str = "lake"):
        self._workspace = Path(workspace)
        self._timeout = timeout
        self._keep_on_failure = keep_on_failure
        self._lake_binary = lake_binary

    def compile(self, lean_code: str, module_name: str) -> CompileResult:
        safe_name = _sanitize_module_name(module_name)

        # Soundness guard — reject before compiling so every code path
        # (generation, all fix strategies, sorry elimination) is covered.
        offending = find_struct_construction(lean_code)
        if offending:
            guard_error = LeanError(
                line=0, column=0, error_class="X",
                raw_message=(
                    "BANNED CONSTRUCT — proof builds a SimplyCon3ConnectedMap instance "
                    f"({offending}). The geometric axioms hold only for the `maps` "
                    "parameter given in the theorem signature; applying them to a "
                    "fabricated instance is unsound. Remove the instance construction "
                    "and work only with the given `maps`."
                ),
                lean_excerpt=offending,
            )
            return CompileResult(
                success=False, exit_code=-2, stdout="",
                stderr="soundness guard: banned instance construction",
                errors=[guard_error], warnings=[],
                compile_time_seconds=0.0, module_name=safe_name,
            )
        temp_dir = self._workspace / "Polib" / "_Temp"
        temp_dir.mkdir(parents=True, exist_ok=True)
        temp_file = temp_dir / f"{safe_name}.lean"

        # Lean source files are intentionally kept so Lake can use content-based
        # caching: if the same code is submitted again, Lake skips re-elaboration.
        temp_file.write_text(lean_code, encoding="utf-8")
        start = time.monotonic()
        try:
            result = subprocess.run(
                [self._lake_binary, "build", f"Polib._Temp.{safe_name}"],
                cwd=self._workspace,
                capture_output=True,
                text=True,
                timeout=self._timeout,
            )
        except subprocess.TimeoutExpired:
            elapsed = time.monotonic() - start
            timeout_error = LeanError(
                line=0, column=0, error_class="E",
                raw_message="elaboration timeout: lake build exceeded time limit",
                lean_excerpt="",
            )
            return CompileResult(
                success=False,
                exit_code=-1,
                stdout="",
                stderr="Timeout",
                errors=[timeout_error],
                warnings=[],
                compile_time_seconds=elapsed,
                module_name=safe_name,
            )
        elapsed = time.monotonic() - start

        combined_output = _ANSI_ESCAPE_RE.sub(
            "", result.stdout + "\n" + result.stderr
        )
        errors = self._parse_errors(combined_output, lean_code, safe_name)
        warnings = self._parse_warnings(combined_output, safe_name)

        # Convert fixable linter warnings into errors so the fix loop addresses them.
        lean_lines = lean_code.splitlines()
        for line_text in combined_output.splitlines():
            m = _WARNING_LINE_RE.match(line_text.strip())
            if not m:
                continue
            file_path = m.group("file")
            if safe_name not in file_path and "_Temp" not in file_path:
                continue
            msg = m.group("msg")
            for pattern, hint in _FIXABLE_WARNINGS:
                if pattern.search(msg):
                    ln = int(m.group("line"))
                    col = int(m.group("col"))
                    excerpt = lean_lines[ln - 1] if 0 < ln <= len(lean_lines) else ""
                    errors.append(LeanError(
                        line=ln, column=col, error_class="A",
                        raw_message=f"[linter warning] {hint}",
                        lean_excerpt=excerpt,
                    ))
                    break

        # If build failed but no structured errors were parsed, do a second
        # looser scan before falling back to a raw dump.
        if result.returncode != 0 and not errors:
            errors = self._loose_parse_errors(combined_output, lean_code, safe_name)

        # Final fallback: include the full combined output so the LLM can
        # see what went wrong instead of just "error: build failed".
        if result.returncode != 0 and not errors:
            raw = combined_output.strip()[:5000] or "unknown build failure"
            errors = [LeanError(
                line=0, column=0, error_class="A",
                raw_message=raw,
                lean_excerpt="",
            )]

        success = result.returncode == 0 and len(errors) == 0
        return CompileResult(
            success=success,
            exit_code=result.returncode,
            stdout=result.stdout,
            stderr=result.stderr,
            errors=errors,
            warnings=warnings,
            compile_time_seconds=elapsed,
            module_name=safe_name,
        )

    def _parse_errors(self, stderr: str, lean_code: str, module_name: str) -> list[LeanError]:
        """Parse errors, filtering to only those from the compiled temp file."""
        lean_lines = lean_code.splitlines()
        errors: list[LeanError] = []
        seen: set[tuple] = set()  # (line, col, msg) dedup
        for line_text in stderr.splitlines():
            m = _ERROR_LINE_RE.match(line_text.strip())
            if m:
                # Only include errors from our temp file, not from Mathlib/lake itself
                file_path = m.group("file")
                if module_name not in file_path and "_Temp" not in file_path:
                    continue
                ln = int(m.group("line"))
                col = int(m.group("col"))
                msg = m.group("msg")
                key = (ln, col, msg[:80])
                if key in seen:
                    continue
                seen.add(key)
                excerpt = lean_lines[ln - 1] if 0 < ln <= len(lean_lines) else ""
                error = ErrorClassifier.classify(msg, line=ln, col=col)
                error.lean_excerpt = excerpt
                errors.append(error)
        return errors

    def _loose_parse_errors(
        self, text: str, lean_code: str, module_name: str
    ) -> list[LeanError]:
        """Second-pass parser for error lines that don't fit the strict format.

        Handles cases where lake omits the inner 'error:' keyword, uses a
        different path prefix, or wraps the message across lines.
        """
        lean_lines = lean_code.splitlines()
        errors: list[LeanError] = []
        seen: set[tuple] = set()

        # Looser pattern: file:line:col: <anything> — no requirement for 'error:' keyword.
        _LOOSE_RE = re.compile(
            r"^(?:error:\s+)?(?P<file>[^:\n]+):(?P<line>\d+):(?P<col>\d+):\s+(?P<msg>.+)$"
        )

        for line_text in text.splitlines():
            stripped = line_text.strip()
            # Skip the generic lake summary lines — these carry no location info.
            if stripped in (
                "error: build failed",
                "Build completed with errors.",
                "error: build failed\n",
            ):
                continue
            m = _LOOSE_RE.match(stripped)
            if not m:
                continue
            file_path = m.group("file")
            if module_name not in file_path and "_Temp" not in file_path:
                continue
            msg = m.group("msg")
            # Skip lines that are just "warning: ..." continuations without context
            if msg.startswith("warning:"):
                continue
            ln = int(m.group("line"))
            col = int(m.group("col"))
            key = (ln, col, msg[:80])
            if key in seen:
                continue
            seen.add(key)
            excerpt = lean_lines[ln - 1] if 0 < ln <= len(lean_lines) else ""
            error = ErrorClassifier.classify(msg, line=ln, col=col)
            error.lean_excerpt = excerpt
            errors.append(error)
        return errors

    def _parse_warnings(self, stderr: str, module_name: str) -> list[str]:
        warnings: list[str] = []
        for line_text in stderr.splitlines():
            m = _WARNING_LINE_RE.match(line_text.strip())
            if m:
                file_path = m.group("file")
                if module_name not in file_path and "_Temp" not in file_path:
                    continue
                warnings.append(m.group("msg"))
        return warnings
