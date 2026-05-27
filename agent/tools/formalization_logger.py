from __future__ import annotations

import json
import threading
from datetime import datetime, timezone
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from agent.tools.lean_compiler import CompileResult


def _now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


class FormalizationLogger:
    """Records every compile attempt and fix round for each formalized node.

    Writes a single JSON file per run to logs/formalization_<run_id>.json.

    Thread-safe: multiple nodes are formalized in parallel.

    JSON schema
    -----------
    {
      "run_id": str,
      "theorem_name": str,
      "started_at": str,
      "finished_at": str | null,
      "nodes": {
        "<node_id>": {
          "node_type": str,
          "description": str,
          "final_status": "proved" | "partial" | "failed" | null,
          "compile_rounds": [
            {
              "round": int,
              "phase": "compile_loop" | "sorry_elim" | "partial_solver",
              "fix_strategy": str,   // what produced this code
              "code": str,
              "compile_success": bool,
              "errors": [{"line", "column", "error_class", "raw_message"}],
              "error_count": int,
              "compile_time_seconds": float,
              "timestamp": str
            }
          ],
          "summary": {
            "total_rounds": int,
            "first_error": str | null,
            "last_error": str | null,
            "sorry_count_final": int
          }
        }
      }
    }
    """

    def __init__(self, log_dir: Path, run_id: str, theorem_name: str) -> None:
        self._log_path = log_dir / f"formalization_{run_id}.json"
        self._lock = threading.Lock()
        self._data: dict = {
            "run_id": run_id,
            "theorem_name": theorem_name,
            "started_at": _now(),
            "finished_at": None,
            "nodes": {},
        }
        log_dir.mkdir(parents=True, exist_ok=True)
        self._flush()

    # ------------------------------------------------------------------
    # Node lifecycle
    # ------------------------------------------------------------------

    def start_node(self, node_id: str, node_type: str, description: str) -> None:
        with self._lock:
            self._data["nodes"][node_id] = {
                "node_type": node_type,
                "description": description,
                "final_status": None,
                "compile_rounds": [],
                "summary": {
                    "total_rounds": 0,
                    "first_error": None,
                    "last_error": None,
                    "sorry_count_final": 0,
                },
            }
            self._flush()

    def finish_node(self, node_id: str, final_status: str, sorry_count: int = 0) -> None:
        with self._lock:
            node = self._data["nodes"].get(node_id)
            if node is None:
                return
            node["final_status"] = final_status
            node["summary"]["sorry_count_final"] = sorry_count
            node["summary"]["total_rounds"] = len(node["compile_rounds"])
            self._flush()

    # ------------------------------------------------------------------
    # Compile-round logging
    # ------------------------------------------------------------------

    def log_compile_round(
        self,
        node_id: str,
        phase: str,
        fix_strategy: str,
        code: str,
        compile_result: "CompileResult",
    ) -> None:
        """Record one compile attempt.

        phase        — "compile_loop" | "sorry_elim" | "partial_solver_elim"
        fix_strategy — what strategy produced this code, e.g.:
                       "initial_generation", "targeted_fix", "targeted_fix_strict",
                       "targeted_fix_decompose", "mechanical_tactic", "sorry_insert",
                       "sorry_elim_parallel", "existing_partial_elim"
        """
        with self._lock:
            node = self._data["nodes"].get(node_id)
            if node is None:
                return

            rounds = node["compile_rounds"]
            round_num = len(rounds)

            errors = [
                {
                    "line": e.line,
                    "column": e.column,
                    "error_class": e.error_class,
                    "raw_message": e.raw_message,
                }
                for e in compile_result.errors
            ]

            first_error_msg = errors[0]["raw_message"] if errors else (
                compile_result.stderr[:200] if compile_result.stderr else None
            )

            entry = {
                "round": round_num,
                "phase": phase,
                "fix_strategy": fix_strategy,
                "code": code,
                "compile_success": compile_result.success,
                "errors": errors,
                "error_count": len(errors),
                "stderr": compile_result.stderr or "",
                "compile_time_seconds": compile_result.compile_time_seconds,
                "timestamp": _now(),
            }
            rounds.append(entry)

            # Update summary
            summary = node["summary"]
            summary["total_rounds"] = len(rounds)
            if not compile_result.success:
                if summary["first_error"] is None and first_error_msg:
                    summary["first_error"] = first_error_msg[:200]
                if first_error_msg:
                    summary["last_error"] = first_error_msg[:200]

            self._flush()

    # ------------------------------------------------------------------
    # Run lifecycle
    # ------------------------------------------------------------------

    def finish_run(self) -> None:
        with self._lock:
            self._data["finished_at"] = _now()
            self._flush()

    def log_path(self) -> Path:
        return self._log_path

    # ------------------------------------------------------------------
    # Internal
    # ------------------------------------------------------------------

    def _flush(self) -> None:
        import uuid as _uuid
        tmp = self._log_path.with_name(self._log_path.stem + f"_{_uuid.uuid4().hex[:8]}.tmp")
        tmp.write_text(json.dumps(self._data, indent=2, ensure_ascii=False), encoding="utf-8")
        tmp.replace(self._log_path)
