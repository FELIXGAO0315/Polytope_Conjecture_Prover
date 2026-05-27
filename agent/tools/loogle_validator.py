"""Validates Mathlib lemma names against the Loogle search API.

Filters hint lists to remove hallucinated names before they reach prompts,
reducing wasted compile rounds caused by references to non-existent lemmas.
"""
from __future__ import annotations

import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.request import urlopen, Request
from urllib.error import URLError
import json

_cache: dict[str, bool] = {}
_cache_lock = threading.Lock()


class LoogleValidator:
    def __init__(self, timeout: int = 8, max_batch: int = 20) -> None:
        self._timeout = timeout
        self._max_batch = max_batch

    @staticmethod
    def _looks_like_lemma_name(hint: str) -> bool:
        """Return True if the hint string looks like a qualified lemma name.

        We only validate names that are either qualified (contain ".") or start
        with an uppercase letter (Lean 4 theorem naming convention).  Plain
        tactics like `omega`, `simp`, `linarith` are left through unconditionally.
        """
        # Strip leading "- " list markers and everything after the first space/colon
        name = hint.strip().lstrip("-").strip().split()[0].split(":")[0]
        return "." in name or (bool(name) and name[0].isupper())

    def _check_one(self, hint: str) -> tuple[str, bool]:
        """Query Loogle for a single lemma name. Returns (hint, exists)."""
        name = hint.strip().lstrip("-").strip().split()[0].split(":")[0]
        with _cache_lock:
            if name in _cache:
                return hint, _cache[name]

        url = f"https://loogle.lean-lang.org/json?q=name:{name}"
        try:
            req = Request(url, headers={"User-Agent": "loogle-validator/1.0"})
            with urlopen(req, timeout=self._timeout) as resp:
                data = json.loads(resp.read().decode())
            # A hit is valid only when the returned hits contain an exact name match
            hits = data.get("hits") or []
            exists = any(h.get("name") == name for h in hits)
        except (URLError, OSError, json.JSONDecodeError, Exception):
            # Network/timeout → keep the hint (fail open)
            with _cache_lock:
                _cache[name] = True
            return hint, True

        with _cache_lock:
            _cache[name] = exists
        return hint, exists

    def filter_existing(self, hints: list[str]) -> list[str]:
        """Return hints with non-existent Mathlib lemma names removed.

        Hints that don't look like qualified names (plain tactics, prose) pass
        through without a network round-trip. Any network error keeps the hint.
        """
        to_validate = [h for h in hints if self._looks_like_lemma_name(h)]
        skip = [h for h in hints if not self._looks_like_lemma_name(h)]

        if not to_validate:
            return hints

        # Batch to avoid hammering the API
        batch = to_validate[: self._max_batch]
        skipped_tail = to_validate[self._max_batch :]

        results: dict[str, bool] = {}
        with ThreadPoolExecutor(max_workers=5) as pool:
            futures = {pool.submit(self._check_one, h): h for h in batch}
            for future in as_completed(futures):
                try:
                    hint, exists = future.result()
                    results[hint] = exists
                except Exception:
                    results[futures[future]] = True  # fail open

        validated = [h for h in batch if results.get(h, True)]
        return skip + validated + skipped_tail

    def search_by_fragment(self, fragment: str, max_results: int = 5) -> list[str]:
        """Search Loogle for Mathlib lemma names containing `fragment`.

        Uses the `name:X` query which returns lemmas whose fully-qualified name
        includes X as a substring. Useful for finding the real name when Lean
        rejected a hallucinated identifier — e.g. fragment='sum_Ico' finds
        'Finset.sum_Ico_consecutive'.
        """
        url = f"https://loogle.lean-lang.org/json?q=name:{fragment}"
        try:
            req = Request(url, headers={"User-Agent": "loogle-validator/1.0"})
            with urlopen(req, timeout=self._timeout) as resp:
                data = json.loads(resp.read().decode())
            hits = data.get("hits") or []
            return [h["name"] for h in hits[:max_results] if "name" in h]
        except Exception:
            return []
