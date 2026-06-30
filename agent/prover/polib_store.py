from __future__ import annotations

import threading
from contextlib import contextmanager
from pathlib import Path
from typing import ClassVar

from agent.prover.tools.polib_manager import PolibManager


class PolibStore:
    """Thread-safe Polib.lean reader + transaction-scoped writer.

    Owns the per-path transaction lock and the in-memory content cache.
    Delegates low-level file mutation to a wrapped :class:`PolibManager`.

    A "transaction" is any sequence that must be atomic with respect to
    parallel worker threads — typically save → verify-build → rollback.
    On exit the cache is unconditionally invalidated so any reader after
    the transaction re-reads the file.
    """

    _locks: ClassVar[dict[str, threading.Lock]] = {}
    _locks_meta: ClassVar[threading.Lock] = threading.Lock()
    _cache: ClassVar[dict[str, str]] = {}
    _cache_lock: ClassVar[threading.Lock] = threading.Lock()

    def __init__(self, manager: PolibManager) -> None:
        self._mgr = manager
        self._lean_path: Path = manager._polib_lean
        self._key = str(self._lean_path.resolve())

    @property
    def lean_path(self) -> Path:
        return self._lean_path

    @property
    def manager(self) -> PolibManager:
        return self._mgr

    # ------------------------------------------------------------------
    # Cached read
    # ------------------------------------------------------------------
    def read(self) -> str:
        """Return Polib.lean content. Reads disk on cache miss, returns
        ``""`` if the file doesn't exist yet (missing file is NOT cached)."""
        with PolibStore._cache_lock:
            cached = PolibStore._cache.get(self._key)
            if cached is not None:
                return cached
            if not self._lean_path.exists():
                return ""
            content = self._lean_path.read_text(encoding="utf-8")
            PolibStore._cache[self._key] = content
            return content

    def invalidate(self) -> None:
        """Evict cached content for this Polib path."""
        with PolibStore._cache_lock:
            PolibStore._cache.pop(self._key, None)

    @classmethod
    def invalidate_path(cls, polib_lean: Path) -> None:
        """Evict the cache for an arbitrary Polib path. Use when no PolibStore
        instance is available yet (e.g. inside the bootstrap that creates
        Polib.lean before any agent exists)."""
        key = str(polib_lean.resolve())
        with cls._cache_lock:
            cls._cache.pop(key, None)

    # ------------------------------------------------------------------
    # Transaction
    # ------------------------------------------------------------------
    @classmethod
    def _get_lock(cls, key: str) -> threading.Lock:
        with cls._locks_meta:
            lock = cls._locks.get(key)
            if lock is None:
                lock = threading.Lock()
                cls._locks[key] = lock
            return lock

    @contextmanager
    def transaction(self):
        """Acquire the per-path transaction lock; invalidate cache on exit.

        Cache invalidation runs whether the body returns normally OR raises,
        so even a failed save-then-rollback leaves the cache consistent.
        """
        lock = PolibStore._get_lock(self._key)
        with lock:
            try:
                yield self
            finally:
                self.invalidate()

    # ------------------------------------------------------------------
    # Mutating delegates (call these inside a transaction)
    # ------------------------------------------------------------------
    def save(self, *args, **kwargs):
        return self._mgr.save(*args, **kwargs)

    def remove(self, *args, **kwargs):
        return self._mgr.remove(*args, **kwargs)
