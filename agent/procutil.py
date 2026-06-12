"""Child-process lifetime helper.

Linux PR_SET_PDEATHSIG: the kernel delivers a signal to a process when its
parent dies. Wired into every child the pipeline spawns (pool workers, RL and
Hopper samplers, plantri enumerations, claude CLI calls, lake builds) so no
child can outlive the orchestrator — even when the orchestrator dies without
running its finally blocks (Ctrl-C with daemon threads, crash, SIGKILL).

Observed leak before this existed (2026-06-12): two generations of orphaned
spawn-pool workers, one burning 4 cores for 40 minutes, the other idling for
8+ hours, both reparented to init after their orchestrator died.
"""
from __future__ import annotations

import ctypes
import os
import signal

_PR_SET_PDEATHSIG = 1

try:
    _libc = ctypes.CDLL(None, use_errno=True)
    _libc.prctl  # resolve now: preexec_fn runs between fork and exec
except Exception:
    _libc = None


def set_pdeathsig(sig: int = signal.SIGKILL,
                  expected_ppid: int | None = None) -> None:
    """Ask the kernel to send `sig` to the CALLING process when its parent
    dies. No-op on non-Linux. Safe as a subprocess preexec_fn.

    `expected_ppid` closes the spawn race: if the parent died before this ran,
    the death signal would never fire, so exit immediately when the current
    parent is not the process that spawned us.
    """
    if _libc is not None:
        try:
            _libc.prctl(_PR_SET_PDEATHSIG, int(sig), 0, 0, 0)
        except Exception:
            return
    if expected_ppid is not None and os.getppid() != expected_ppid:
        os._exit(1)
