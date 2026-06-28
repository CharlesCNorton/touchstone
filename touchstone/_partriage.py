"""Worker entry for the parallel whole-repo triage (engines._run_triage with jobs > 1).

A spawn-pool worker unpickles its task function by importing the module that defines it. Importing
touchstone.engines DIRECTLY re-enters the package's lazy loader while engines is still mid-import (engines'
`from . import core` triggers _impl, which re-imports the partial engines for the `from .engines import *` in
domains / theories / audit) -- a circular import. This module instead pulls the package in through its normal
entry (`touchstone.check`), so _impl loads the submodules in dependency order with no cycle, and exposes the
worker. The heavy import happens once per worker, in the pool initializer."""
import touchstone

_REPO = None
_CHECK = None


def init(repo):
    """Pool initializer: set the shared repo and force the package's ordered load (touchstone.check goes
    through _impl), so the worker's first task does not pay it and no direct-submodule cycle is hit."""
    global _REPO, _CHECK
    _REPO = repo
    _CHECK = touchstone.check


def run(job):
    """Check one triage item (hash, src, key, total) and return (hash, status). A top-level function (key not
    None) is checked against the shared repo; a standalone method (key None) without one. The verdict is the
    deterministic rlimit-bound result, identical to the serial check."""
    h, src, key, total = job
    fn = _CHECK or touchstone.check
    try:
        status = fn(src, repo=(_REPO if key is not None else None), target=key, total=total).status
    except Exception:
        status = "UNKNOWN"
    return h, status


def scan_unit_worker(widx, task_q, results, current, repo, modules, total, sandbox_subject, allow_exec, crash_on):
    """Crash-tolerant SCAN triage worker (engines._run_unit_pool). Pull unit tasks from task_q (read-only, so a
    reader's abort cannot corrupt it); record the in-flight unit index in current[widx] (a manager-backed list)
    before the possibly-aborting work, then store the finished row in results[idx] (a manager-backed dict). A z3
    SIGABRT on a unit kills this process after current[widx] is set, so the supervisor marks exactly that unit
    UNKNOWN -- the manager state survives the crash (it lives in a separate server process) and the other workers
    are untouched. Replicates scan's execution-mode flags (a fresh worker would default SANDBOX_SUBJECT on,
    running code in a symbolic scan) and suppresses core dumps (a z3 abort would otherwise write a multi-GB
    core)."""
    import queue as _queue
    _chk = touchstone.check                                       # force the ordered load first (no submodule cycle)
    from touchstone import core as _core, engines as _eng         # both fully loaded now
    _core.SANDBOX_SUBJECT = sandbox_subject
    _core.ALLOW_SUBJECT_EXECUTION = allow_exec
    try:
        import resource
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    except Exception:
        pass
    while True:
        try:
            idx, job = task_q.get(timeout=1.0)
        except _queue.Empty:
            continue                                             # the supervisor terminates us when the run is done
        current[widx] = idx                                     # announce the in-flight unit before the (possibly
        try:                                                    # aborting) work, so a crash names exactly one casualty
            row = _eng._unit_lite_row(job, repo, modules, total, crash_on)
        except BaseException:
            row = _eng._crash_unknown(job)                       # a catchable failure the guards somehow missed
        results[idx] = row
