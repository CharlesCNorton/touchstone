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
_ENGINES = None


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


def scan_init(repo, sandbox_subject, allow_exec):
    """Pool initializer for the parallel SCAN triage (engines._triage_repo_verdicts). Like init -- the shared
    repo and the ordered package load through touchstone.check -- and additionally replicates scan's
    execution-mode flags in the worker: a spawned worker imports fresh and would otherwise default
    SANDBOX_SUBJECT on, running code during a symbolic-only scan, so set the worker's core flags to match the
    main process exactly. Holds the loaded engines module for the per-module worker."""
    global _REPO, _CHECK, _ENGINES
    _REPO = repo
    _CHECK = touchstone.check                                     # forces the ordered load (no submodule cycle)
    from touchstone import core as _core, engines as _eng         # both fully loaded now
    _core.SANDBOX_SUBJECT = sandbox_subject
    _core.ALLOW_SUBJECT_EXECUTION = allow_exec
    _ENGINES = _eng


def scan_module(item):
    """Triage one module (modname, src, total) against the shared repo and return its lite rows (the picklable
    per-module rows engines._triage_repo_verdicts re-expands)."""
    modname, src, total = item
    return _ENGINES._module_rows(modname, src, _REPO, total)
