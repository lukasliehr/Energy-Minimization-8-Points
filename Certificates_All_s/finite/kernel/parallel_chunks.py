"""Forked row chunks with the same arithmetic and accumulation order.

Call only from a single-threaded Linux checker after BLAS has been limited to
one thread. The parent processes matrix blocks sequentially, while each pool
evaluates disjoint row chunks of the current block. Large constant factors are
prepared before fork and inherited read-only via copy-on-write.
"""
import multiprocessing as multiprocessing
import os
from pathlib import Path
import time

import numpy as np
from interval_arithmetic import I
from ipoly import IP, prepare_right
from taylor_models import ORDER

_JOB = None
LAST_DIAGNOSTICS = []


def memory_snapshot():
    """Linux proportional memory; diagnostics only."""
    out = {}
    path = Path("/proc/self/smaps_rollup")
    if path.exists():
        for line in path.read_text().splitlines():
            key, _, value = line.partition(":")
            if key in ("Rss", "Pss", "Private_Dirty", "Shared_Dirty"):
                out[key + "_KiB"] = int(value.split()[0])
    return out


def _pack(model):
    return ([(a.lo, a.hi) for a in model.c], (model.e.lo, model.e.hi))


def _unpack(data):
    coeffs, error = data
    return IP([I(lo, hi) for lo, hi in coeffs], I(*error))


def _worker(task):
    from verify_interval import coefficient_model
    start, stop = task
    dat, basis, rows, indices, right_c, right_x = _JOB
    begun = time.perf_counter()
    before = memory_snapshot()
    coeff = coefficient_model([dat], [basis], rows[start:stop], [indices])
    tt = right_c(coeff)
    rr = right_x(coeff)
    diagnostics = {
        "pid": os.getpid(), "start": start, "stop": stop,
        "elapsed_seconds": time.perf_counter() - begun,
        "memory_before": before, "memory_after": memory_snapshot(),
    }
    return start, stop, _pack(tt), _pack(rr), diagnostics


def correction_models_parallel(data, bases, rows, inds, slices, C, w0, targetM,
                               workers=3, allow_test_degree=False):
    """Same T/r enclosures as correction_models_streamed, ordered by row/block.

    The production-facing guard permits degree18 and degree20. Small-degree comparison
    tests must explicitly opt out of that guard. Worker exceptions abort the
    entire call and terminate the pool; no successful report is emitted here.
    """
    import verify_interval
    global _JOB, LAST_DIAGNOSTICS
    if verify_interval.v.D not in (9, 10) and not allow_test_degree:
        raise ValueError("Parallel row execution is restricted to degree18 and degree20")
    if not 1 <= workers <= 6:
        raise ValueError("One to six fork workers supported")
    if "fork" not in multiprocessing.get_all_start_methods():
        raise RuntimeError("Linux fork is required")
    LAST_DIAGNOSTICS = []
    nrows = len(rows)
    chunk = int(os.environ.get("N8_ROW_CHUNK", "32"))
    if not 1 <= chunk <= 64:
        raise ValueError("Invalid row chunk")
    tc = [I(np.zeros((nrows, nrows))) for _ in range(ORDER + 1)]
    te = I(np.zeros((nrows, nrows)))
    rc = [cc for cc in targetM.c]
    re = targetM.e
    tasks = [(start, min(start + chunk, nrows)) for start in range(0, nrows, chunk)]
    context = multiprocessing.get_context("fork")
    try:
        for dat, basis, indices, sl in zip(data, bases, inds, slices):
            cb, x0 = C[sl, :], I(w0[sl, None])
            right_c, right_x = prepare_right(cb), prepare_right(x0)
            _JOB = (dat, basis, rows, indices, right_c, right_x)
            parent_memory = memory_snapshot()
            with context.Pool(processes=min(workers, len(tasks))) as pool:
                # imap preserves the original ascending row-chunk order.
                for start, stop, packed_t, packed_r, diagnostics in pool.imap(_worker, tasks, chunksize=1):
                    tt, rr = _unpack(packed_t), _unpack(packed_r)
                    jj = slice(start, stop)
                    for k in range(ORDER + 1):
                        tc[k][jj, :] = tc[k][jj, :] + tt.c[k]
                        rc[k][jj, :] = rc[k][jj, :] - rr.c[k]
                    te[jj, :] = te[jj, :] + tt.e
                    re[jj, :] = re[jj, :] + rr.e
                    diagnostics.update(block=dat["name"], parent_memory_at_fork=parent_memory)
                    LAST_DIAGNOSTICS.append(diagnostics)
            _JOB = None
            del right_c, right_x
    finally:
        _JOB = None
    return IP(tc, te), IP(rc, re)
