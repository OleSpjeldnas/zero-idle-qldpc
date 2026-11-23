"""Direct calls to ldpc. POSIX workers share the immutable upstream OSD trial table."""

import multiprocessing as mp
import os
import time

import numpy as np
from ldpc import BpOsdDecoder
from scipy.sparse import csc_matrix

_JOB = None


def _decode_block(bounds):
    first, last = bounds
    decoder, model, packed = _JOB
    pred = np.empty((last - first, model.observables), np.uint8)
    start = time.process_time()
    for i in range(first, last):
        syn = np.unpackbits(packed[i], count=model.detectors, bitorder="little")
        correction = decoder.decode(syn)
        mask = np.bitwise_xor.reduce(
            model.masks[correction.astype(bool)], initial=np.uint64(0)
        )
        pred[i - first] = np.unpackbits(
            np.frombuffer(int(mask).to_bytes(8, "little"), np.uint8),
            count=model.observables,
            bitorder="little",
        )
    return first, pred, time.process_time() - start


def decode(model, packed, order, workers, checkpoint=None):
    global _JOB
    start = time.perf_counter()
    h = csc_matrix(
        (np.ones(len(model.indices), np.uint8), model.indices, model.offsets),
        shape=(model.detectors, len(model.probabilities)),
    )
    decoder = BpOsdDecoder(
        h,
        error_channel=model.probabilities.tolist(),
        max_iter=30,
        bp_method="minimum_sum",
        ms_scaling_factor=0.8,
        schedule="serial",
        osd_method="OSD_CS",
        osd_order=order,
        omp_thread_count=1,
    )
    _JOB = decoder, model, packed
    setup = time.perf_counter() - start
    start = time.perf_counter()
    pred = np.empty((len(packed), model.observables), np.uint8)
    total_cpu = 0
    pending = []
    block = 16 if len(model.probabilities) > 30000 else 128
    for first in range(0, len(packed), block):
        last = min(len(packed), first + block)
        if checkpoint and (checkpoint / f"{first}.npz").exists():
            with np.load(checkpoint / f"{first}.npz") as receipt:
                pred[first:last] = receipt["prediction"]
                total_cpu += float(receipt["cpu"])
        else:
            pending.append((first, last))
    workers = min(workers, len(pending)) if "fork" in mp.get_all_start_methods() else 1
    pool = None
    try:
        if workers > 1:
            pool = mp.get_context("fork").Pool(workers)
            completed = pool.imap_unordered(_decode_block, pending)
        else:
            completed = map(_decode_block, pending)
        for number, (first, values, cpu) in enumerate(completed, 1):
            pred[first : first + len(values)] = values
            total_cpu += cpu
            if checkpoint:
                checkpoint.mkdir(parents=True, exist_ok=True)
                tmp = checkpoint / f"{first}.tmp.npz"
                np.savez(tmp, prediction=values, cpu=cpu)
                os.replace(tmp, checkpoint / f"{first}.npz")
            if number % 16 == 0:
                print(
                    f"ldpc CS{order} completed {number}/{len(pending)} blocks",
                    flush=True,
                )
        if pool:
            pool.close()
    finally:
        if pool:
            pool.terminate()
            pool.join()
        _JOB = None
    return pred, dict(
        setup_s=setup,
        decode_cpu_s=total_cpu,
        wall_this_invocation_s=time.perf_counter() - start,
        us_per_shot=1e6 * total_cpu / len(packed),
        workers=workers,
    )
