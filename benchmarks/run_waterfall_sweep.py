#!/usr/bin/env python3
"""Multi-p waterfall error-suppression and Pareto latency sweep for zero-idle-qldpc.

Compares across p in {0.0005, 0.00075, 0.001, 0.0015, 0.002, 0.003}:
  1. Co-designed asymmetric (4,2) zero-idle T=6 codes ([[56,6,6]], [[84,8,6]], [[96,8,6]])
     against matched T=12 serialized two-phase baselines and canonical (3,3) two-phase BB.
  2. Non-abelian order-30 [[60,8,6]]@T=7 (Z_5 x| Z_6) and 90-class [[60,8,6]]@T=7
     against canonical abelian Z_6 x Z_5 ~= Z_30 two-phase d_circ=4 hook-collapse.
  3. Drop-in decoding on fixed Stim circuits — including IBM's published Bravyi-Cross
     [[72,12,6]] and [[144,12,12]] Gross codes (4 and 12 rounds) and [[70,6,8]]@T=10 —
     comparing SpaceTimeDecoder (scalar & batch), C++17 BP+OSD-CS, and external
     Python/Cython ldpc.BpOsdDecoder (OSD-CS) anchors.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import ctypes as ct
from dataclasses import dataclass
import hashlib
from importlib.metadata import version
import json
import math
import multiprocessing as mp
import os
from pathlib import Path
import platform
import re
import sys
import time
from typing import Any

import numpy as np
from scipy.sparse import csc_matrix
import stim

HERE = Path(__file__).resolve().parent
REPO_ROOT = Path(__file__).resolve().parents[1]


def resolve_repo_paths() -> tuple[Path, Path]:
    """Locate circuits/python source directory and compiled libqldpc shared library."""
    if not ((REPO_ROOT / "circuits").is_dir() and (REPO_ROOT / "python").is_dir()):
        raise FileNotFoundError(
            "Could not locate zero-idle-qldpc circuits/ and python/ directories"
        )
    cand = REPO_ROOT / "build" / "libqldpc.so"
    if cand.is_file():
        return REPO_ROOT, cand
    raise FileNotFoundError(
        "Could not locate compiled build/libqldpc.so (run `make build` first)"
    )


SRC_ROOT, LIB_PATH = resolve_repo_paths()
if str(SRC_ROOT / "python") not in sys.path:
    sys.path.insert(0, str(SRC_ROOT / "python"))

from zero_idle_qldpc.circuits import memory  # noqa: E402
from zero_idle_qldpc.decoder import Mechanisms  # noqa: E402
from zero_idle_qldpc.synthesizer import materialize  # noqa: E402

P_SWEEP = (0.0005, 0.00075, 0.001, 0.0015, 0.002, 0.003)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def wilson_95(errors: int, shots: int) -> tuple[float, float]:
    """Two-sided 95% Wilson binomial confidence interval."""
    if shots <= 0:
        return 0.0, 1.0
    z = 1.959963984540054
    phat = errors / shots
    denom = 1.0 + (z * z) / shots
    center = (phat + (z * z) / (2.0 * shots)) / denom
    half = (
        z
        * math.sqrt((phat * (1.0 - phat) + (z * z) / (4.0 * shots)) / shots)
        / denom
    )
    return max(0.0, center - half), min(1.0, center + half)


def per_round_ler(frame_ler: float, rounds: int) -> float:
    if frame_ler <= 0.0:
        return 0.0
    if frame_ler >= 1.0:
        return 1.0
    return 1.0 - (1.0 - min(0.999999999, frame_ler)) ** (1.0 / rounds)


_CACHED_LIB: ct.CDLL | None = None


def _get_lib() -> ct.CDLL:
    global _CACHED_LIB
    if _CACHED_LIB is None:
        lib = ct.CDLL(str(LIB_PATH))
        for family in ("spacetime", "bposd"):
            create = getattr(lib, f"create_{family}_decoder")
            create.argtypes = [ct.c_int] * 3 + [ct.c_void_p] * 4
            create.restype = ct.c_void_p
            destroy = getattr(lib, f"destroy_{family}_decoder")
            destroy.argtypes = [ct.c_void_p]
            dec = getattr(lib, f"decode_{family}_batch")
            argtypes = [
                ct.c_void_p,
                ct.c_void_p,
                ct.c_int,
                ct.c_int,
                ct.c_int,
                ct.c_float,
                ct.c_float,
            ]
            if family == "bposd":
                argtypes += [ct.c_int, ct.c_int]
            argtypes += [ct.c_void_p]
            dec.argtypes = argtypes
            dec.restype = ct.c_int
        _CACHED_LIB = lib
    return _CACHED_LIB


class IsolatedNativeDecoder:
    """Direct ctypes binding to compiled libqldpc.so."""

    def __init__(self, model: Mechanisms, *, reference: bool = False) -> None:
        self.detectors = model.detectors
        self.observables = model.observables
        lib = _get_lib()
        family = "bposd" if reference else "spacetime"
        create = getattr(lib, f"create_{family}_decoder")
        self._destroy = getattr(lib, f"destroy_{family}_decoder")
        self._decode = getattr(lib, f"decode_{family}_batch")
        self._params = (20, 0.85, 0.75, 2, 20) if reference else (8, 0.82, 0.78)

        prob = np.asarray(model.probabilities)
        llr = np.ascontiguousarray(np.log((1.0 - prob) / prob), np.float32)
        offsets = np.ascontiguousarray(model.offsets, np.int32)
        indices = np.ascontiguousarray(model.indices, np.int32)
        masks = np.ascontiguousarray(model.masks, np.uint64)
        self._ptr = create(
            model.detectors,
            len(prob),
            model.observables,
            *(x.ctypes.data for x in (offsets, indices, llr, masks)),
        )
        if not self._ptr:
            raise RuntimeError(f"Native {family} decoder rejected DEM")

    def __del__(self) -> None:
        ptr = getattr(self, "_ptr", None)
        if ptr:
            self._destroy(ptr)
            self._ptr = None

    def decode(self, packed: np.ndarray) -> np.ndarray:
        arr = np.asarray(packed, dtype=np.uint8)
        syn = np.ascontiguousarray(np.atleast_2d(arr))
        out = np.empty((len(syn), self.observables), np.uint8)
        rc = self._decode(
            self._ptr,
            syn.ctypes.data,
            len(syn),
            syn.shape[1],
            *self._params,
            out.ctypes.data,
        )
        if rc != 0:
            raise RuntimeError(f"Native decode failed with rc={rc}")
        return out[0] if arr.ndim == 1 else out


@dataclass(frozen=True)
class CircuitSpec:
    key: str
    label: str
    category: str
    n: int
    k: int
    d_static: int
    d_circ_z: int
    t_cnot: int
    rounds: int
    published: bool
    stage1_prefix: str | None = None
    custom_code: dict[str, Any] | None = None
    notes: str = ""


def build_suite() -> list[CircuitSpec]:
    cdir = SRC_ROOT / "circuits"

    def load_stage1_json(prefix: str) -> dict[str, Any]:
        return json.loads((cdir / f"{prefix}.json").read_text())

    # Construct matched T=12 serialized two-phase baselines on the exact same (4,2) matrices
    t12 = tuple(range(12))
    n56_j = load_stage1_json("n56")
    n84_j = load_stage1_json("n84")
    n96_j = load_stage1_json("n96")
    n56_t12 = materialize(tuple(n56_j["group"]), n56_j["A"], n56_j["B"], t12, 6, 5)
    n84_t12 = materialize(tuple(n84_j["group"]), n84_j["A"], n84_j["B"], t12, 8, 6)
    n96_t12 = materialize(tuple(n96_j["group"]), n96_j["A"], n96_j["B"], t12, 8, 6)

    # Canonical (3,3) two-phase BB baselines (including Z_6 x Z_5 ~= Z_30 d_circ=4 collapse)
    bb84_c1_t12 = materialize((7, 6, 1), (0, 28, 38), (16, 38, 0), t12, 8, 5)
    ab60_t12_collapse = materialize((6, 5, 1), (0, 22, 11), (0, 23, 10), t12, 8, 4)

    return [
        # Co-designed (4,2) zero-idle T=6 codes
        CircuitSpec(
            key="n56-t6",
            label="[[56,6,6]] (4,2) Zero-Idle T=6",
            category="codesign_42_t6",
            n=56,
            k=6,
            d_static=6,
            d_circ_z=6,
            t_cnot=6,
            rounds=4,
            published=False,
            stage1_prefix="n56",
            notes="Z14 x Z2 asymmetric (4,2), 100% active CNOT ticks, d_circ=6",
        ),
        CircuitSpec(
            key="n84-t6",
            label="[[84,8,6]] (4,2) Zero-Idle T=6",
            category="codesign_42_t6",
            n=84,
            k=8,
            d_static=6,
            d_circ_z=6,
            t_cnot=6,
            rounds=4,
            published=False,
            stage1_prefix="n84",
            notes="Cyclic Z42 asymmetric (4,2), 100% active CNOT ticks, d_circ=6",
        ),
        CircuitSpec(
            key="n96-t6",
            label="[[96,8,6]] (4,2) Zero-Idle T=6",
            category="codesign_42_t6",
            n=96,
            k=8,
            d_static=6,
            d_circ_z=6,
            t_cnot=6,
            rounds=4,
            published=False,
            stage1_prefix="n96",
            notes="Z12 x Z4 asymmetric (4,2), 100% active CNOT ticks, d_circ=6",
        ),
        # Matched T=12 two-phase baselines
        CircuitSpec(
            key="n56-t12-twophase",
            label="[[56,6,6]] Two-Phase T=12",
            category="baseline_t12",
            n=56,
            k=6,
            d_static=6,
            d_circ_z=5,
            t_cnot=12,
            rounds=4,
            published=False,
            custom_code=n56_t12,
            notes="Same [[56,6,6]] matrices serialized X-then-Z (T=12, hook proxy drops 6->5)",
        ),
        CircuitSpec(
            key="n84-t12-twophase",
            label="[[84,8,6]] Two-Phase T=12",
            category="baseline_t12",
            n=84,
            k=8,
            d_static=6,
            d_circ_z=6,
            t_cnot=12,
            rounds=4,
            published=False,
            custom_code=n84_t12,
            notes="Same [[84,8,6]] matrices serialized X-then-Z (T=12, 2x CNOT depth)",
        ),
        CircuitSpec(
            key="n96-t12-twophase",
            label="[[96,8,6]] Two-Phase T=12",
            category="baseline_t12",
            n=96,
            k=8,
            d_static=6,
            d_circ_z=6,
            t_cnot=12,
            rounds=4,
            published=False,
            custom_code=n96_t12,
            notes="Same [[96,8,6]] matrices serialized X-then-Z (T=12, 2x CNOT depth)",
        ),
        CircuitSpec(
            key="bb84-c1-t12",
            label="[[84,8,6]] (3,3) BB Two-Phase T=12",
            category="baseline_t12",
            n=84,
            k=8,
            d_static=6,
            d_circ_z=5,
            t_cnot=12,
            rounds=4,
            published=False,
            custom_code=bb84_c1_t12,
            notes="Canonical Z7 x Z6 (3,3) Bivariate Bicycle at T=12 (hook proxy=5)",
        ),
        # Order-30 non-abelian vs abelian two-phase d_circ=4 collapse
        CircuitSpec(
            key="n60-nonabelian-t7",
            label="[[60,8,6]] Non-Abelian (Z5⋊Z6) T=7",
            category="order30_comparison",
            n=60,
            k=8,
            d_static=6,
            d_circ_z=6,
            t_cnot=7,
            rounds=4,
            published=False,
            stage1_prefix="n60-nonabelian",
            notes="Order-30 non-abelian semidirect 2BGA; verified Z-memory d_circ=6 (X-sector proxy=4)",
        ),
        CircuitSpec(
            key="n60-archive-t7",
            label="[[60,8,6]] 90-Class Scheduled T=7",
            category="order30_comparison",
            n=60,
            k=8,
            d_static=6,
            d_circ_z=6,
            t_cnot=7,
            rounds=4,
            published=False,
            stage1_prefix="n60-archive",
            notes="Order-30 Z6 x Z5 with reversal-coupled 90-class T=7 schedule; d_circ=6",
        ),
        CircuitSpec(
            key="n60-abelian-t12-collapse",
            label="[[60,8,6]] Abelian Z30 Two-Phase T=12 (d_circ=4)",
            category="order30_comparison",
            n=60,
            k=8,
            d_static=6,
            d_circ_z=4,
            t_cnot=12,
            rounds=4,
            published=False,
            custom_code=ab60_t12_collapse,
            notes="Canonical Z6 x Z5 ~= Z30 two-phase [A,A,A,B,B,B] midpoint hook collapse (d_circ=4, O(p^2))",
        ),
        # Fixed-circuit drop-in benchmarks including IBM published Gross codes
        CircuitSpec(
            key="n70-t10-r4",
            label="[[70,6,8]] 2BGA T=10 (d_circ=7)",
            category="fixed_circuit_decoder",
            n=70,
            k=6,
            d_static=8,
            d_circ_z=7,
            t_cnot=10,
            rounds=4,
            published=False,
            stage1_prefix="n70",
            notes="Z7 x Z5 code with static d=8 and verified Z-memory d_circ=7",
        ),
        CircuitSpec(
            key="ibm72-published-r4",
            label="IBM [[72,12,6]] Gross-Family (Published r=4)",
            category="ibm_gross",
            n=72,
            k=12,
            d_static=6,
            d_circ_z=6,
            t_cnot=7,
            rounds=4,
            published=True,
            stage1_prefix="ibm72-published",
            notes="Bravyi-Cross Nature (2024) [[72,12,6]] published schedule, 4 rounds",
        ),
        CircuitSpec(
            key="ibm72-t9-r4",
            label="IBM [[72,12,6]] Hook-Preserving T=9 (r=4)",
            category="ibm_gross",
            n=72,
            k=12,
            d_static=6,
            d_circ_z=6,
            t_cnot=9,
            rounds=4,
            published=False,
            stage1_prefix="ibm72-t9",
            notes="[[72,12,6]] under T=9 schedule lifting single-round hook proxy 5->6",
        ),
        CircuitSpec(
            key="ibm144-published-r4",
            label="IBM [[144,12,12]] Gross Code (Published r=4)",
            category="ibm_gross",
            n=144,
            k=12,
            d_static=12,
            d_circ_z=10,
            t_cnot=7,
            rounds=4,
            published=True,
            stage1_prefix="ibm144-published",
            notes="Bravyi-Cross Nature (2024) flagship [[144,12,12]] Gross code, 4 rounds (D=576)",
        ),
        CircuitSpec(
            key="ibm144-published-r12",
            label="IBM [[144,12,12]] Gross Code (Published r=12)",
            category="ibm_gross",
            n=144,
            k=12,
            d_static=12,
            d_circ_z=10,
            t_cnot=7,
            rounds=12,
            published=True,
            stage1_prefix="ibm144-published",
            notes="Bravyi-Cross Nature (2024) flagship [[144,12,12]] Gross code, 12 rounds (D=1728, M=67752)",
        ),
    ]


def build_stim_circuit(spec: CircuitSpec, p: float) -> tuple[stim.Circuit, str | None]:
    """Load exact Stage 1 .stim file (rescaling noise arg for non-tabulated p) or build baseline."""
    if spec.stage1_prefix is not None:
        cdir = SRC_ROOT / "circuits"
        code = json.loads((cdir / f"{spec.stage1_prefix}.json").read_text())
        exact_file = cdir / f"{spec.stage1_prefix}-r{spec.rounds}-p{p:.3f}.stim"
        if exact_file.is_file() and p in (0.001, 0.002):
            raw = exact_file.read_text()
            generated = str(memory(code, spec.rounds, p, spec.published))
            body = "\n".join(
                line for line in raw.splitlines() if not line.startswith("#")
            )
            if body.strip() != generated.strip():
                raise RuntimeError(f"Mismatch between {exact_file.name} and memory()")
            return stim.Circuit(raw), exact_file.name

        # Rescale directly from the checked-in p=0.001 .stim template and cross-check memory()
        template_file = cdir / f"{spec.stage1_prefix}-r{spec.rounds}-p0.001.stim"
        raw_t = template_file.read_text()
        rescaled = re.sub(r"\(0\.001\)", f"({p:.8g})", raw_t)
        circ = stim.Circuit(rescaled)
        circ_check = memory(code, spec.rounds, p, spec.published)
        if str(circ).strip() != str(circ_check).strip():
            circ = circ_check
        return circ, f"{template_file.name}@p={p:.5g}"

    assert spec.custom_code is not None
    return memory(spec.custom_code, spec.rounds, p, spec.published), None


def deterministic_seed(key: str, p: float) -> int:
    token = f"waterfall-v1:{key}:p={p:.6f}".encode()
    return int(sha256_bytes(token)[:15], 16)


def shots_for_point(spec: CircuitSpec, p: float) -> int:
    if spec.key == "ibm144-published-r12":
        # 12-round D=1728 Gross code: C++ BP+OSD-CS takes ~25-30 ms/shot
        return 2500 if p < 0.002 else 1500
    return 10000 if p < 0.002 else 5000


_LDPC_JOB: Any = None


def _ldpc_worker_block(bounds: tuple[int, int]) -> tuple[int, np.ndarray, float]:
    first, last = bounds
    decoder, model, packed = _LDPC_JOB
    pred = np.empty((last - first, model.observables), np.uint8)
    t0 = time.process_time()
    for i in range(first, last):
        syn = np.unpackbits(packed[i], count=model.detectors, bitorder="little")
        corr = decoder.decode(syn)
        mask = np.bitwise_xor.reduce(
            model.masks[corr.astype(bool)], initial=np.uint64(0)
        )
        pred[i - first] = np.unpackbits(
            np.frombuffer(int(mask).to_bytes(8, "little"), np.uint8),
            count=model.observables,
            bitorder="little",
        )
    return first, pred, time.process_time() - t0


def run_ldpc_anchor(
    model: Mechanisms,
    packed: np.ndarray,
    truth: np.ndarray,
    order: int = 2,
    workers: int = 2,
) -> dict[str, Any]:
    """Run external open-source ldpc.BpOsdDecoder (OSD-CS) on the first len(packed) syndromes."""
    from ldpc import BpOsdDecoder

    global _LDPC_JOB
    t_setup0 = time.perf_counter()
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
    setup_s = time.perf_counter() - t_setup0
    _LDPC_JOB = (decoder, model, packed)
    n_shots = len(packed)
    block = 25 if len(model.probabilities) > 15000 else 50
    chunks = [(i, min(n_shots, i + block)) for i in range(0, n_shots, block)]
    pred = np.empty((n_shots, model.observables), np.uint8)
    total_cpu = 0.0
    t_wall0 = time.perf_counter()
    use_workers = (
        min(workers, len(chunks)) if "fork" in mp.get_all_start_methods() else 1
    )
    pool = None
    try:
        if use_workers > 1:
            pool = mp.get_context("fork").Pool(use_workers)
            it = pool.imap_unordered(_ldpc_worker_block, chunks)
        else:
            it = map(_ldpc_worker_block, chunks)
        for first, vals, cpu_s in it:
            pred[first : first + len(vals)] = vals
            total_cpu += cpu_s
        if pool:
            pool.close()
    finally:
        if pool:
            pool.terminate()
            pool.join()
        _LDPC_JOB = None

    wall_s = time.perf_counter() - t_wall0
    errs = int(np.count_nonzero(np.any(pred != truth, axis=1)))
    lo, hi = wilson_95(errs, n_shots)
    ler = errs / n_shots
    return {
        "shots": n_shots,
        "errors": errs,
        "frame_ler": ler,
        "wilson95_lo": lo,
        "wilson95_hi": hi,
        "setup_s": round(setup_s, 6),
        "decode_cpu_s": round(total_cpu, 6),
        "wall_s": round(wall_s, 6),
        "us_per_shot": round(1e6 * total_cpu / n_shots, 2),
        "prediction_sha256": sha256_bytes(pred.tobytes()),
    }


def evaluate_point(
    spec: CircuitSpec, p: float, measure_scalar: bool
) -> dict[str, Any]:
    circ, stim_ref = build_stim_circuit(spec, p)
    shots = shots_for_point(spec, p)
    seed = deterministic_seed(spec.key, p)
    sampler = circ.compile_detector_sampler(seed=seed)
    packed, obs_packed = sampler.sample(
        shots, separate_observables=True, bit_packed=True
    )
    truth = np.unpackbits(
        obs_packed, axis=1, count=circ.num_observables, bitorder="little"
    )
    model = Mechanisms.from_dem(circ.detector_error_model())

    # 1. SpaceTimeDecoder (batch)
    t0 = time.perf_counter()
    dec_st = IsolatedNativeDecoder(model, reference=False)
    st_setup_s = time.perf_counter() - t0

    t_cpu0 = time.process_time()
    pred_batch = dec_st.decode(packed)
    st_batch_cpu = time.process_time() - t_cpu0
    st_errs = int(np.count_nonzero(np.any(pred_batch != truth, axis=1)))
    st_ler = st_errs / shots
    st_lo, st_hi = wilson_95(st_errs, shots)

    arms: dict[str, Any] = {
        "spacetime_batch": {
            "shots": shots,
            "errors": st_errs,
            "frame_ler": st_ler,
            "per_round_ler": per_round_ler(st_ler, spec.rounds),
            "wilson95_lo": st_lo,
            "wilson95_hi": st_hi,
            "setup_s": round(st_setup_s, 6),
            "decode_cpu_s": round(st_batch_cpu, 6),
            "us_per_shot": round(1e6 * st_batch_cpu / shots, 3),
            "prediction_sha256": sha256_bytes(pred_batch.tobytes()),
        }
    }

    # Optional N=1 scalar latency & bit-exactness verification
    if measure_scalar:
        t_sc0 = time.process_time()
        pred_scalar = np.stack([dec_st.decode(row) for row in packed])
        st_scalar_cpu = time.process_time() - t_sc0
        disagree = int(np.count_nonzero(pred_scalar != pred_batch))
        if disagree != 0:
            raise RuntimeError(
                f"Scalar vs batch disagreement ({disagree}) on {spec.key} @ p={p}"
            )
        arms["spacetime_scalar"] = {
            "shots": shots,
            "errors": st_errs,
            "frame_ler": st_ler,
            "per_round_ler": per_round_ler(st_ler, spec.rounds),
            "wilson95_lo": st_lo,
            "wilson95_hi": st_hi,
            "setup_s": round(st_setup_s, 6),
            "decode_cpu_s": round(st_scalar_cpu, 6),
            "us_per_shot": round(1e6 * st_scalar_cpu / shots, 3),
            "scalar_batch_disagreements": 0,
            "prediction_sha256": sha256_bytes(pred_scalar.tobytes()),
        }

    # 2. C++17 Reference BP+OSD-CS (order 2, K=20)
    t0 = time.perf_counter()
    dec_ref = IsolatedNativeDecoder(model, reference=True)
    ref_setup_s = time.perf_counter() - t0
    t_rcpu0 = time.process_time()
    pred_ref = dec_ref.decode(packed)
    ref_cpu = time.process_time() - t_rcpu0
    ref_errs = int(np.count_nonzero(np.any(pred_ref != truth, axis=1)))
    ref_ler = ref_errs / shots
    ref_lo, ref_hi = wilson_95(ref_errs, shots)

    arms["cpp_bposd_cs2"] = {
        "shots": shots,
        "errors": ref_errs,
        "frame_ler": ref_ler,
        "per_round_ler": per_round_ler(ref_ler, spec.rounds),
        "wilson95_lo": ref_lo,
        "wilson95_hi": ref_hi,
        "setup_s": round(ref_setup_s, 6),
        "decode_cpu_s": round(ref_cpu, 6),
        "us_per_shot": round(1e6 * ref_cpu / shots, 3),
        "prediction_sha256": sha256_bytes(pred_ref.tobytes()),
    }

    return {
        "p": p,
        "shots": shots,
        "seed": seed,
        "stim_source": stim_ref,
        "detectors": model.detectors,
        "mechanisms": len(model.probabilities),
        "observables": model.observables,
        "syndrome_sha256": sha256_bytes(packed.tobytes()),
        "truth_sha256": sha256_bytes(truth.tobytes()),
        "arms": arms,
    }


def collect_stage1_receipts() -> dict[str, dict[str, Any]]:
    """Read completed 10,000-shot Stage 1 benchmark receipts (read-only) when present."""
    receipt_dir = SRC_ROOT / "build" / "receipts" / "full"
    out: dict[str, dict[str, Any]] = {}
    if not receipt_dir.is_dir():
        return out
    for p in sorted(receipt_dir.glob("*.json")):
        try:
            d = json.loads(p.read_text())
            arm = d["id"]["arm"]
            stem = p.stem[: -(len(arm) + 1)]
            meas = dict(d["measurement"])
            meas["shots"] = 10000
            meas["frame_ler"] = meas["errors"] / 10000.0
            lo, hi = wilson_95(int(meas["errors"]), 10000)
            meas["wilson95_lo"] = lo
            meas["wilson95_hi"] = hi
            out.setdefault(stem, {})[arm] = meas
        except Exception:
            continue
    return out


def _eval_fork_task(task: tuple[CircuitSpec, float, bool]) -> tuple[str, dict[str, Any]]:
    spec, p, m_sc = task
    return spec.key, evaluate_point(spec, p, m_sc)


def _write_payload(
    out_path: Path,
    suite: list[CircuitSpec],
    point_map: dict[str, list[dict[str, Any]]],
    stage1_10k: dict[str, dict[str, Any]],
    cpp_wall_s: float,
    t_start: float,
) -> None:
    circuits_out = []
    for spec in suite:
        pts = sorted(point_map[spec.key], key=lambda x: x["p"])
        circuits_out.append(
            {
                "key": spec.key,
                "label": spec.label,
                "category": spec.category,
                "n": spec.n,
                "k": spec.k,
                "d_static": spec.d_static,
                "d_circ_z": spec.d_circ_z,
                "t_cnot": spec.t_cnot,
                "rounds": spec.rounds,
                "published": spec.published,
                "stage1_prefix": spec.stage1_prefix,
                "notes": spec.notes,
                "points": pts,
            }
        )
    payload = {
        "schema": "zero-idle-qldpc-waterfall-v1",
        "platform": platform.platform(),
        "python": sys.version.split()[0],
        "versions": {
            pkg: version(pkg) for pkg in ("numpy", "scipy", "stim", "ldpc", "matplotlib")
        },
        "lib_path": (
            str(LIB_PATH.relative_to(REPO_ROOT))
            if LIB_PATH.is_relative_to(REPO_ROOT)
            else LIB_PATH.name
        ),
        "lib_sha256": sha256_bytes(LIB_PATH.read_bytes()),
        "p_values": list(P_SWEEP),
        "cpp_sweep_wall_s": round(cpp_wall_s, 3),
        "total_wall_s": round(time.perf_counter() - t_start, 3),
        "circuits": circuits_out,
        "stage1_10k_receipts": stage1_10k,
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    tmp = out_path.with_suffix(".tmp.json")
    tmp.write_text(json.dumps(payload, indent=2) + "\n")
    tmp.replace(out_path)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=HERE / "results" / "waterfall_results.json",
        help="Path to output JSON file",
    )
    parser.add_argument(
        "--cpp-workers",
        type=int,
        default=4,
        help="Forked processes for independent C++17 (circuit, p) points",
    )
    parser.add_argument(
        "--ldpc-shots",
        type=int,
        default=500,
        help="Shots per anchor point for external ldpc.BpOsdDecoder on Gross codes",
    )
    parser.add_argument(
        "--ldpc-workers",
        type=int,
        default=4,
        help="Forked single-threaded workers for external ldpc anchor points",
    )
    parser.add_argument(
        "--skip-ldpc",
        action="store_true",
        help="Skip running fresh external ldpc anchor points",
    )
    args = parser.parse_args()

    t_start = time.perf_counter()
    suite = build_suite()
    spec_map = {s.key: s for s in suite}

    tasks: list[tuple[CircuitSpec, float, bool]] = []
    for spec in suite:
        for p in P_SWEEP:
            measure_scalar = p in (0.001, 0.002)
            tasks.append((spec, p, measure_scalar))

    print(
        f"Running {len(tasks)} C++17 (circuit, p) points using {LIB_PATH} ...",
        flush=True,
    )
    point_map: dict[str, list[dict[str, Any]]] = {s.key: [] for s in suite}
    if args.cpp_workers > 1 and "fork" in mp.get_all_start_methods():
        with mp.get_context("fork").Pool(args.cpp_workers) as pool:
            for key, res in pool.imap_unordered(_eval_fork_task, tasks):
                point_map[key].append(res)
                st = res["arms"]["spacetime_batch"]
                rf = res["arms"]["cpp_bposd_cs2"]
                print(
                    f"  {key:26s} p={res['p']:.5f} shots={res['shots']:5d} | "
                    f"SpaceTime: {st['errors']:4d} err ({st['us_per_shot']:6.1f} us) | "
                    f"C++ CS2: {rf['errors']:4d} err ({rf['us_per_shot']:7.1f} us)",
                    flush=True,
                )
    else:
        for task in tasks:
            key, res = _eval_fork_task(task)
            point_map[key].append(res)
            st = res["arms"]["spacetime_batch"]
            rf = res["arms"]["cpp_bposd_cs2"]
            print(
                f"  {key:26s} p={res['p']:.5f} shots={res['shots']:5d} | "
                f"SpaceTime: {st['errors']:4d} err ({st['us_per_shot']:6.1f} us) | "
                f"C++ CS2: {rf['errors']:4d} err ({rf['us_per_shot']:7.1f} us)",
                flush=True,
            )

    cpp_wall_s = time.perf_counter() - t_start
    print(f"Completed C++17 multi-p sweep in {cpp_wall_s:.2f} s wall.", flush=True)

    stage1_10k = collect_stage1_receipts()
    _write_payload(args.output, suite, point_map, stage1_10k, cpp_wall_s, t_start)
    print(f"Checkpointed C++17 sweep to {args.output}.", flush=True)

    # Run deterministic external ldpc.BpOsdDecoder (OSD-CS, order 2) anchors on Gross codes
    ldpc_targets = [
        ("ibm72-published-r4", 0.001),
        ("ibm72-published-r4", 0.002),
        ("ibm72-published-r4", 0.003),
        ("ibm144-published-r4", 0.001),
        ("ibm144-published-r4", 0.002),
        ("ibm144-published-r4", 0.003),
    ]

    if not args.skip_ldpc and args.ldpc_shots > 0:
        print(
            f"Running {len(ldpc_targets)} external ldpc.BpOsdDecoder ({args.ldpc_shots}-shot) Gross anchors ...",
            flush=True,
        )
        for key, p in ldpc_targets:
            spec = spec_map[key]
            circ, _ = build_stim_circuit(spec, p)
            seed = deterministic_seed(spec.key, p)
            sampler = circ.compile_detector_sampler(seed=seed)
            packed, obs_packed = sampler.sample(
                args.ldpc_shots, separate_observables=True, bit_packed=True
            )
            truth = np.unpackbits(
                obs_packed, axis=1, count=circ.num_observables, bitorder="little"
            )
            model = Mechanisms.from_dem(circ.detector_error_model())

            dec_st = IsolatedNativeDecoder(model, reference=False)
            pred_st_sub = dec_st.decode(packed)
            st_sub_errs = int(np.count_nonzero(np.any(pred_st_sub != truth, axis=1)))

            ldpc_res = run_ldpc_anchor(
                model, packed, truth, order=2, workers=args.ldpc_workers
            )
            ldpc_res["per_round_ler"] = per_round_ler(
                ldpc_res["frame_ler"], spec.rounds
            )
            ldpc_res["paired_spacetime_errors_same_slice"] = st_sub_errs
            for pt in point_map[key]:
                if abs(pt["p"] - p) < 1e-12:
                    pt["arms"]["ldpc_bposd_cs2_anchor"] = ldpc_res
                    break
            print(
                f"  [ldpc CS2] {key:22s} p={p:.5f} shots={args.ldpc_shots:4d} -> "
                f"{ldpc_res['errors']:3d} err (paired SpaceTime: {st_sub_errs:3d} err), "
                f"{ldpc_res['us_per_shot']:9.1f} us/shot",
                flush=True,
            )

    stage1_10k = collect_stage1_receipts()
    _write_payload(args.output, suite, point_map, stage1_10k, cpp_wall_s, t_start)
    print(f"Wrote {args.output} ({args.output.stat().st_size} bytes).", flush=True)


if __name__ == "__main__":
    main()
