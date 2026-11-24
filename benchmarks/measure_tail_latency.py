#!/usr/bin/env python3
"""Measure single-shot (N = 1) wall-clock latency percentiles (mean, p50, p90, p99, p99.9).

Each call invokes SpaceTimeDecoder.decode(row) on a single packed syndrome row with zero
native heap allocations, recording per-shot wall-clock duration via time.perf_counter_ns().
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import platform
import sys
import time

import numpy as np
import stim

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "python") not in sys.path:
    sys.path.insert(0, str(ROOT / "python"))

from zero_idle_qldpc import SpaceTimeDecoder  # noqa: E402

DEFAULT_CIRCUITS = (
    "n84-r4-p0.001.stim",
    "n84-r4-p0.002.stim",
    "n96-r4-p0.001.stim",
    "n96-r4-p0.002.stim",
    "ibm72-published-r4-p0.001.stim",
    "ibm72-published-r4-p0.002.stim",
    "ibm144-published-r4-p0.001.stim",
    "ibm144-published-r4-p0.002.stim",
    "ibm144-published-r12-p0.001.stim",
)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--shots", type=int, default=10000)
    ap.add_argument("--seed", type=int, default=424242)
    ap.add_argument(
        "--output",
        type=Path,
        default=ROOT / "benchmarks" / "results" / "tail_latency.json",
    )
    args = ap.parse_args()

    rows = []
    print(
        "| Circuit | Shots | Mean (µs) | p50 (µs) | p90 (µs) | p99 (µs) | p99.9 (µs) |",
        flush=True,
    )
    print("|---|---:|---:|---:|---:|---:|---:|")
    for cname in DEFAULT_CIRCUITS:
        c = stim.Circuit.from_file(str(ROOT / "circuits" / cname))
        dec = SpaceTimeDecoder(c.detector_error_model())
        packed = c.compile_detector_sampler(seed=args.seed).sample(
            args.shots, bit_packed=True
        )
        for i in range(min(32, len(packed))):
            dec.decode(packed[i])
        lat_us = np.empty(args.shots, dtype=np.float64)
        for i in range(args.shots):
            t0 = time.perf_counter_ns()
            dec.decode(packed[i])
            lat_us[i] = (time.perf_counter_ns() - t0) * 1e-3
        rec = {
            "circuit": cname,
            "shots": args.shots,
            "seed": args.seed,
            "mean_wall_us": round(float(lat_us.mean()), 2),
            "p50_wall_us": round(float(np.percentile(lat_us, 50)), 2),
            "p90_wall_us": round(float(np.percentile(lat_us, 90)), 2),
            "p99_wall_us": round(float(np.percentile(lat_us, 99)), 2),
            "p999_wall_us": round(float(np.percentile(lat_us, 99.9)), 2),
        }
        rows.append(rec)
        print(
            f"| `{cname}` | {args.shots:,} | {rec['mean_wall_us']:.1f} | "
            f"{rec['p50_wall_us']:.1f} | {rec['p90_wall_us']:.1f} | "
            f"{rec['p99_wall_us']:.1f} | {rec['p999_wall_us']:.1f} |",
            flush=True,
        )

    payload = {
        "platform": platform.platform(),
        "metric": "single_shot_wall_clock_perf_counter_ns",
        "rows": rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n")


if __name__ == "__main__":
    main()
