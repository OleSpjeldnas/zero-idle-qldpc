"""Paired Stim memory experiment. Checkpoint each completed arm atomically."""

import argparse
import hashlib
import json
from pathlib import Path
import os
import platform
import sys
import time
from importlib.metadata import version

import numpy as np
from stock_ldpc import decode as stock_decode
import stim


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "python"))
from zero_idle_qldpc.decoder import Mechanisms, SpaceTimeDecoder


def digest(data):
    return hashlib.sha256(data).hexdigest()


def save(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(obj, indent=2) + "\n")
    tmp.replace(path)


def samples(path, shots):
    raw = path.read_bytes()
    circuit = stim.Circuit(raw.decode())
    seed = int(digest(path.name.encode())[:15], 16)
    sampler = circuit.compile_detector_sampler(seed=seed)
    packed, obs = sampler.sample(shots, separate_observables=True, bit_packed=True)
    truth = np.unpackbits(obs, axis=1, count=circuit.num_observables, bitorder="little")
    return (
        circuit,
        packed,
        truth,
        dict(
            circuit=path.name,
            shots=shots,
            seed=seed,
            circuit_sha256=digest(raw),
            syndrome_sha256=digest(packed),
            truth_sha256=digest(truth),
        ),
    )


def measure(name, model, packed, truth, workers, checkpoint=None):
    if name.startswith("ldpc"):
        pred, stats = stock_decode(model, packed, int(name[-1]), workers, checkpoint)
        return dict(
            **stats,
            errors=int(np.any(pred != truth, axis=1).sum()),
            prediction_sha256=digest(pred),
        )
    start = time.perf_counter()
    dec = SpaceTimeDecoder(model, reference=name == "reference")
    setup = time.perf_counter() - start
    start = time.process_time()
    if name == "scalar":
        pred = np.stack([dec.decode(row) for row in packed])
    elif name == "batch":
        perm = np.random.default_rng(6721).permutation(len(packed))
        pred = np.empty_like(truth)
        pred[perm] = dec.decode(packed[perm])
    else:
        pred = dec.decode(packed)
    elapsed = time.process_time() - start
    return dict(
        errors=int(np.count_nonzero(np.any(pred != truth, axis=1))),
        setup_s=setup,
        decode_cpu_s=elapsed,
        us_per_shot=1e6 * elapsed / len(packed),
        prediction_sha256=digest(pred),
    )


ARMS = ("ldpc2", "ldpc7", "reference", "scalar", "batch")


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--quick", action="store_true")
    mode.add_argument("--full", action="store_true")
    parser.add_argument(
        "--resume", action="store_true", help="reuse completed matching receipts"
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=min(os.cpu_count() or 1, 8),
        help="stock ldpc single-threaded workers per full circuit",
    )
    parser.add_argument(
        "--arm",
        choices=ARMS,
        action="append",
        help="run selected arms and retain receipts",
    )
    parser.add_argument("--circuit", help="run one named .stim file")
    args = parser.parse_args()
    if args.workers < 1:
        parser.error("workers must be positive")
    mode = "quick" if args.quick else "full"
    paths = sorted(
        (ROOT / "circuits").glob("*.stim"),
        key=lambda p: (p.name.startswith("ibm"), p.name),
    )
    shots = 4 if args.quick else 10000
    if args.quick:
        paths = [
            p
            for p in paths
            if p.name
            in (
                "n56-r4-p0.002.stim",
                "n60-nonabelian-r4-p0.002.stim",
                "ibm72-published-r4-p0.002.stim",
            )
        ]
    if args.circuit:
        paths = [p for p in paths if p.name == args.circuit]
        if not paths:
            parser.error("unknown circuit")
    versions = {k: version(k) for k in ("numpy", "scipy", "stim", "ldpc")}
    binary_sha = digest((ROOT / "build/libqldpc.so").read_bytes())
    results = dict(
        mode=mode,
        platform=platform.platform(),
        versions=versions,
        build_sha256=binary_sha,
        rows=[],
    )
    out = ROOT / "benchmarks" / "results" / f"{mode}_benchmark.json"
    print(
        "| Circuit | Shots | ldpc CS2 | ldpc CS7 | C++ CS2 | Scalar | Shuffled batch |",
        flush=True,
    )
    print("|---|---:|---:|---:|---:|---:|---:|")
    partial = bool(args.arm or args.circuit)
    for path in paths:
        c, packed, truth, row = samples(path, shots)
        model = Mechanisms.from_dem(c.detector_error_model())
        row.update(
            detectors=model.detectors, mechanisms=len(model.probabilities), arms={}
        )
        for name in args.arm or ARMS:
            ident = dict(
                arm=name,
                syndrome=row["syndrome_sha256"],
                circuit=row["circuit_sha256"],
                runner=digest(
                    Path(__file__).read_bytes()
                    + (ROOT / "benchmarks/stock_ldpc.py").read_bytes()
                ),
                versions=versions,
                binary=binary_sha if not name.startswith("ldpc") else None,
            )
            ck = ROOT / "build" / "receipts" / mode / (path.stem + "-" + name + ".json")
            receipt = json.loads(ck.read_text()) if args.resume and ck.exists() else {}
            if ident != receipt.get("id"):
                checkpoint = None
                if args.full:
                    run_id = digest(json.dumps(ident, sort_keys=True).encode())[:20]
                    checkpoint = (
                        ROOT / "build" / "blocks" / run_id if args.resume else None
                    )
                data = measure(
                    name,
                    model,
                    packed,
                    truth,
                    args.workers if args.full else 1,
                    checkpoint,
                )
                save(ck, dict(id=ident, measurement=data))
            else:
                data = receipt["measurement"]
            row["arms"][name] = data
        if partial:
            for key, value in row["arms"].items():
                print(path.name, key, value, flush=True)
            continue
        if (
            row["arms"]["scalar"]["prediction_sha256"]
            != row["arms"]["batch"]["prediction_sha256"]
        ):
            raise RuntimeError(f"Scalar/batch disagreement on {path}")
        row["scalar_batch_disagreements"] = 0
        results["rows"].append(row)
        print(
            "|",
            path.stem,
            "|",
            shots,
            "|",
            " | ".join(
                f"{d['errors']} / {d['us_per_shot']:.1f} µs"
                for d in row["arms"].values()
            ),
            "|",
            flush=True,
        )
        save(out.with_suffix(".partial.json"), results)
    if partial:
        return
    save(out, results)
    out.with_suffix(".partial.json").unlink(missing_ok=True)


if __name__ == "__main__":
    main()
