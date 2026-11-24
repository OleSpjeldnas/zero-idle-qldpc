# Eliminating the Idle CNOT Barrier and Decoding Bottleneck in Weight-Six Two-Block Quantum LDPC Memories

## Abstract

High-rate two-block quantum low-density parity-check (qLDPC) codes—exemplified by bivariate bicycle (BB) memories such as the `[[72, 12, 6]]` and `[[144, 12, 12]]` Gross codes—reduce physical qubit overhead by up to an order of magnitude relative to planar surface codes while maintaining weight-six checks and degree-six qubit connectivity. Transitioning these codes into low-latency fault-tolerant operation faces two coupled bottlenecks. **First, on the quantum circuit side**, every universal shift-homogeneous CNOT schedule for a symmetric $(3, 3)$ two-block code requires at least $T_{\text{CNOT}} \ge 7$ entangling steps, imposing mandatory idle decoherence slots each syndrome cycle while risking mid-cycle hook-error distance collapse ($d \to d/2$) under unscreened gate orderings. **Second, on the classical inference side**, circuit-level detector error models (DEMs) contain $10^4\text{–}10^5$ correlated fault mechanisms whose symmetric weight-$\lceil d/2 \rceil$ quantum degeneracies stall belief propagation (`BP`) and force millisecond-to-second ordered statistics decoding (`OSD`).

Here we resolve both bottlenecks within a self-contained, formally verified synthesis and decoding stack (**[`docs/technical_note.md`](docs/technical_note.md)**):

1. **Zero-Idle $T_{\text{CNOT}} = 6$ Circuit Co-Design (`proofs/`, `cpp/src/synthesizer.cpp`).** We prove an exact biorder inversion-parity identity ($2N = w_A w_B$ at $T = w_A + w_B$) establishing why symmetric $(3, 3)$ schedules cannot achieve $T_{\text{CNOT}} = 6$ ($3 \times 3 = 9$ is odd), and show that **asymmetric $(4, 2)$ two-block group-algebra (`2BGA`) codes** ($4 \times 2 = 8$) achieve **$100\%$ CNOT-layer occupancy at $T_{\text{CNOT}} = 6$** while preserving check weight 6, qubit degree 6, verified Z-memory fault distance $d_Z = 6$, and **thickness-2 bilayer planar routability**. Paired with a Lean-certified **90-class hook-equivalence canonicalizer** (and non-abelian `2BGA` lifts where cyclic abelian tori suffer two-phase hook collapse), zero-idle $(4, 2)$ schedules reduce 4-round logical error rates at $p = 2 \times 10^{-3}$ by **$12.4\times\text{–}17.0\times$** (`4/5,000` vs `68/5,000` on `n = 56`; `5/5,000` vs `62/5,000` on `n = 84`; and `0/5,000` vs `35/5,000` on `n = 96`, with $21.2\times$ at $p = 3 \times 10^{-3}$) relative to serialized extraction.
2. **Microsecond Certified + Active-Conflict Space-Time Decoding (`cpp/src/spacetime_decoder.cpp`).** We introduce `SpaceTimeDecoder`, a single-shot ($N = 1$), zero-heap-allocation C++17 decoder that places **Lean-certified 1-, 2-, and 3-fault global minimum-weight fast paths** ahead of alternating-direction SIMD min-sum BP and incremental active-conflict `OSD` (restricting higher-order combinations to columns overlapping the active pivot support). Across 22 exported `Stim` Z-memory circuits—including **drop-in decoding of IBM's published `[[72, 12, 6]]` and `[[144, 12, 12]]` Gross circuits**—`SpaceTimeDecoder` reduces frame errors by **$2.8\times\text{–}15.1\times$** at $p = 2 \times 10^{-3}$ while running **$16\times\text{–}102\times$ faster** in mean CPU time than C++17 `BP+OSD-CS` (**$2{,}071\times\text{–}9{,}148\times$ faster** than Python/Cython `ldpc.BpOsdDecoder`). At $p = 10^{-3}$, single-shot wall-clock medians (`p50`) span **$8.1\text{–}33.0\ \mu\text{s}$** and 99th-percentile (`p99`) latencies span **$70.7\text{–}157.3\ \mu\text{s}$** across the four benchmarked flagship 4-round memories (`n84`, `n96`, `ibm72-published`, and `ibm144-published`) on a single CPU core.

---

## Why This Matters for Quantum Hardware & Decoding Teams

- **Free CNOT-depth compression without extra layers or check weight:** Breaking $(3, 3) \to (4, 2)$ block symmetry eliminates the mandatory CNOT idle tick ($T = 7 \to 6$), keeps every check weight-6 and every qubit degree-6, and still decomposes into two planar degree-3 routing layers (`python/zero_idle_qldpc/layout.py`).
- **Immediate drop-in decoder gains on existing `(3, 3)` Gross roadmaps:** Without changing a single wire of IBM's published `[[72, 12, 6]]` or `[[144, 12, 12]]` Gross circuits, `SpaceTimeDecoder` decodes 4-round memories at $p = 10^{-3}$ in **`8.1 µs` (`p50`) / `88.4 µs` (`p99`)** and **`33.0 µs` (`p50`) / `157.3 µs` (`p99`)** wall-clock per shot with zero dynamic memory allocations—and decodes 12-round `[[144, 12, 12]]` ($D = 1{,}728, M = 67{,}752$) in **`124.5 µs` (`p50`) / `792.6 µs` (`p99`)**.
- **Designed for skeptical, zero-trust verification:** No claim relies on trusting our C++ synthesizer or benchmark harness. Every algebraic and certificate theorem compiles in **< 15 seconds in Lean 4 with zero Mathlib dependencies**, and every `.stim` circuit and fault distance is audited by standalone `Stim`-only scripts that import **zero** code from this package.

---

## Verify Every Claim in ~60 Seconds (Zero Trust Required)

Requires Python $\ge 3.10$, Make, and a C++17 compiler (`clang++` or `g++`). If [Lean 4 (`elan`)](https://lean-lang.org/lean4/doc/setup.html) is installed (`~/.elan/bin/lake`), `make verify` also kernel-checks all formal proofs from source:

```sh
python3 -m venv .venv
.venv/bin/pip install -e .
make verify
```

Each verification layer can also be audited independently:

| Verification Layer | Command | What It Checks Independently |
|---|---|---|
| **1. Formal Proofs (`Lean 4.36.0`)** | `make proofs` *(or `cd proofs && lake build && lake exe verify-proofs`)* | Kernel-checks all 4 proof modules (`26` headline theorems & witnesses, `0` external deps, `0` `sorry`s, `0` `native_decide` axioms, `~14 s` cold build). |
| **2. Zero-Trust `Stim` Circuit & Distance Audit** | `.venv/bin/python3 verification/verify_circuits.py && .venv/bin/python3 verification/verify_distances.py` | `149`-line `Stim`+`NumPy` checker (`0` imports from `zero_idle_qldpc`) verifying $H_X H_Z^T = 0$, tick collision-freeness, Heisenberg pullback, DEM determinism, and tight multi-round Z-memory distances ($d_Z \in \{6, 7, 10\}$ across all 22 `.stim` files, including $d_Z = 10$ on 4- and 12-round `[[144, 12, 12]]` Gross). |
| **3. Native Oracle, External `ldpc` & Tail-Latency Benchmarks** | `make test && make benchmark-quick && make tail-latency` *(full `10k`-shot suite: `make benchmark-full`)* | Runs `tests/native.cpp` (`0` native heap allocations on scalar calls) + `tests/test_package.py` (`24/24` permutations of the 4-mechanism `3.0 vs 2.7` counterexample & bit-identical scalar vs shuffled-batch checks), head-to-head parity against Roffe's `ldpc.BpOsdDecoder`, and single-shot `p50`/`p99` wall-clock percentiles. |

---

## Visual Overview

<p align="center">
  <img src="docs/figures/waterfall_ler.svg" alt="Multi-p Logical Error Rate Waterfall: Circuit Co-Design and Fixed-Circuit Drop-In Decoding" width="100%">
</p>

<p align="center">
  <img src="docs/figures/latency_accuracy_pareto.svg" alt="Mean Single-Shot Decode CPU Time vs Logical Error Rate at p = 0.002" width="92%">
</p>

---

## Repository Structure

```text
zero-idle-qldpc/
├── proofs/                   # Lean 4 (v4.36.0) formal proofs (Init/Std only, 0 Mathlib deps, 0 sorrys)
│   └── ZeroIdleQldpc/        # BimoduleCSS, ParityBarrier, HookClasses90, CertifiedDecoder, CheckAxioms
├── verification/             # Zero-trust Stim-only circuit & fault-distance checkers (0 package imports)
│   ├── verify_circuits.py    # 149-line standalone CSS, tick-collision, Heisenberg & Stim witness audit
│   ├── verify_distances.py   # Parity-projected exhaustive Z-memory fault-distance lower/upper bounds
│   ├── gross_distance.py     # Torus-orbit exhaustive d_Z = 10 verifier for 144-qubit Gross circuits
│   └── faults.json           # Explicit physical fault witnesses on exported circuits
├── circuits/                 # 22 standard noisy Z-memory .stim files & bilayer planar layout JSONs
├── cpp/                      # Dependency-free C++17 library (0 per-shot heap allocations)
│   ├── include/qldpc/        # C/C++ headers (code.hpp, synthesizer.h, decoder.h)
│   └── src/                  # synthesizer.cpp, spacetime_decoder.cpp, min_sum.hpp, bposd.cpp
├── python/zero_idle_qldpc/   # Installable Python API (ZeroIdleSynthesizer, SpaceTimeDecoder, layout.py)
├── benchmarks/               # Paired ldpc.BpOsdDecoder, waterfall & p50/p99 tail-latency runners + JSONs
├── docs/                     # Full technical note (technical_note.md) & vector figures (figures/*.svg)
└── tests/                    # Native C++ allocation/oracle tests (native.cpp) & Python unit tests
```

---

## Machine-Checked Formal Theorems (`proofs/`)

All proofs use core Lean 4 (`Init`/`Std` only) and are audited in [`proofs/ZeroIdleQldpc/CheckAxioms.lean`](proofs/ZeroIdleQldpc/CheckAxioms.lean) to depend solely on standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`):

| Module | Principal Theorems & Constructive Witnesses | Physical / Algorithmic Consequence |
|---|---|---|
| [`BimoduleCSS.lean`](proofs/ZeroIdleQldpc/BimoduleCSS.lean) | `left_right_comm` *(0 axioms)*, `css_orthogonality`, `s3_css_witness` | Left translations $L(A)$ commute with right translations $R(B)$ over *any* finite group $G$ (commutative or non-abelian), guaranteeing $H_X H_Z^T = 0 \pmod 2$. |
| [`ParityBarrier.lean`](proofs/ZeroIdleQldpc/ParityBarrier.lean) | `zero_idle_inversion_double_eq_prod`, `no_symmetric_3_3_depth_6`, `zero_idle_4_2_depth_6`, `symmetric_3_3_tight_min_depth_7` | Proves $2N = w_A w_B$ at $T = w_A + w_B$: symmetric $(3, 3)$ schedules cannot achieve $T = 6$ ($9$ is odd; $T = 7$ is tight), whereas $(4, 2)$ achieves $100\%$ active zero-idle $T = 6$. |
| [`HookClasses90.lean`](proofs/ZeroIdleQldpc/HookClasses90.lean) | `bare_hook_classes_eq_360`, `augmented_hook_classes_eq_90`, `coset90_key_sound_and_complete` | Over all $6! = 720$ gate orders of a weight-6 check, bare suffix hooks form `360` coset classes, collapsing to `90` exact reversal-coupled classes once single-qubit data faults are adjoined. |
| [`CertifiedDecoder.lean`](proofs/ZeroIdleQldpc/CertifiedDecoder.lean) | `kSmallestSum_le_subsetWeight`, `path1/2/3_certified_map`, `counterexample_30_vs_27_restricted_slack_fails` | Proves Paths 1–3 (`< pair_floor`, `< triple_floor`, `< four_floor` with unique observable) return the strict global minimum-weight explanation across all $2^M$ subsets, and proves why slack-gated local tiles fail (`30 vs 9+9+9=27`). |

---

## Empirical Benchmarks

### 1. Circuit-Level Logical Error Rate & Mean CPU Time (`10,000` Shots per `.stim` Circuit)

Within every row, C++17 `BP+OSD-CS`, scalar `SpaceTimeDecoder`, and shuffled-batch `SpaceTimeDecoder` decode **byte-identical `10,000`-shot `Stim` syndromes** ([`benchmarks/results/full_benchmark.json`](benchmarks/results/full_benchmark.json)), with zero disagreements between scalar and shuffled-batch calls across all `220,000` shots. `ldpc.BpOsdDecoder` also decodes those exact `10,000` syndromes on every row except the two `†` rows (`ibm72-r4` and `ibm144-r4`), which report `500`-shot waterfall anchors alongside matched-slice `SpaceTimeDecoder` (`ST`) counts.

| Exported Circuit | Parameters & Schedule | $d_Z$ | `ldpc.BpOsdDecoder` (`OSD-CS`) | C++17 `BP+OSD-CS` (`10k`) | `SpaceTimeDecoder` (`10k` Scalar / Batch) |
|---|---|---:|---:|---:|---:|
| `n56-r4-p0.001` | `[[56,6,6]]` $(4,2)$ `T=6` | 6 | 2 err / 42,461 µs | 4 err / 787.5 µs | **2 err / 13.2 µs** *(9.3 µs)* |
| `n56-r4-p0.002` | `[[56,6,6]]` $(4,2)$ `T=6` | 6 | 8 err / 88,414 µs | 34 err / 1,176.0 µs | **12 err / 42.7 µs** *(34.0 µs)* |
| `n84-r4-p0.001` | `[[84,8,6]]` $(4,2)$ `T=6` | 6 | 0 err / 91,241 µs | 0 err / 1,137.3 µs | **0 err / 18.6 µs** *(14.2 µs)* |
| `n84-r4-p0.002` | `[[84,8,6]]` $(4,2)$ `T=6` | 6 | 5 err / 181,038 µs | 28 err / 2,001.1 µs | **8 err / 61.0 µs** *(51.5 µs)* |
| `n96-r4-p0.001` | `[[96,8,6]]` $(4,2)$ `T=6` | 6 | 0 err / 130,882 µs | 0 err / 1,610.1 µs | **0 err / 24.2 µs** *(20.2 µs)* |
| `n96-r4-p0.002` | `[[96,8,6]]` $(4,2)$ `T=6` | 6 | 7 err / 315,690 µs | 5 err / 2,700.1 µs | **1 err / 75.0 µs** *(63.8 µs)* |
| `n60-nonabelian-r4-p0.002` | `[[60,8,6]]` $\mathbb{Z}_5 \rtimes_4 \mathbb{Z}_6$ `T=7` | 6 | 18 err / 154,390 µs | 71 err / 1,633.7 µs | **16 err / 54.2 µs** *(49.7 µs)* |
| `n70-r4-p0.002` | `[[70,6,8]]` $\mathbb{Z}_7 \times \mathbb{Z}_5$ `T=10` | 7 | 32 err / 418,348 µs | 242 err / 2,686.8 µs | **16 err / 168.6 µs** *(160.1 µs)* |
| `ibm72-published-r4-p0.002` | IBM `[[72,12,6]]` Gross `T=7` | 6 | 1/500 (`ST`: 1/500) / 207,161 µs† | 37 err / 2,669.1 µs | **7 err / 65.8 µs** *(46.4 µs)* |
| `ibm144-published-r4-p0.002` | IBM `[[144,12,12]]` Gross `r=4` | 10 | 0/500 (`ST`: 0/500) / 634,662 µs† | 0 err / 7,099.9 µs | **0 err / 177.0 µs** *(149.6 µs)* |
| `ibm144-published-r12-p0.001` | IBM `[[144,12,12]]` Gross `r=12` | 10 | 0 err / 2,219,422 µs | 0 err / 24,711.4 µs | **0 err / 242.6 µs** *(211.0 µs)* |
| `ibm144-published-r12-p0.002` | IBM `[[144,12,12]]` Gross `r=12` | 10 | >4 GB table† | 5 err / 29,820.4 µs | **0 err / 1,795.0 µs** *(1,857.0 µs)* |

*†Table 1 timings report mean single-thread CPU time (`time.process_time() / shots`). `ibm72-r4` and `ibm144-r4` `ldpc` entries come from `benchmarks/results/waterfall_results.json`'s independent 500-shot anchor sample (`ST` gives `SpaceTimeDecoder` on that identical 500-shot slice: `1/500` and `0/500`). On 12-round `ibm144` ($M = 67{,}752$), upstream `ldpc` `OSD-CS` materializes $>4\text{ GB}$ of trial strings per decoder.*

### 2. Per-Shot Wall-Clock Latency Distribution (`N = 1` Scalar Calls, `0` Heap Allocations)

Measured via `time.perf_counter_ns()` per individual `decoder.decode(row)` call across `10,000` shots (`make tail-latency`, [`benchmarks/results/tail_latency.json`](benchmarks/results/tail_latency.json), Apple Silicon single core):

| Exported Circuit | Physical Error Rate $p$ | Mean (µs) | Median `p50` (µs) | `p90` (µs) | `p99` (µs) | `p99.9` (µs) |
|---|---:|---:|---:|---:|---:|---:|
| `n84-r4` (`[[84,8,6]]` Zero-Idle `T=6`) | `0.001` | 19.8 | **15.7** | 38.8 | **70.7** | 194.7 |
| `n96-r4` (`[[96,8,6]]` Zero-Idle `T=6`) | `0.001` | 24.1 | **24.0** | 42.5 | **80.3** | 248.8 |
| `ibm72-published-r4` (IBM `[[72,12,6]]`) | `0.001` | 18.5 | **8.1** | 40.1 | **88.4** | 197.8 |
| `ibm144-published-r4` (IBM `[[144,12,12]]` `r=4`) | `0.001` | 36.9 | **33.0** | 57.9 | **157.3** | 386.8 |
| `ibm144-published-r12` (IBM `[[144,12,12]]` `r=12`) | `0.001` | 197.2 | **124.5** | 462.0 | **792.6** | 5046.8 |
| `n84-r4` (`[[84,8,6]]` Zero-Idle `T=6`) | `0.002` | 53.3 | **39.0** | 65.9 | **371.5** | 1151.0 |
| `ibm72-published-r4` (IBM `[[72,12,6]]`) | `0.002` | 45.9 | **34.4** | 63.3 | **272.3** | 1205.9 |
| `ibm144-published-r4` (IBM `[[144,12,12]]` `r=4`) | `0.002` | 141.9 | **71.5** | 327.8 | **1759.5** | 2295.8 |

### 3. Thickness-2 Bilayer Planar Routing (`python/zero_idle_qldpc/layout.py`)

Every $(4, 2)$ zero-idle code retains check weight 6 and qubit degree 6, and partitions its six bipartite matchings into **two verified planar 3-regular subgraphs** (`2A + 1B` in Layer 1; the remaining three in Layer 2, with clockwise planar rotation systems exported in `circuits/*.json`):

| Blocklength $n$ | Layer 1 Grid (mean / max) | Layer 1 Torus (mean / max) | Layer 2 Grid (mean / max) | Layer 2 Torus (mean / max) |
|---:|---:|---:|---:|---:|
| `56` | `10.57 / 19` | `9.00 / 13` | `6.19 / 27` | `5.00 / 13` |
| `84` | `1.65 / 83` | `1.00 / 1` | `19.46 / 79` | `11.67 / 17` |
| `96` | `2.00 / 7` | `1.67 / 3` | `12.39 / 25` | `9.67 / 13` |

---

## Minimal Python API

After `pip install -e .` and `make build`:

```python
import stim
from zero_idle_qldpc import SpaceTimeDecoder, ZeroIdleSynthesizer

# 1. Synthesize a cyclic (4,2) zero-idle T=6 [[84, 8, 6]] code (~6 ms)
code = ZeroIdleSynthesizer().cyclic(n=84, k=8, distance=6)

# 2. Drop-in causal N=1 decoding on any Stim circuit / DetectorErrorModel (D <= 2048, K <= 64)
circuit = stim.Circuit.from_file("circuits/ibm144-published-r12-p0.001.stim")
decoder = SpaceTimeDecoder(circuit.detector_error_model())
shots = circuit.compile_detector_sampler(seed=102).sample(100, bit_packed=True)

frames = decoder.decode(shots)       # shape (100, 12), uint8
single = decoder.decode(shots[0])    # shape (12,), 0 native heap allocs, bit-identical to batch
```

For the full mathematical derivations, the 4-mechanism blind-review counterexample, and decoder ablation analysis, see **[`docs/technical_note.md`](docs/technical_note.md)**.

---

## Scope & Modeling Assumptions

- **CNOT layers vs SPAM ticks:** Zero-idle $T_{\text{CNOT}} = 6$ refers to the six entangling CNOT layers of the $(4, 2)$ schedules ($100\%$ qubit occupancy in every CNOT tick). Exported non-overlapped Z-memory `.stim` circuits (`n56`, `n84`, `n96`, `n60-*`, `n70`, `ibm72-t7/t9`) include explicit ancilla reset/readout ticks with `DEPOLARIZE1(p)` on data qubits; `ibm72-published` and `ibm144-published` follow Bravyi et al. ([*Nature* 2024](https://doi.org/10.1038/s41586-024-07107-7)) by overlapping X-preparation and Z-measurement onto the first and seventh CNOT ticks.
- **Evaluated memory sector & noise model:** All 22 `.stim` files benchmark Z-basis memory under standard circuit-level depolarizing noise (`DEPOLARIZE2(p)` on CNOTs, `DEPOLARIZE1(p)` on idle qubits, `X_ERROR(p)`/`Z_ERROR(p)` on resets/readouts). On `n60-nonabelian`, the verified multi-round Z-memory distance is $d_Z = 6$ while the single-round X-sector hook proxy is 4; `n60-archive` attains 6 in both sectors at $T = 7$. Physical hardware crosstalk, leakage, and FPGA/ASIC deterministic worst-case clock closure require device-specific characterization.
- **Certified vs heuristic decoding stages:** Paths 1, 2, and 3 in `SpaceTimeDecoder` certify strict global minimum additive-LLR optimality over clamped `float32` weights when their cost-floor and unique-observable conditions hold (`CertifiedDecoder.lean`). Subsequent local RREF, peel/beam, min-sum BP, and active-conflict `OSD` stages are bounded heuristics.
