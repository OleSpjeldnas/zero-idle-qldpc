# Zero-Idle qLDPC — Formal Proofs in Lean 4 (`v4.36.0`)

Zero-external-dependency formal verification package (`Init` / `Std` only — no Mathlib download required) proving the four algebraic, scheduling, hook-equivalence, and decoder-optimality theorems underlying `zero-idle-qldpc`.

## Quick Verification

```sh
lake clean
time lake build
lake exe verify-proofs
```

Every theorem is checked by the standard Lean 4 kernel with `0` occurrences of `sorry`, `admit`, custom `axiom`, or `native_decide` (`Lean.ofReduceBool`).

## Module Map

| Module | Proved Results | Corresponding Code |
|---|---|---|
| `ZeroIdleQldpc/BimoduleCSS.lean` | `left_right_comm`, `css_orthogonality`, `css_orthogonality_list`, non-abelian `S3` witness (`s3_non_abelian`, `s3_css_witness`) | `cpp/src/synthesizer.cpp` (`build_2bga_hx_hz`) |
| `ZeroIdleQldpc/ParityBarrier.lean` | `schedule_depth_ge_weight`, `zero_idle_inversion_double_eq_prod` (`2 * N = w_A * w_B`), `no_symmetric_3_3_depth_6`, `zero_idle_4_2_depth_6` + `zero_idle_4_2_all_ticks_active`, `mirror_3_3_depth_7`, `symmetric_3_3_tight_min_depth_7` | `cpp/src/synthesizer.cpp` (`balanced_ticks`), `python/zero_idle_qldpc/synthesizer.py` (`T6`, `T7`) |
| `ZeroIdleQldpc/HookClasses90.lean` | `canonCoset_eq_iff`, `total_perms6_eq_720`, `bare_hook_classes_eq_360`, `bare_hook_eq_iff_canonBarePerm_eq`, `augmented_hook_classes_eq_90`, `coset90_key_sound_and_complete` | `python/zero_idle_qldpc/synthesizer.py` (`search_seven`) |
| `ZeroIdleQldpc/CertifiedDecoder.lean` | `kSmallestSum_le_subsetWeight`, `path1_strict_singleton_optimal`, `path1_certified_map`, `pair_anchor_complete`, `path2_certified_map`, `triple_anchor_pivot_complete`, `path3_certified_map`, `counterexample_30_vs_27_restricted_slack_fails` | `cpp/src/spacetime_decoder.cpp` (`low_weight`, `quick_osd`), `tests/test_package.py` (`test_minimum_cost_triple`) |
| `ZeroIdleQldpc/CheckAxioms.lean` | `#print axioms` audit across all exported theorems | `Main.lean` (`verify-proofs`) |
