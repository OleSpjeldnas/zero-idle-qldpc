/-
  ZeroIdleQldpc.CheckAxioms
  =========================
  Compile-time foundational audit across all four formal modules.
  Verifies that every proved theorem relies ONLY on Lean 4's standard
  foundational principles (`propext`, `Classical.choice`, `Quot.sound`)
  with zero unproved holes and zero compiler-trusted `Lean.ofReduceBool`.
-/
import ZeroIdleQldpc.BimoduleCSS
import ZeroIdleQldpc.ParityBarrier
import ZeroIdleQldpc.HookClasses90
import ZeroIdleQldpc.CertifiedDecoder

-- 1. BimoduleCSS
#print axioms ZeroIdleQldpc.BimoduleCSS.left_right_comm
#print axioms ZeroIdleQldpc.BimoduleCSS.css_orthogonality
#print axioms ZeroIdleQldpc.BimoduleCSS.css_orthogonality_list
#print axioms ZeroIdleQldpc.BimoduleCSS.s3_non_abelian
#print axioms ZeroIdleQldpc.BimoduleCSS.s3_css_witness

-- 2. ParityBarrier
#print axioms ZeroIdleQldpc.ParityBarrier.schedule_depth_ge_weight
#print axioms ZeroIdleQldpc.ParityBarrier.zero_idle_inversion_double_eq_prod
#print axioms ZeroIdleQldpc.ParityBarrier.no_symmetric_3_3_depth_6
#print axioms ZeroIdleQldpc.ParityBarrier.zero_idle_4_2_depth_6
#print axioms ZeroIdleQldpc.ParityBarrier.zero_idle_4_2_all_ticks_active
#print axioms ZeroIdleQldpc.ParityBarrier.mirror_3_3_depth_7
#print axioms ZeroIdleQldpc.ParityBarrier.symmetric_3_3_tight_min_depth_7

-- 3. HookClasses90
#print axioms ZeroIdleQldpc.HookClasses90.canonCoset_eq_iff
#print axioms ZeroIdleQldpc.HookClasses90.total_perms6_eq_720
#print axioms ZeroIdleQldpc.HookClasses90.bare_hook_classes_eq_360
#print axioms ZeroIdleQldpc.HookClasses90.bare_hook_eq_iff_canonBarePerm_eq
#print axioms ZeroIdleQldpc.HookClasses90.augmented_hook_classes_eq_90
#print axioms ZeroIdleQldpc.HookClasses90.coset90_key_sound_and_complete

-- 4. CertifiedDecoder
#print axioms ZeroIdleQldpc.CertifiedDecoder.kSmallestSum_le_subsetWeight
#print axioms ZeroIdleQldpc.CertifiedDecoder.path1_strict_singleton_optimal
#print axioms ZeroIdleQldpc.CertifiedDecoder.path1_certified_map
#print axioms ZeroIdleQldpc.CertifiedDecoder.pair_anchor_complete
#print axioms ZeroIdleQldpc.CertifiedDecoder.path2_certified_map
#print axioms ZeroIdleQldpc.CertifiedDecoder.triple_anchor_pivot_complete
#print axioms ZeroIdleQldpc.CertifiedDecoder.path3_certified_map
#print axioms ZeroIdleQldpc.CertifiedDecoder.counterexample_30_vs_27_restricted_slack_fails
