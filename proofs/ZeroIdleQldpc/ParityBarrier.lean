/-
  ZeroIdleQldpc.ParityBarrier
  ===========================
  Formal verification of universal shift-homogeneous `(w_A, w_B)` 2-block CSS
  CNOT schedules over `Fin T`:
    1. Tick-collision freedom on X-ancillas, Z-ancillas, L-data qubits, and R-data qubits,
    2. Universal paired Heisenberg stabilizer commutation:
         ∀ i j, decide (tA i < tBT j) = decide (tB j < tAT i),
    3. General zero-idle inversion-parity identity (`2 * inversionCount = w_A * w_B`
       at `T = w_A + w_B`), proving `no_symmetric_3_3_depth_6` (`3 * 3 = 9` is odd!)
       and `no_symmetric_3_3_depth_lt_7`,
    4. Constructive zero-idle `(4, 2)` witness at `T = 6` (`zero_idle_4_2_depth_6`)
       with 100% qubit activity across all 6 ticks, and
    5. Constructive mirror `(3, 3)` witness at `T = 7` (`mirror_3_3_depth_7`),
       establishing `T = 7` as the exact minimum depth for universal `(3, 3)` schedules.
-/

namespace ZeroIdleQldpc.ParityBarrier

/-- A universal shift-homogeneous `(wA, wB)` 2-block CNOT schedule in `T` ticks.
    - `tA`  : X-check → L-data CNOT ticks (`wA` wires)
    - `tB`  : X-check → R-data CNOT ticks (`wB` wires)
    - `tBT` : L-data → Z-check CNOT ticks (`wB` wires)
    - `tAT` : R-data → Z-check CNOT ticks (`wA` wires) -/
structure ValidBiorderSchedule (wA wB T : Nat) where
  tA  : Fin wA → Fin T
  tB  : Fin wB → Fin T
  tBT : Fin wB → Fin T
  tAT : Fin wA → Fin T
  tA_inj  : ∀ i₁ i₂ : Fin wA, tA i₁ = tA i₂ → i₁ = i₂
  tB_inj  : ∀ j₁ j₂ : Fin wB, tB j₁ = tB j₂ → j₁ = j₂
  tBT_inj : ∀ j₁ j₂ : Fin wB, tBT j₁ = tBT j₂ → j₁ = j₂
  tAT_inj : ∀ i₁ i₂ : Fin wA, tAT i₁ = tAT i₂ → i₁ = i₂
  x_anc_disjoint  : ∀ (i : Fin wA) (j : Fin wB), tA i ≠ tB j
  z_anc_disjoint  : ∀ (j : Fin wB) (i : Fin wA), tBT j ≠ tAT i
  l_data_disjoint : ∀ (i : Fin wA) (j : Fin wB), tA i ≠ tBT j
  r_data_disjoint : ∀ (j : Fin wB) (i : Fin wA), tB j ≠ tAT i
  heisenberg_comm : ∀ (i : Fin wA) (j : Fin wB),
    decide (tA i < tBT j) = decide (tB j < tAT i)

/-! ### Finite Summation & Multiplicity Machinery -/

/-- Sum `f : Fin n → Nat` over `Fin n`. -/
def finSum : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f =>
    finSum n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + f ⟨n, Nat.lt_succ_self n⟩

theorem finSum_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    finSum n f = finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => h _), h]

theorem finSum_zero (n : Nat) : finSum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [finSum, ih]

theorem finSum_const_one (n : Nat) : finSum n (fun _ => 1) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [finSum, ih]

theorem finSum_const (n c : Nat) : finSum n (fun _ => c) = n * c := by
  induction n with
  | zero => simp [finSum]
  | succ n ih => simp [finSum, ih, Nat.succ_mul]

theorem finSum_add {n : Nat} (f g : Fin n → Nat) :
    finSum n (fun i => f i + g i) = finSum n f + finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum, ih]
    omega

theorem finSum_mul_right {n : Nat} (f : Fin n → Nat) (c : Nat) :
    finSum n f * c = finSum n (fun i => f i * c) := by
  induction n with
  | zero => simp [finSum]
  | succ n ih => simp [finSum, Nat.add_mul, ih]

theorem finSum_mul_left {n : Nat} (c : Nat) (f : Fin n → Nat) :
    c * finSum n f = finSum n (fun i => c * f i) := by
  induction n with
  | zero => simp [finSum]
  | succ n ih => simp [finSum, Nat.mul_add, ih]

theorem finSum_le {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i ≤ g i) :
    finSum n f ≤ finSum n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    simp only [finSum]
    have h1 := ih (f := fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                  (g := fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                  (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    have h2 := h ⟨n, Nat.lt_succ_self n⟩
    omega

/-- If every term `f i ≤ 1` and `∑_{i ∈ Fin n} f i = n`, then every term equals `1`. -/
theorem finSum_eq_one_of_le_one : ∀ {n : Nat} {f : Fin n → Nat},
    (∀ i, f i ≤ 1) → finSum n f = n → ∀ i, f i = 1
  | 0, _, _, _, i => Fin.elim0 i
  | n + 1, f, hle, hsum, i => by
    simp only [finSum] at hsum
    have hsub_le : finSum n (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) ≤ n :=
      Nat.le_trans
        (finSum_le (f := fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
                   (g := fun _ => 1)
                   (fun j => hle ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩))
        (Nat.le_of_eq (finSum_const_one n))
    have hlast_le : f ⟨n, Nat.lt_succ_self n⟩ ≤ 1 := hle _
    have hlast_eq : f ⟨n, Nat.lt_succ_self n⟩ = 1 := by omega
    have hsub_eq : finSum n (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) = n := by omega
    by_cases hi : i.val = n
    · have hfin : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi
      rw [hfin, hlast_eq]
    · have hlt : i.val < n := by omega
      have hrec := finSum_eq_one_of_le_one
        (f := fun j : Fin n => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
        (fun j => hle _) hsub_eq ⟨i.val, hlt⟩
      simpa using hrec

theorem finSum_comm {n k : Nat} (h : Fin n → Fin k → Nat) :
    finSum n (fun a => finSum k (fun b => h a b)) =
    finSum k (fun b => finSum n (fun a => h a b)) := by
  induction n with
  | zero =>
    simp only [finSum]
    exact (finSum_zero k).symm
  | succ n ih =>
    simp only [finSum]
    rw [ih, ← finSum_add]

theorem finSum_delta : ∀ (n : Nat) (target : Fin n) (g : Fin n → Nat),
    finSum n (fun x => if target = x then g x else 0) = g target
  | 0, target, _ => Fin.elim0 target
  | n + 1, target, g => by
    simp only [finSum]
    by_cases hlast : target = ⟨n, Nat.lt_succ_self n⟩
    · subst hlast
      have hz : finSum n (fun i =>
          if (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
          then g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ else 0) = 0 := by
        refine Eq.trans (finSum_congr fun i => ?_) (finSum_zero n)
        have hne : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) ≠
                   ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
          intro heq
          have hv : n = i.val := congrArg Fin.val heq
          exact Nat.ne_of_lt i.isLt hv.symm
        simp [hne]
      rw [hz]
      simp
    · have hlt : target.val < n := by
        have hne_val : target.val ≠ n := fun hv => hlast (Fin.ext hv)
        omega
      let t' : Fin n := ⟨target.val, hlt⟩
      have hsub : finSum n (fun i =>
          if target = ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
          then g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ else 0) =
          finSum n (fun i =>
          if t' = i then g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ else 0) := by
        apply finSum_congr
        intro i
        have heq_iff : (target = ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ↔ (t' = i) := by
          constructor
          · intro h
            have hv : target.val = i.val := congrArg Fin.val h
            exact Fin.ext hv
          · intro h
            have hv : target.val = i.val := congrArg Fin.val h
            exact Fin.ext hv
        simp [heq_iff]
      rw [hsub, finSum_delta n t' (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)]
      have ht' : (⟨t'.val, Nat.lt_succ_of_lt t'.isLt⟩ : Fin (n + 1)) = target :=
        Fin.ext rfl
      rw [ht']
      simp [hlast]

/-- Multiplicity of tick `t : Fin T` in schedule vector `f : Fin k → Fin T`. -/
def mult {k T : Nat} (f : Fin k → Fin T) (t : Fin T) : Nat :=
  finSum k (fun i => if f i = t then 1 else 0)

theorem finSum_mult {k T : Nat} (f : Fin k → Fin T) :
    finSum T (mult f) = k := by
  unfold mult
  rw [finSum_comm]
  have h1 : ∀ i : Fin k, finSum T (fun t => if f i = t then 1 else 0) = 1 :=
    fun i => finSum_delta T (f i) (fun _ => 1)
  rw [finSum_congr h1, finSum_const_one]

theorem mult_pos_exists : ∀ {k T : Nat} (f : Fin k → Fin T) (t : Fin T),
    0 < mult f t → ∃ i : Fin k, f i = t
  | 0, _, _, _, hpos => absurd hpos (Nat.not_lt_zero 0)
  | k + 1, _, f, t, hpos => by
    unfold mult at hpos
    simp only [finSum] at hpos
    by_cases hlast : f ⟨k, Nat.lt_succ_self k⟩ = t
    · exact ⟨⟨k, Nat.lt_succ_self k⟩, hlast⟩
    · simp only [hlast, ↓reduceIte, Nat.add_zero] at hpos
      obtain ⟨i, hi⟩ := mult_pos_exists
        (fun j : Fin k => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) t hpos
      exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, hi⟩

theorem mult_le_one_of_inj : ∀ {k T : Nat} (f : Fin k → Fin T),
    (∀ i₁ i₂, f i₁ = f i₂ → i₁ = i₂) → ∀ t : Fin T, mult f t ≤ 1
  | 0, _, _, _, _ => by simp [mult, finSum]
  | k + 1, _, f, hinj, t => by
    unfold mult
    simp only [finSum]
    by_cases hlast : f ⟨k, Nat.lt_succ_self k⟩ = t
    · have hz : finSum k (fun i =>
          if f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = t then 1 else 0) = 0 := by
        refine Eq.trans (finSum_congr fun i => ?_) (finSum_zero k)
        have hne : f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ≠ t := by
          intro heq
          have heq' := hinj ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⟨k, Nat.lt_succ_self k⟩
            (heq.trans hlast.symm)
          have hv : i.val = k := congrArg Fin.val heq'
          exact Nat.ne_of_lt i.isLt hv
        simp [hne]
      rw [hz]
      simp [hlast]
    · simp only [hlast, ↓reduceIte, Nat.add_zero]
      exact mult_le_one_of_inj
        (fun i : Fin k => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i₁ i₂ heq => by
          have hinj_eq := hinj ⟨i₁.val, Nat.lt_succ_of_lt i₁.isLt⟩
                               ⟨i₂.val, Nat.lt_succ_of_lt i₂.isLt⟩ heq
          injection hinj_eq with hv
          exact Fin.ext hv) t

theorem mult_disjoint_le_one {wA wB T : Nat}
    (f : Fin wA → Fin T) (g : Fin wB → Fin T)
    (hf : ∀ i₁ i₂, f i₁ = f i₂ → i₁ = i₂)
    (hg : ∀ j₁ j₂, g j₁ = g j₂ → j₁ = j₂)
    (hdisj : ∀ i j, f i ≠ g j) (t : Fin T) :
    mult f t + mult g t ≤ 1 := by
  have h1 := mult_le_one_of_inj f hf t
  have h2 := mult_le_one_of_inj g hg t
  by_cases hfp : 0 < mult f t
  · by_cases hgp : 0 < mult g t
    · obtain ⟨i, hi⟩ := mult_pos_exists f t hfp
      obtain ⟨j, hj⟩ := mult_pos_exists g t hgp
      exact absurd (hi.trans hj.symm) (hdisj i j)
    · omega
  · omega

/-! ### Depth Lower Bound & Zero-Idle Inversion-Parity Obstruction -/

/-- Every valid universal `(wA, wB)` schedule requires at least `wA + wB` ticks. -/
theorem schedule_depth_ge_weight {wA wB T : Nat} (s : ValidBiorderSchedule wA wB T) :
    wA + wB ≤ T := by
  have hsum : finSum T (fun t => mult s.tA t + mult s.tB t) = wA + wB := by
    rw [finSum_add, finSum_mult, finSum_mult]
  have hle : finSum T (fun t => mult s.tA t + mult s.tB t) ≤ finSum T (fun _ => 1) :=
    finSum_le (mult_disjoint_le_one s.tA s.tB s.tA_inj s.tB_inj s.x_anc_disjoint)
  rw [hsum, finSum_const_one] at hle
  exact hle

/-- Number of pairs `(i, j)` with `f i < g j`. -/
def pairCountLt {k₁ k₂ T : Nat} (f : Fin k₁ → Fin T) (g : Fin k₂ → Fin T) : Nat :=
  finSum k₁ (fun i => finSum k₂ (fun j => if f i < g j then 1 else 0))

/-- Forward inversion count `|{ (i, j) | tA i < tBT j }|`. -/
def inversionCount {wA wB T : Nat} (s : ValidBiorderSchedule wA wB T) : Nat :=
  pairCountLt s.tA s.tBT

/-- Express `pairCountLt f g` purely through the tick multiplicities `mult f` and `mult g`. -/
theorem pairCountLt_eq_mult_sum {k₁ k₂ T : Nat} (f : Fin k₁ → Fin T) (g : Fin k₂ → Fin T) :
    pairCountLt f g =
    finSum T (fun u => finSum T (fun v => (if u < v then 1 else 0) * mult f u * mult g v)) := by
  unfold pairCountLt mult
  have hpull : ∀ u v : Fin T,
      ((if u < v then 1 else 0) * finSum k₁ (fun i => if f i = u then 1 else 0)) *
        finSum k₂ (fun j => if g j = v then 1 else 0) =
      finSum k₁ (fun i => finSum k₂ (fun j =>
        if f i = u then (if g j = v then (if u < v then 1 else 0) else 0) else 0)) := by
    intro u v
    rw [finSum_mul_left (if u < v then 1 else 0), finSum_mul_right]
    apply finSum_congr
    intro i
    rw [finSum_mul_left]
    apply finSum_congr
    intro j
    by_cases hi : f i = u <;> by_cases hj : g j = v <;> simp [hi, hj]
  symm
  calc
    finSum T (fun u => finSum T (fun v =>
        ((if u < v then 1 else 0) * finSum k₁ (fun i => if f i = u then 1 else 0)) *
        finSum k₂ (fun j => if g j = v then 1 else 0)))
      = finSum T (fun u => finSum T (fun v => finSum k₁ (fun i => finSum k₂ (fun j =>
          if f i = u then (if g j = v then (if u < v then 1 else 0) else 0) else 0)))) :=
        finSum_congr (fun u => finSum_congr (fun v => hpull u v))
    _ = finSum T (fun u => finSum k₁ (fun i => finSum T (fun v => finSum k₂ (fun j =>
          if f i = u then (if g j = v then (if u < v then 1 else 0) else 0) else 0)))) :=
        finSum_congr (fun u => finSum_comm _)
    _ = finSum k₁ (fun i => finSum T (fun u => finSum T (fun v => finSum k₂ (fun j =>
          if f i = u then (if g j = v then (if u < v then 1 else 0) else 0) else 0)))) :=
        finSum_comm _
    _ = finSum k₁ (fun i => finSum T (fun u => finSum k₂ (fun j => finSum T (fun v =>
          if f i = u then (if g j = v then (if u < v then 1 else 0) else 0) else 0)))) :=
        finSum_congr (fun _ => finSum_congr (fun _ => finSum_comm _))
    _ = finSum k₁ (fun i => finSum k₂ (fun j => finSum T (fun u => finSum T (fun v =>
          if f i = u then (if g j = v then (if u < v then 1 else 0) else 0) else 0)))) :=
        finSum_congr (fun _ => finSum_comm _)
    _ = finSum k₁ (fun i => finSum k₂ (fun j => if f i < g j then 1 else 0)) := by
        apply finSum_congr
        intro i
        apply finSum_congr
        intro j
        have hu : finSum T (fun u => finSum T (fun v =>
            if f i = u then (if g j = v then (if u < v then 1 else 0) else 0) else 0)) =
            finSum T (fun u => if f i = u then (if u < g j then 1 else 0) else 0) := by
          apply finSum_congr
          intro u
          by_cases hiu : f i = u
          · simp only [hiu, ↓reduceIte]
            exact finSum_delta T (g j) (fun v => if u < v then 1 else 0)
          · simp only [hiu, ↓reduceIte]
            exact finSum_zero T
        rw [hu]
        exact finSum_delta T (f i) (fun u => if u < g j then 1 else 0)

/-- **General Zero-Idle Inversion-Parity Theorem**:
    At zero-idle depth `T = wA + wB`, every valid `(wA, wB)` schedule satisfies
    `2 * inversionCount s = wA * wB`. -/
theorem zero_idle_inversion_double_eq_prod {wA wB : Nat}
    (s : ValidBiorderSchedule wA wB (wA + wB)) :
    2 * inversionCount s = wA * wB := by
  let T := wA + wB
  have hx_all : ∀ t : Fin T, mult s.tA t + mult s.tB t = 1 := by
    apply finSum_eq_one_of_le_one
      (mult_disjoint_le_one s.tA s.tB s.tA_inj s.tB_inj s.x_anc_disjoint)
    rw [finSum_add, finSum_mult, finSum_mult]
  have hl_all : ∀ t : Fin T, mult s.tA t + mult s.tBT t = 1 := by
    apply finSum_eq_one_of_le_one
      (mult_disjoint_le_one s.tA s.tBT s.tA_inj s.tBT_inj s.l_data_disjoint)
    rw [finSum_add, finSum_mult, finSum_mult]
  have hz_all : ∀ t : Fin T, mult s.tBT t + mult s.tAT t = 1 := by
    apply finSum_eq_one_of_le_one
      (mult_disjoint_le_one s.tBT s.tAT s.tBT_inj s.tAT_inj s.z_anc_disjoint)
    rw [finSum_add, finSum_mult, finSum_mult]
    omega
  have hmult_B : ∀ t : Fin T, mult s.tB t = mult s.tBT t := by
    intro t; have := hx_all t; have := hl_all t; omega
  have hmult_AT : ∀ t : Fin T, mult s.tAT t = mult s.tA t := by
    intro t; have := hl_all t; have := hz_all t; omega
  have hcomm_count : inversionCount s = pairCountLt s.tB s.tAT := by
    unfold inversionCount pairCountLt
    rw [finSum_comm (fun (j : Fin wB) (i : Fin wA) => if s.tB j < s.tAT i then 1 else 0)]
    apply finSum_congr
    intro i
    apply finSum_congr
    intro j
    have hc := s.heisenberg_comm i j
    by_cases h1 : s.tA i < s.tBT j <;> by_cases h2 : s.tB j < s.tAT i
    · simp only [h1, h2, ↓reduceIte]
    · simp only [h1, h2, decide_true, decide_false] at hc; cases hc
    · simp only [h1, h2, decide_true, decide_false] at hc; cases hc
    · simp only [h1, h2, ↓reduceIte]
  have hswap_count : pairCountLt s.tB s.tAT = pairCountLt s.tBT s.tA := by
    rw [pairCountLt_eq_mult_sum s.tB s.tAT, pairCountLt_eq_mult_sum s.tBT s.tA]
    apply finSum_congr
    intro u
    apply finSum_congr
    intro v
    rw [hmult_B u, hmult_AT v]
  have htotal : inversionCount s + pairCountLt s.tBT s.tA = wA * wB := by
    unfold inversionCount pairCountLt
    rw [finSum_comm (fun (j : Fin wB) (i : Fin wA) => if s.tBT j < s.tA i then 1 else 0)]
    rw [← finSum_add]
    have hrow : ∀ i : Fin wA,
        finSum wB (fun j => if s.tA i < s.tBT j then 1 else 0) +
        finSum wB (fun j => if s.tBT j < s.tA i then 1 else 0) = wB := by
      intro i
      rw [← finSum_add]
      have hij : ∀ j : Fin wB,
          (if s.tA i < s.tBT j then 1 else 0) +
          (if s.tBT j < s.tA i then 1 else 0) = 1 := by
        intro j
        have hne : (s.tA i).val ≠ (s.tBT j).val := fun hv => s.l_data_disjoint i j (Fin.ext hv)
        by_cases h1 : s.tA i < s.tBT j
        · have h2 : ¬ (s.tBT j < s.tA i) := by
            change ¬ ((s.tBT j).val < (s.tA i).val)
            have h1' : (s.tA i).val < (s.tBT j).val := h1
            omega
          simp only [h1, h2, ↓reduceIte]
        · have h1' : ¬ ((s.tA i).val < (s.tBT j).val) := h1
          have h2 : s.tBT j < s.tA i := by
            change (s.tBT j).val < (s.tA i).val
            omega
          simp only [h1, h2, ↓reduceIte]
      rw [finSum_congr hij, finSum_const_one]
    rw [finSum_congr hrow, finSum_const]
  omega

/-- Whenever `wA * wB` is odd, NO universal `(wA, wB)` schedule exists at depth `wA + wB`. -/
theorem odd_product_zero_idle_impossible {wA wB : Nat} (hodd : (wA * wB) % 2 = 1) :
    ¬ Nonempty (ValidBiorderSchedule wA wB (wA + wB)) := by
  intro ⟨s⟩
  have h := zero_idle_inversion_double_eq_prod s
  omega

/-- **Main Impossibility Theorem (`no_symmetric_3_3_depth_6`)**:
    No valid universal `(3, 3)` 2-block CNOT schedule exists in `T = 6` ticks
    (`3 * 3 = 9` odd inversion-parity obstruction). -/
theorem no_symmetric_3_3_depth_6 : ¬ ∃ _ : ValidBiorderSchedule 3 3 6, True := by
  intro ⟨s, _⟩
  exact odd_product_zero_idle_impossible (wA := 3) (wB := 3) (by decide) ⟨s⟩

/-- Stronger lower bound: no universal `(3, 3)` schedule exists for ANY `T < 7`. -/
theorem no_symmetric_3_3_depth_lt_7 (T : Nat) (hT : T < 7) :
    ¬ Nonempty (ValidBiorderSchedule 3 3 T) := by
  intro ⟨s⟩
  have hge : 6 ≤ T := schedule_depth_ge_weight s
  have heq : T = 6 := by omega
  subst heq
  exact no_symmetric_3_3_depth_6 ⟨s, trivial⟩

/-! ### Constructive Schedule Witnesses: `(4, 2)` at `T = 6` & `(3, 3)` at `T = 7` -/

def zeroIdle42_tA : Fin 4 → Fin 6
  | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 2 | ⟨2, _⟩ => 3 | ⟨3, _⟩ => 5

def zeroIdle42_tB : Fin 2 → Fin 6
  | ⟨0, _⟩ => 4 | ⟨1, _⟩ => 1

def zeroIdle42_tBT : Fin 2 → Fin 6
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 4

def zeroIdle42_tAT : Fin 4 → Fin 6
  | ⟨0, _⟩ => 5 | ⟨1, _⟩ => 3 | ⟨2, _⟩ => 2 | ⟨3, _⟩ => 0

/-- **Constructive Zero-Idle `(4, 2)` Schedule at `T = 6` (`zero_idle_4_2_depth_6`)**:
    Asymmetric `4 + 2 = 6` check split (`4 * 2 = 8` even!) unlocks a collision-free,
    Heisenberg-commuting CNOT schedule in 6 ticks with zero idle slots. -/
def zero_idle_4_2_depth_6 : ValidBiorderSchedule 4 2 6 where
  tA  := zeroIdle42_tA
  tB  := zeroIdle42_tB
  tBT := zeroIdle42_tBT
  tAT := zeroIdle42_tAT
  tA_inj          := by decide
  tB_inj          := by decide
  tBT_inj         := by decide
  tAT_inj         := by decide
  x_anc_disjoint  := by decide
  z_anc_disjoint  := by decide
  l_data_disjoint := by decide
  r_data_disjoint := by decide
  heisenberg_comm := by decide

/-- Check whether tick `t : Fin T` is active on all 4 qubit roles (X-ancilla, Z-ancilla,
    L-data, R-data) of schedule `s`. -/
def isTickFullyActive {wA wB T : Nat} (s : ValidBiorderSchedule wA wB T) (t : Fin T) : Bool :=
  let xActive := decide (∃ i, s.tA i = t) || decide (∃ j, s.tB j = t)
  let zActive := decide (∃ j, s.tBT j = t) || decide (∃ i, s.tAT i = t)
  let lActive := decide (∃ i, s.tA i = t) || decide (∃ j, s.tBT j = t)
  let rActive := decide (∃ j, s.tB j = t) || decide (∃ i, s.tAT i = t)
  xActive && zActive && lActive && rActive

/-- Every single tick `0..5` in `zero_idle_4_2_depth_6` has 100% active qubit utilization
    across X-ancillas, Z-ancillas, L-data, and R-data (`0` idle slots). -/
theorem zero_idle_4_2_all_ticks_active :
    ∀ t : Fin 6, isTickFullyActive zero_idle_4_2_depth_6 t = true := by
  decide

def mirror33_tA : Fin 3 → Fin 7
  | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 2 | ⟨2, _⟩ => 4

def mirror33_tB : Fin 3 → Fin 7
  | ⟨0, _⟩ => 5 | ⟨1, _⟩ => 3 | ⟨2, _⟩ => 1

def mirror33_tBT : Fin 3 → Fin 7
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 3 | ⟨2, _⟩ => 5

def mirror33_tAT : Fin 3 → Fin 7
  | ⟨0, _⟩ => 6 | ⟨1, _⟩ => 4 | ⟨2, _⟩ => 2

/-- **Constructive Mirror `(3, 3)` Schedule at `T = 7` (`mirror_3_3_depth_7`)**:
    Time-reversal mirror schedule (`tAT i = 6 - tA i`, `tBT j = 6 - tB j`) achieving
    the tight minimum depth `T = 7` for universal `(3, 3)` codes. -/
def mirror_3_3_depth_7 : ValidBiorderSchedule 3 3 7 where
  tA  := mirror33_tA
  tB  := mirror33_tB
  tBT := mirror33_tBT
  tAT := mirror33_tAT
  tA_inj          := by decide
  tB_inj          := by decide
  tBT_inj         := by decide
  tAT_inj         := by decide
  x_anc_disjoint  := by decide
  z_anc_disjoint  := by decide
  l_data_disjoint := by decide
  r_data_disjoint := by decide
  heisenberg_comm := by decide

/-- `T = 7` is the exact tight minimum depth for universal `(3, 3)` schedules. -/
theorem symmetric_3_3_tight_min_depth_7 :
    (∀ T < 7, ¬ Nonempty (ValidBiorderSchedule 3 3 T)) ∧
    Nonempty (ValidBiorderSchedule 3 3 7) :=
  ⟨no_symmetric_3_3_depth_lt_7, ⟨mirror_3_3_depth_7⟩⟩

end ZeroIdleQldpc.ParityBarrier
