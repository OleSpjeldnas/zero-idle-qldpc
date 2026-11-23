/-
  ZeroIdleQldpc.CertifiedDecoder
  ==============================
  Formal verification of global MAP (minimum-weight syndrome-compatible subset)
  optimality for `SpaceTimeDecoder` Paths 1, 2, and 3 over arbitrary strictly
  positive integer/natural mechanism weights (`∀ m, 0 < w m`) and `GF(2)`
  syndrome/observable columns (`BitVec D`, `BitVec K`), together with the
  4-mechanism `30 vs 9 + 9 + 9 = 27` counterexample refuting global optimality
  of the restricted-tile slack gate (`30 ≤ 37`).
-/

namespace ZeroIdleQldpc.CertifiedDecoder

/-- A mechanism explanation subset `S ⊆ Fin M`. -/
abbrev SubsetM (M : Nat) := Fin M → Bool

def emptySubset {M : Nat} : SubsetM M := fun _ => false

def singletonSubset {M : Nat} (m : Fin M) : SubsetM M :=
  fun x => decide (x = m)

def pairSubset {M : Nat} (m₁ m₂ : Fin M) : SubsetM M :=
  fun x => decide (x = m₁) || decide (x = m₂)

def tripleSubset {M : Nat} (m₁ m₂ m₃ : Fin M) : SubsetM M :=
  fun x => decide (x = m₁) || decide (x = m₂) || decide (x = m₃)

def eraseElem {M : Nat} (S : SubsetM M) (m : Fin M) : SubsetM M :=
  fun x => S x && decide (x ≠ m)

/-! ### Subset Weight, Cardinality, Syndrome, and Observable -/

/-- Additive mechanism weight `∑_{m ∈ S} w(m)`. -/
def subsetWeight : {M : Nat} → (Fin M → Nat) → SubsetM M → Nat
  | 0, _, _ => 0
  | M + 1, w, S =>
    subsetWeight (fun i => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                 (fun i => S ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) +
    (if S ⟨M, Nat.lt_succ_self M⟩ then w ⟨M, Nat.lt_succ_self M⟩ else 0)

/-- Cardinality `|S|` of `S : SubsetM M`. -/
def card {M : Nat} (S : SubsetM M) : Nat :=
  subsetWeight (fun _ => 1) S

/-- `GF(2)` XOR combination `⊕_{m ∈ S} f(m)` of `BitVec W` columns. -/
def xorSubset {W : Nat} : {M : Nat} → (Fin M → BitVec W) → SubsetM M → BitVec W
  | 0, _, _ => 0#W
  | M + 1, f, S =>
    xorSubset (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
              (fun i => S ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ^^^
    (if S ⟨M, Nat.lt_succ_self M⟩ then f ⟨M, Nat.lt_succ_self M⟩ else 0#W)

/-- Induced detector syndrome `⊕_{m ∈ S} col(m)`. -/
def subsetSyndrome {D M : Nat} (col : Fin M → BitVec D) (S : SubsetM M) : BitVec D :=
  xorSubset col S

/-- Induced logical observable frame `⊕_{m ∈ S} obs(m)`. -/
def subsetObs {K M : Nat} (obs : Fin M → BitVec K) (S : SubsetM M) : BitVec K :=
  xorSubset obs S

/-- `S` is a syndrome-compatible explanation of `syn`. -/
def IsCompatible {D M : Nat} (col : Fin M → BitVec D) (syn : BitVec D) (S : SubsetM M) : Prop :=
  subsetSyndrome col S = syn

/-! ### Structural Lemmas for `subsetWeight`, `card`, and `xorSubset` -/

theorem subsetWeight_congr {M : Nat} (w : Fin M → Nat) {S₁ S₂ : SubsetM M}
    (h : ∀ x, S₁ x = S₂ x) : subsetWeight w S₁ = subsetWeight w S₂ := by
  have heq : S₁ = S₂ := funext h
  rw [heq]

theorem xorSubset_congr {W M : Nat} (f : Fin M → BitVec W) {S₁ S₂ : SubsetM M}
    (h : ∀ x, S₁ x = S₂ x) : xorSubset f S₁ = xorSubset f S₂ := by
  have heq : S₁ = S₂ := funext h
  rw [heq]

theorem subsetWeight_empty {M : Nat} (w : Fin M → Nat) :
    subsetWeight w emptySubset = 0 := by
  induction M with
  | zero => rfl
  | succ M ih =>
    simp only [subsetWeight]
    have h0 : (if emptySubset (M := M + 1) ⟨M, Nat.lt_succ_self M⟩ then w ⟨M, Nat.lt_succ_self M⟩ else 0) = 0 := rfl
    rw [h0, Nat.add_zero]
    exact ih (fun i => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)

theorem card_empty (M : Nat) : card (emptySubset (M := M)) = 0 :=
  subsetWeight_empty (fun _ => 1)

theorem xorSubset_empty {W M : Nat} (f : Fin M → BitVec W) :
    xorSubset f emptySubset = 0#W := by
  induction M with
  | zero => rfl
  | succ M ih =>
    simp only [xorSubset]
    have h0 : (if emptySubset (M := M + 1) ⟨M, Nat.lt_succ_self M⟩ then f ⟨M, Nat.lt_succ_self M⟩ else 0#W) = 0#W := rfl
    rw [h0, BitVec.xor_zero]
    exact ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)

private theorem nat_disj_ite (a b v : Nat) (x y : Bool) (h : ¬ (x = true ∧ y = true)) :
    (a + b) + (if (x || y) = true then v else 0) =
    (a + if x = true then v else 0) + (b + if y = true then v else 0) := by
  cases x <;> cases y
  · simp
  · simp; omega
  · simp; omega
  · exact absurd ⟨rfl, rfl⟩ h

theorem subsetWeight_disjoint : ∀ {M : Nat} (w : Fin M → Nat) (S₁ S₂ : SubsetM M),
    (∀ x, ¬ (S₁ x = true ∧ S₂ x = true)) →
    subsetWeight w (fun x => S₁ x || S₂ x) = subsetWeight w S₁ + subsetWeight w S₂
  | 0, _, _, _, _ => rfl
  | M + 1, w, S₁, S₂, hdisj => by
    simp only [subsetWeight]
    have ih := subsetWeight_disjoint
      (fun i : Fin M => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (fun i : Fin M => S₁ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (fun i : Fin M => S₂ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (fun i => hdisj _)
    rw [ih]
    exact nat_disj_ite _ _ _ _ _ (hdisj ⟨M, Nat.lt_succ_self M⟩)

private theorem bitvec_xor_ite {W : Nat} (a b v : BitVec W) (x y : Bool) :
    (a ^^^ b) ^^^ (if xor x y = true then v else 0#W) =
    (a ^^^ if x = true then v else 0#W) ^^^ (b ^^^ if y = true then v else 0#W) := by
  cases x <;> cases y
  · simp [BitVec.xor_zero]
  · simp [BitVec.xor_zero, BitVec.xor_assoc]
  · simp only [Bool.xor_false, Bool.false_eq_true, ↓reduceIte, BitVec.xor_zero]
    rw [BitVec.xor_assoc, BitVec.xor_comm b v, ← BitVec.xor_assoc]
  · simp only [Bool.xor_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, BitVec.xor_zero]
    rw [BitVec.xor_assoc, ← BitVec.xor_assoc v b v, BitVec.xor_comm v b,
        BitVec.xor_assoc b v v, BitVec.xor_self, BitVec.xor_zero]

theorem xorSubset_xor : ∀ {W M : Nat} (f : Fin M → BitVec W) (S₁ S₂ : SubsetM M),
    xorSubset f (fun x => xor (S₁ x) (S₂ x)) = xorSubset f S₁ ^^^ xorSubset f S₂
  | _, 0, _, _, _ => by simp [xorSubset]
  | W, M + 1, f, S₁, S₂ => by
    simp only [xorSubset]
    have ih := xorSubset_xor
      (fun i : Fin M => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (fun i : Fin M => S₁ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (fun i : Fin M => S₂ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    rw [ih]
    exact bitvec_xor_ite _ _ _ _ _

theorem subsetWeight_singleton : ∀ {M : Nat} (w : Fin M → Nat) (m : Fin M),
    subsetWeight w (singletonSubset m) = w m
  | 0, _, m => Fin.elim0 m
  | M + 1, w, m => by
    simp only [subsetWeight, singletonSubset]
    by_cases hm : m = ⟨M, Nat.lt_succ_self M⟩
    · subst hm
      have hz : subsetWeight (fun i : Fin M => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
          (fun i : Fin M => decide ((⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (M + 1)) =
                                    ⟨M, Nat.lt_succ_self M⟩)) = 0 := by
        refine Eq.trans (subsetWeight_congr _ fun i => ?_)
          (subsetWeight_empty (fun i : Fin M => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
        have hne : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (M + 1)) ≠ ⟨M, Nat.lt_succ_self M⟩ :=
          fun heq => Nat.ne_of_lt i.isLt (congrArg Fin.val heq)
        simp [emptySubset, hne]
      rw [hz]
      simp
    · have hlt : m.val < M := by
        have hv : m.val ≠ M := fun hv => hm (Fin.ext hv)
        omega
      let m' : Fin M := ⟨m.val, hlt⟩
      have hsub : subsetWeight (fun i : Fin M => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
          (fun i : Fin M => decide ((⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (M + 1)) = m)) =
          subsetWeight (fun i : Fin M => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
          (singletonSubset m') := by
        apply subsetWeight_congr
        intro i
        have hiff : ((⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (M + 1)) = m) ↔ (i = m') := by
          constructor
          · intro h; have hv : i.val = m.val := congrArg Fin.val h; exact Fin.ext hv
          · intro h; have hv : i.val = m.val := congrArg Fin.val h; exact Fin.ext hv
        simp [singletonSubset, hiff]
      have hne_top : (⟨M, Nat.lt_succ_self M⟩ : Fin (M + 1)) ≠ m := fun h => hm h.symm
      rw [hsub, subsetWeight_singleton _ m']
      have hm' : (⟨m'.val, Nat.lt_succ_of_lt m'.isLt⟩ : Fin (M + 1)) = m := Fin.ext rfl
      rw [hm']
      simp [hne_top]

theorem xorSubset_singleton : ∀ {W M : Nat} (f : Fin M → BitVec W) (m : Fin M),
    xorSubset f (singletonSubset m) = f m
  | _, 0, _, m => Fin.elim0 m
  | W, M + 1, f, m => by
    simp only [xorSubset, singletonSubset]
    by_cases hm : m = ⟨M, Nat.lt_succ_self M⟩
    · subst hm
      have hz : xorSubset (fun i : Fin M => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
          (fun i : Fin M => decide ((⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (M + 1)) =
                                    ⟨M, Nat.lt_succ_self M⟩)) = 0#W := by
        refine Eq.trans (xorSubset_congr _ fun i => ?_)
          (xorSubset_empty (fun i : Fin M => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
        have hne : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (M + 1)) ≠ ⟨M, Nat.lt_succ_self M⟩ :=
          fun heq => Nat.ne_of_lt i.isLt (congrArg Fin.val heq)
        simp [emptySubset, hne]
      rw [hz]
      simp [BitVec.zero_xor]
    · have hlt : m.val < M := by
        have hv : m.val ≠ M := fun hv => hm (Fin.ext hv)
        omega
      let m' : Fin M := ⟨m.val, hlt⟩
      have hsub : xorSubset (fun i : Fin M => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
          (fun i : Fin M => decide ((⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (M + 1)) = m)) =
          xorSubset (fun i : Fin M => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
          (singletonSubset m') := by
        apply xorSubset_congr
        intro i
        have hiff : ((⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (M + 1)) = m) ↔ (i = m') := by
          constructor
          · intro h; have hv : i.val = m.val := congrArg Fin.val h; exact Fin.ext hv
          · intro h; have hv : i.val = m.val := congrArg Fin.val h; exact Fin.ext hv
        simp [singletonSubset, hiff]
      have hne_top : (⟨M, Nat.lt_succ_self M⟩ : Fin (M + 1)) ≠ m := fun h => hm h.symm
      rw [hsub, xorSubset_singleton _ m']
      have hm' : (⟨m'.val, Nat.lt_succ_of_lt m'.isLt⟩ : Fin (M + 1)) = m := Fin.ext rfl
      rw [hm']
      simp [hne_top, BitVec.xor_zero]

theorem subsetWeight_pair {M : Nat} (w : Fin M → Nat) {m₁ m₂ : Fin M} (h12 : m₁ ≠ m₂) :
    subsetWeight w (pairSubset m₁ m₂) = w m₁ + w m₂ := by
  have hd : ∀ x, ¬ (singletonSubset m₁ x = true ∧ singletonSubset m₂ x = true) := by
    intro x ⟨h1, h2⟩
    simp only [singletonSubset, decide_eq_true_eq] at h1 h2
    exact h12 (h1.symm.trans h2)
  have heq : pairSubset m₁ m₂ = fun x => singletonSubset m₁ x || singletonSubset m₂ x := rfl
  rw [heq, subsetWeight_disjoint w _ _ hd, subsetWeight_singleton, subsetWeight_singleton]

theorem xorSubset_pair {W M : Nat} (f : Fin M → BitVec W) {m₁ m₂ : Fin M} (h12 : m₁ ≠ m₂) :
    xorSubset f (pairSubset m₁ m₂) = f m₁ ^^^ f m₂ := by
  have heq : pairSubset m₁ m₂ = fun x => xor (singletonSubset m₁ x) (singletonSubset m₂ x) := by
    funext x
    unfold pairSubset singletonSubset
    by_cases hx1 : x = m₁ <;> by_cases hx2 : x = m₂
    · exact absurd (hx1.symm.trans hx2) h12
    · rw [decide_eq_true hx1, decide_eq_false hx2]; rfl
    · rw [decide_eq_false hx1, decide_eq_true hx2]; rfl
    · rw [decide_eq_false hx1, decide_eq_false hx2]; rfl
  rw [heq, xorSubset_xor, xorSubset_singleton, xorSubset_singleton]

theorem subsetWeight_triple {M : Nat} (w : Fin M → Nat) {m₁ m₂ m₃ : Fin M}
    (h12 : m₁ ≠ m₂) (h13 : m₁ ≠ m₃) (h23 : m₂ ≠ m₃) :
    subsetWeight w (tripleSubset m₁ m₂ m₃) = w m₁ + w m₂ + w m₃ := by
  have hd : ∀ x, ¬ (pairSubset m₁ m₂ x = true ∧ singletonSubset m₃ x = true) := by
    intro x ⟨h1, h2⟩
    simp only [pairSubset, singletonSubset, Bool.or_eq_true, decide_eq_true_eq] at h1 h2
    rcases h1 with rfl | rfl
    · exact h13 h2
    · exact h23 h2
  have heq : tripleSubset m₁ m₂ m₃ = fun x => pairSubset m₁ m₂ x || singletonSubset m₃ x := rfl
  rw [heq, subsetWeight_disjoint w _ _ hd, subsetWeight_pair w h12, subsetWeight_singleton]

theorem xorSubset_triple {W M : Nat} (f : Fin M → BitVec W) {m₁ m₂ m₃ : Fin M}
    (h12 : m₁ ≠ m₂) (h13 : m₁ ≠ m₃) (h23 : m₂ ≠ m₃) :
    xorSubset f (tripleSubset m₁ m₂ m₃) = f m₁ ^^^ f m₂ ^^^ f m₃ := by
  have heq : tripleSubset m₁ m₂ m₃ = fun x => xor (pairSubset m₁ m₂ x) (singletonSubset m₃ x) := by
    funext x
    unfold tripleSubset pairSubset singletonSubset
    by_cases hx1 : x = m₁ <;> by_cases hx2 : x = m₂ <;> by_cases hx3 : x = m₃
    · exact absurd (hx1.symm.trans hx2) h12
    · exact absurd (hx1.symm.trans hx2) h12
    · exact absurd (hx1.symm.trans hx3) h13
    · rw [decide_eq_true hx1, decide_eq_false hx2, decide_eq_false hx3]; rfl
    · exact absurd (hx2.symm.trans hx3) h23
    · rw [decide_eq_false hx1, decide_eq_true hx2, decide_eq_false hx3]; rfl
    · rw [decide_eq_false hx1, decide_eq_false hx2, decide_eq_true hx3]; rfl
    · rw [decide_eq_false hx1, decide_eq_false hx2, decide_eq_false hx3]; rfl
  rw [heq, xorSubset_xor, xorSubset_pair f h12, xorSubset_singleton]

/-! ### Cardinality Decomposition (`card = 0, 1, 2, 3`) via `eraseElem` -/

theorem exists_mem_of_card_pos : ∀ {M : Nat} {S : SubsetM M},
    0 < card S → ∃ m : Fin M, S m = true
  | 0, _, hpos => absurd hpos (Nat.not_lt_zero 0)
  | M + 1, S, hpos => by
    unfold card subsetWeight at hpos
    by_cases htop : S ⟨M, Nat.lt_succ_self M⟩ = true
    · exact ⟨⟨M, Nat.lt_succ_self M⟩, htop⟩
    · simp only [htop, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hpos
      obtain ⟨i, hi⟩ := exists_mem_of_card_pos
        (S := fun j : Fin M => S ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) hpos
      exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, hi⟩

theorem eraseElem_decomp {M : Nat} (S : SubsetM M) {m : Fin M} (hm : S m = true) :
    (∀ x, (eraseElem S m x || singletonSubset m x) = S x) ∧
    (∀ x, ¬ (eraseElem S m x = true ∧ singletonSubset m x = true)) ∧
    eraseElem S m m = false := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    unfold eraseElem singletonSubset
    by_cases hxm : x = m
    · subst hxm; simp [hm]
    · simp [hxm]
  · intro x ⟨h1, h2⟩
    unfold eraseElem at h1
    unfold singletonSubset at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2
    exact h1.2 h2
  · simp [eraseElem]

theorem card_eraseElem {M : Nat} (S : SubsetM M) {m : Fin M} (hm : S m = true) :
    card S = card (eraseElem S m) + 1 := by
  obtain ⟨hunion, hdisj, _⟩ := eraseElem_decomp S hm
  unfold card
  rw [← subsetWeight_congr (fun _ => 1) hunion,
      subsetWeight_disjoint (fun _ => 1) _ _ hdisj,
      subsetWeight_singleton]

theorem card_le_total : ∀ {M : Nat} (S : SubsetM M), card S ≤ M
  | 0, _ => Nat.le_refl 0
  | M + 1, S => by
    unfold card subsetWeight
    have ih := card_le_total (fun i : Fin M => S ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    unfold card at ih
    cases S ⟨M, Nat.lt_succ_self M⟩ <;> simp <;> omega

theorem eq_empty_of_card_zero {M : Nat} {S : SubsetM M} (hc : card S = 0) :
    S = emptySubset := by
  funext x
  cases hx : S x
  · rfl
  · have h1 := card_eraseElem S hx
    omega

theorem eq_singleton_of_card_one {M : Nat} {S : SubsetM M} (hc : card S = 1) :
    ∃ m : Fin M, S = singletonSubset m := by
  obtain ⟨m, hm⟩ := exists_mem_of_card_pos (by omega : 0 < card S)
  obtain ⟨hunion, _, _⟩ := eraseElem_decomp S hm
  have hc0 : card (eraseElem S m) = 0 := by have := card_eraseElem S hm; omega
  have he0 := eq_empty_of_card_zero hc0
  refine ⟨m, funext fun x => ?_⟩
  have hu := (hunion x).symm
  rw [he0] at hu
  simpa [emptySubset] using hu

theorem eq_pair_of_card_two {M : Nat} {S : SubsetM M} (hc : card S = 2) :
    ∃ m₁ m₂ : Fin M, m₁ ≠ m₂ ∧ S = pairSubset m₁ m₂ := by
  obtain ⟨m₁, hm₁⟩ := exists_mem_of_card_pos (by omega : 0 < card S)
  obtain ⟨hunion, _, herase_self⟩ := eraseElem_decomp S hm₁
  have hc1 : card (eraseElem S m₁) = 1 := by have := card_eraseElem S hm₁; omega
  obtain ⟨m₂, he1⟩ := eq_singleton_of_card_one hc1
  have hne : m₁ ≠ m₂ := by
    intro heq
    rw [he1, heq] at herase_self
    simp [singletonSubset] at herase_self
  refine ⟨m₁, m₂, hne, funext fun x => ?_⟩
  have hu := (hunion x).symm
  rw [he1] at hu
  rw [hu]
  unfold pairSubset singletonSubset
  cases decide (x = m₂) <;> cases decide (x = m₁) <;> rfl

theorem eq_triple_of_card_three {M : Nat} {S : SubsetM M} (hc : card S = 3) :
    ∃ m₁ m₂ m₃ : Fin M, m₁ ≠ m₂ ∧ m₁ ≠ m₃ ∧ m₂ ≠ m₃ ∧ S = tripleSubset m₁ m₂ m₃ := by
  obtain ⟨m₁, hm₁⟩ := exists_mem_of_card_pos (by omega : 0 < card S)
  obtain ⟨hunion, _, herase_self⟩ := eraseElem_decomp S hm₁
  have hc2 : card (eraseElem S m₁) = 2 := by have := card_eraseElem S hm₁; omega
  obtain ⟨m₂, m₃, h23, he2⟩ := eq_pair_of_card_two hc2
  have h12 : m₁ ≠ m₂ := by
    intro heq
    rw [he2, heq] at herase_self
    simp [pairSubset] at herase_self
  have h13 : m₁ ≠ m₃ := by
    intro heq
    rw [he2, heq] at herase_self
    simp [pairSubset] at herase_self
  refine ⟨m₁, m₂, m₃, h12, h13, h23, funext fun x => ?_⟩
  have hu := (hunion x).symm
  rw [he2] at hu
  rw [hu]
  unfold tripleSubset pairSubset singletonSubset
  cases decide (x = m₁) <;> cases decide (x = m₂) <;> cases decide (x = m₃) <;> rfl

theorem card_pos_of_compatible_nonzero {D M : Nat} {col : Fin M → BitVec D}
    {syn : BitVec D} {S : SubsetM M} (hsyn : syn ≠ 0#D) (hcomp : IsCompatible col syn S) :
    1 ≤ card S := by
  by_cases hc : card S = 0
  · have he := eq_empty_of_card_zero hc
    unfold IsCompatible subsetSyndrome at hcomp
    rw [he, xorSubset_empty] at hcomp
    exact absurd hcomp.symm hsyn
  · omega

/-! ### Sorted Cost Floors (`pairFloor`, `tripleFloor`, `fourFloor`) -/

/-- Insert `x : Nat` into a non-decreasing list. -/
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

/-- Non-decreasing sorted predicate on `List Nat`. -/
def IsSorted : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: ys => x ≤ y ∧ IsSorted (y :: ys)

/-- Sum of the first `k` elements of `xs`. -/
def sumTake : Nat → List Nat → Nat
  | 0, _ => 0
  | _, [] => 0
  | k + 1, x :: xs => x + sumTake k xs

/-- Sorted list of all `M` mechanism weights. -/
def sortedWeights : {M : Nat} → (Fin M → Nat) → List Nat
  | 0, _ => []
  | M + 1, w =>
    insertSorted (w ⟨M, Nat.lt_succ_self M⟩)
      (sortedWeights (fun i => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))

/-- Sum of the `k` smallest mechanism weights. -/
def kSmallestSum {M : Nat} (w : Fin M → Nat) (k : Nat) : Nat :=
  sumTake k (sortedWeights w)

def pairFloor {M : Nat} (w : Fin M → Nat) : Nat := kSmallestSum w 2
def tripleFloor {M : Nat} (w : Fin M → Nat) : Nat := kSmallestSum w 3
def fourFloor {M : Nat} (w : Fin M → Nat) : Nat := kSmallestSum w 4

private theorem length_insertSorted (x : Nat) (xs : List Nat) :
    (insertSorted x xs).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [insertSorted]
    by_cases hxy : x ≤ y <;> simp [hxy, ih]

private theorem length_sortedWeights : ∀ {M : Nat} (w : Fin M → Nat),
    (sortedWeights w).length = M
  | 0, _ => rfl
  | M + 1, w => by
    simp [sortedWeights, length_insertSorted, length_sortedWeights]

private theorem isSorted_insertSorted (x : Nat) : ∀ {xs : List Nat},
    IsSorted xs → IsSorted (insertSorted x xs)
  | [], _ => trivial
  | [y], _ => by
    simp only [insertSorted]
    by_cases hxy : x ≤ y
    · simp [hxy, IsSorted]
    · have hyx : y ≤ x := by omega
      simp [hxy, IsSorted, hyx]
  | y :: z :: zs, ⟨hyz, hzs⟩ => by
    simp only [insertSorted]
    by_cases hxy : x ≤ y
    · simp [hxy, IsSorted, hyz, hzs]
    · simp only [hxy, ↓reduceIte]
      have ih := isSorted_insertSorted x hzs
      simp only [insertSorted] at ih ⊢
      by_cases hxz : x ≤ z
      · have hyx : y ≤ x := by omega
        simp [hxz] at ih ⊢
        exact ⟨hyx, ih⟩
      · simp [hxz] at ih ⊢
        exact ⟨hyz, ih⟩

private theorem isSorted_sortedWeights : ∀ {M : Nat} (w : Fin M → Nat),
    IsSorted (sortedWeights w)
  | 0, _ => trivial
  | _ + 1, _ => isSorted_insertSorted _ (isSorted_sortedWeights _)

private theorem sumTake_cons_le_tail : ∀ (k : Nat) (y : Nat) (ys : List Nat),
    IsSorted (y :: ys) → k ≤ ys.length → sumTake k (y :: ys) ≤ sumTake k ys
  | 0, _, _, _, _ => Nat.le_refl 0
  | _ + 1, _, [], _, hlen => absurd hlen (Nat.not_succ_le_zero _)
  | k + 1, y, z :: zs, ⟨hyz, hzs⟩, hlen => by
    simp only [sumTake]
    have hlen' : k ≤ zs.length := by simp at hlen; omega
    have ih := sumTake_cons_le_tail k z zs hzs hlen'
    omega

private theorem sumTake_succ_insertSorted_le (x : Nat) : ∀ (k : Nat) (xs : List Nat),
    sumTake (k + 1) (insertSorted x xs) ≤ x + sumTake k xs
  | 0, [] => by simp [insertSorted, sumTake]
  | k + 1, [] => by simp [insertSorted, sumTake]
  | 0, y :: ys => by
    simp only [insertSorted]
    by_cases hxy : x ≤ y
    · simp [hxy, sumTake]
    · simp [hxy, sumTake]; omega
  | k + 1, y :: ys => by
    simp only [insertSorted]
    by_cases hxy : x ≤ y
    · simp [hxy, sumTake]
    · simp only [hxy, ↓reduceIte, sumTake]
      have ih := sumTake_succ_insertSorted_le x k ys
      omega

private theorem sumTake_insertSorted_le_skip (x : Nat) : ∀ (k : Nat) (xs : List Nat),
    IsSorted xs → k ≤ xs.length → sumTake k (insertSorted x xs) ≤ sumTake k xs
  | 0, _, _, _ => Nat.le_refl 0
  | _ + 1, [], _, hlen => absurd hlen (Nat.not_succ_le_zero _)
  | k + 1, y :: ys, hsort, hlen => by
    simp only [insertSorted]
    have hlen' : k ≤ ys.length := by simp at hlen; omega
    by_cases hxy : x ≤ y
    · simp only [hxy, ↓reduceIte, sumTake]
      have htail := sumTake_cons_le_tail k y ys hsort hlen'
      omega
    · simp only [hxy, ↓reduceIte, sumTake]
      have hsort' : IsSorted ys := by
        cases ys with
        | nil => trivial
        | cons z zs => exact hsort.2
      have ih := sumTake_insertSorted_le_skip x k ys hsort' hlen'
      omega

/-- **Fundamental Cost-Floor Bound (`kSmallestSum_le_subsetWeight`)**:
    For EVERY subset `S : SubsetM M` and `k ≤ card S`, the sum of the `k` smallest
    mechanism weights lower-bounds `subsetWeight w S`. -/
theorem kSmallestSum_le_subsetWeight : ∀ {M : Nat} (w : Fin M → Nat) (S : SubsetM M)
    {k : Nat}, k ≤ card S → kSmallestSum w k ≤ subsetWeight w S
  | 0, _, S, k, hk => by
    have hc : card S = 0 := rfl
    have hk0 : k = 0 := by omega
    subst hk0
    exact Nat.le_refl _
  | M + 1, w, S, k, hk => by
    unfold kSmallestSum sortedWeights subsetWeight
    cases htop : S ⟨M, Nat.lt_succ_self M⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      have hcard' : k ≤ card (fun i : Fin M => S ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) := by
        unfold card at hk ⊢
        simp only [subsetWeight, htop, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hk
        exact hk
      have hlen : k ≤ (sortedWeights (fun i : Fin M => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)).length := by
        rw [length_sortedWeights]
        exact Nat.le_trans hcard' (card_le_total _)
      have hskip := sumTake_insertSorted_le_skip (w ⟨M, Nat.lt_succ_self M⟩) k
        (sortedWeights (fun i : Fin M => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
        (isSorted_sortedWeights _) hlen
      have ih := kSmallestSum_le_subsetWeight
        (fun i : Fin M => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i : Fin M => S ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) hcard'
      unfold kSmallestSum at ih
      exact Nat.le_trans hskip ih
    · simp only [↓reduceIte]
      cases k with
      | zero => simp [sumTake]
      | succ k' =>
        have hcard' : k' ≤ card (fun i : Fin M => S ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) := by
          unfold card at hk ⊢
          simp only [subsetWeight, htop, ↓reduceIte] at hk
          omega
        have hinc := sumTake_succ_insertSorted_le (w ⟨M, Nat.lt_succ_self M⟩) k'
          (sortedWeights (fun i : Fin M => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
        have ih := kSmallestSum_le_subsetWeight
          (fun i : Fin M => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
          (fun i : Fin M => S ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) hcard'
        unfold kSmallestSum at ih
        omega

/-! ### Path 1, Path 2, and Path 3 Global MAP Optimality Certificates -/

/-- **Path 1 Strict Singleton Certificate**:
    If `syn ≠ 0`, `col mStar = syn`, `w mStar < pairFloor w` (`M ≥ 2`), and `mStar`
    strictly beats every other compatible singleton, then `{mStar}` has **strictly smaller
    weight than EVERY other syndrome-compatible subset `S ⊆ Fin M`**! -/
theorem path1_strict_singleton_optimal {D M : Nat}
    (w : Fin M → Nat) (col : Fin M → BitVec D) (syn : BitVec D) (mStar : Fin M)
    (hsyn : syn ≠ 0#D)
    (hmatch : col mStar = syn)
    (hfloor : w mStar < pairFloor w)
    (hsingle : ∀ m : Fin M, m ≠ mStar → col m = syn → w mStar < w m) :
    IsCompatible col syn (singletonSubset mStar) ∧
    ∀ S : SubsetM M, IsCompatible col syn S → S ≠ singletonSubset mStar →
      subsetWeight w (singletonSubset mStar) < subsetWeight w S := by
  have hcomp_star : IsCompatible col syn (singletonSubset mStar) := by
    unfold IsCompatible subsetSyndrome
    rw [xorSubset_singleton, hmatch]
  refine ⟨hcomp_star, fun S hcomp hne => ?_⟩
  rw [subsetWeight_singleton]
  have hcpos := card_pos_of_compatible_nonzero hsyn hcomp
  by_cases hc1 : card S = 1
  · obtain ⟨m, rfl⟩ := eq_singleton_of_card_one hc1
    have hne_m : m ≠ mStar := fun heq => hne (heq ▸ rfl)
    unfold IsCompatible subsetSyndrome at hcomp
    rw [xorSubset_singleton] at hcomp
    rw [subsetWeight_singleton]
    exact hsingle m hne_m hcomp
  · have hc2 : 2 ≤ card S := by omega
    have hpf := kSmallestSum_le_subsetWeight w S hc2
    unfold pairFloor at hfloor
    omega

/-- **Path 1 Observable-Unambiguous MAP Certificate** (matching `spacetime_decoder.cpp`):
    Even when multiple singletons tie for minimum cost `bestCost`, if all minimum-cost
    compatible singletons share observable `bestObs` and `bestCost < pairFloor w`, then
    `bestCost` is the global minimum weight across all $2^M$ subsets and EVERY global
    minimum-weight compatible subset induces `bestObs`. -/
theorem path1_certified_map {D M K : Nat}
    (w : Fin M → Nat) (col : Fin M → BitVec D) (obs : Fin M → BitVec K)
    (syn : BitVec D) (mStar : Fin M) (bestCost : Nat) (bestObs : BitVec K)
    (hsyn : syn ≠ 0#D)
    (hmatch : col mStar = syn)
    (hcost : w mStar = bestCost)
    (hobs : obs mStar = bestObs)
    (hfloor : bestCost < pairFloor w)
    (hmin1 : ∀ m : Fin M, col m = syn → bestCost ≤ w m)
    (hunamb1 : ∀ m : Fin M, col m = syn → w m = bestCost → obs m = bestObs) :
    (∃ S₀, IsCompatible col syn S₀ ∧ subsetWeight w S₀ = bestCost ∧ subsetObs obs S₀ = bestObs) ∧
    ∀ S : SubsetM M, IsCompatible col syn S →
      bestCost ≤ subsetWeight w S ∧
      (subsetWeight w S = bestCost → subsetObs obs S = bestObs) := by
  refine ⟨⟨singletonSubset mStar, ?_, ?_, ?_⟩, fun S hcomp => ?_⟩
  · unfold IsCompatible subsetSyndrome; rw [xorSubset_singleton, hmatch]
  · rw [subsetWeight_singleton, hcost]
  · unfold subsetObs; rw [xorSubset_singleton, hobs]
  · have hcpos := card_pos_of_compatible_nonzero hsyn hcomp
    by_cases hc1 : card S = 1
    · obtain ⟨m, rfl⟩ := eq_singleton_of_card_one hc1
      unfold IsCompatible subsetSyndrome at hcomp
      rw [xorSubset_singleton] at hcomp
      rw [subsetWeight_singleton]
      refine ⟨hmin1 m hcomp, fun hweq => ?_⟩
      unfold subsetObs
      rw [xorSubset_singleton]
      exact hunamb1 m hcomp hweq
    · have hc2 : 2 ≤ card S := by omega
      have hpf := kSmallestSum_le_subsetWeight w S hc2
      unfold pairFloor at hfloor
      exact ⟨by omega, fun hweq => absurd hweq (by omega)⟩

private theorem xor_solve_right {W : Nat} {x y s : BitVec W} (h : x ^^^ y = s) :
    y = s ^^^ x := by
  rw [← h, BitVec.xor_comm x y, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

private theorem xor_solve_left {W : Nat} {x y s : BitVec W} (h : x ^^^ y = s) :
    x = s ^^^ y := by
  rw [← h, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- **Path 2 Anchor-Detector Completeness Lemma (`pair_anchor_complete`)**:
    For any fired detector `anchor : Fin D` (`syn.getLsbD anchor = true`), every
    compatible pair `{m₁, m₂}` contains at least one mechanism incident to `anchor`
    with the partner matching `syn ^^^ col m_anchor`. -/
theorem pair_anchor_complete {D M : Nat}
    (col : Fin M → BitVec D) (syn : BitVec D) (anchor : Fin D)
    (hanc : syn.getLsbD anchor.val = true)
    {m₁ m₂ : Fin M} (h12 : m₁ ≠ m₂)
    (hcomp : IsCompatible col syn (pairSubset m₁ m₂)) :
    ∃ a b : Fin M, a ≠ b ∧ (col a).getLsbD anchor.val = true ∧
      col b = syn ^^^ col a ∧ pairSubset m₁ m₂ = pairSubset a b := by
  unfold IsCompatible subsetSyndrome at hcomp
  rw [xorSubset_pair col h12] at hcomp
  have hbit : ((col m₁ ^^^ col m₂).getLsbD anchor.val) = true := by
    rw [hcomp]; exact hanc
  rw [BitVec.getLsbD_xor] at hbit
  by_cases ha1 : (col m₁).getLsbD anchor.val = true
  · exact ⟨m₁, m₂, h12, ha1, xor_solve_right hcomp, rfl⟩
  · have ha2 : (col m₂).getLsbD anchor.val = true := by
      cases h1 : (col m₁).getLsbD anchor.val <;> cases h2 : (col m₂).getLsbD anchor.val <;>
        simp_all
    refine ⟨m₂, m₁, h12.symm, ha2, xor_solve_left hcomp, ?_⟩
    funext x; unfold pairSubset; cases decide (x = m₁) <;> cases decide (x = m₂) <;> rfl

/-- **Path 2 Certified Global MAP Optimality (`path2_certified_map`)**:
    Scanning singletons and `anchor`-incident pairs (`col a` touches `anchor`,
    `col b = syn ^^^ col a`) with `bestCost < tripleFloor w` and unambiguous minimum
    observable returns the global minimum-weight explanation across all $2^M$ subsets! -/
theorem path2_certified_map {D M K : Nat}
    (w : Fin M → Nat) (col : Fin M → BitVec D) (obs : Fin M → BitVec K)
    (syn : BitVec D) (anchor : Fin D) (SStar : SubsetM M)
    (bestCost : Nat) (bestObs : BitVec K)
    (hsyn : syn ≠ 0#D)
    (hanc : syn.getLsbD anchor.val = true)
    (hwit_comp : IsCompatible col syn SStar)
    (hwit_cost : subsetWeight w SStar = bestCost)
    (hwit_obs  : subsetObs obs SStar = bestObs)
    (hfloor : bestCost < tripleFloor w)
    (hscan1 : ∀ m : Fin M, col m = syn →
      bestCost ≤ w m ∧ (w m = bestCost → obs m = bestObs))
    (hscan2 : ∀ a b : Fin M, a ≠ b →
      (col a).getLsbD anchor.val = true → col b = syn ^^^ col a →
      bestCost ≤ w a + w b ∧ (w a + w b = bestCost → (obs a ^^^ obs b) = bestObs)) :
    (∃ S₀, IsCompatible col syn S₀ ∧ subsetWeight w S₀ = bestCost ∧ subsetObs obs S₀ = bestObs) ∧
    ∀ S : SubsetM M, IsCompatible col syn S →
      bestCost ≤ subsetWeight w S ∧
      (subsetWeight w S = bestCost → subsetObs obs S = bestObs) := by
  refine ⟨⟨SStar, hwit_comp, hwit_cost, hwit_obs⟩, fun S hcomp => ?_⟩
  have hcpos := card_pos_of_compatible_nonzero hsyn hcomp
  by_cases hc1 : card S = 1
  · obtain ⟨m, rfl⟩ := eq_singleton_of_card_one hc1
    unfold IsCompatible subsetSyndrome at hcomp
    rw [xorSubset_singleton] at hcomp
    rw [subsetWeight_singleton]
    unfold subsetObs
    rw [xorSubset_singleton]
    exact hscan1 m hcomp
  · by_cases hc2 : card S = 2
    · obtain ⟨m₁, m₂, h12, rfl⟩ := eq_pair_of_card_two hc2
      obtain ⟨a, b, hab, ha_bit, hb_col, hpair_eq⟩ :=
        pair_anchor_complete col syn anchor hanc h12 hcomp
      rw [hpair_eq, subsetWeight_pair w hab]
      unfold subsetObs
      rw [xorSubset_pair obs hab]
      exact hscan2 a b hab ha_bit hb_col
    · have hc3 : 3 ≤ card S := by omega
      have htf := kSmallestSum_le_subsetWeight w S hc3
      unfold tripleFloor at hfloor
      exact ⟨by omega, fun hweq => absurd hweq (by omega)⟩

/-- **Path 3 Anchor + Residual-Pivot Completeness & Zero-Residual Suboptimality**:
    Over strictly positive weights (`∀ m, 0 < w m`), for any fired `anchor : Fin D` and
    compatible triple `{m₁, m₂, m₃}`:
    - EITHER one member `a` already satisfies `col a = syn` (`residual = 0`), in which case
      singleton `{a}` is compatible with **strictly smaller weight** `w a < w m₁ + w m₂ + w m₃`,
    - OR there is an `anchor`-incident member `a` with nonzero residual `res = syn ^^^ col a ≠ 0#D`
      such that for ANY fired bit `pivot` of `res` (`pivotFn res`), one of the remaining two
      members `b` touches `pivot` and the third satisfies `col c = res ^^^ col b`! -/
theorem triple_anchor_pivot_complete {D M : Nat}
    (w : Fin M → Nat) (hw : ∀ m : Fin M, 0 < w m)
    (col : Fin M → BitVec D) (syn : BitVec D) (anchor : Fin D)
    (pivotFn : BitVec D → Fin D)
    (hpiv_spec : ∀ r : BitVec D, r ≠ 0#D → r.getLsbD (pivotFn r).val = true)
    (hanc : syn.getLsbD anchor.val = true)
    {m₁ m₂ m₃ : Fin M} (h12 : m₁ ≠ m₂) (h13 : m₁ ≠ m₃) (h23 : m₂ ≠ m₃)
    (hcomp : IsCompatible col syn (tripleSubset m₁ m₂ m₃)) :
    (∃ a : Fin M, col a = syn ∧ w a < subsetWeight w (tripleSubset m₁ m₂ m₃)) ∨
    (∃ a b c : Fin M, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (col a).getLsbD anchor.val = true ∧
      (syn ^^^ col a) ≠ 0#D ∧
      (col b).getLsbD (pivotFn (syn ^^^ col a)).val = true ∧
      col c = (syn ^^^ col a) ^^^ col b ∧
      tripleSubset m₁ m₂ m₃ = tripleSubset a b c) := by
  unfold IsCompatible subsetSyndrome at hcomp
  rw [xorSubset_triple col h12 h13 h23] at hcomp
  have hbit : ((col m₁ ^^^ col m₂ ^^^ col m₃).getLsbD anchor.val) = true := by
    rw [hcomp]; exact hanc
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_xor] at hbit
  have hex_anchor : ∃ a u v : Fin M, a ≠ u ∧ a ≠ v ∧ u ≠ v ∧
      (col a).getLsbD anchor.val = true ∧
      col a ^^^ col u ^^^ col v = syn ∧
      tripleSubset m₁ m₂ m₃ = tripleSubset a u v := by
    by_cases ha1 : (col m₁).getLsbD anchor.val = true
    · exact ⟨m₁, m₂, m₃, h12, h13, h23, ha1, hcomp, rfl⟩
    · by_cases ha2 : (col m₂).getLsbD anchor.val = true
      · refine ⟨m₂, m₁, m₃, h12.symm, h23, h13, ha2, ?_, ?_⟩
        · rw [BitVec.xor_comm (col m₂) (col m₁)]; exact hcomp
        · funext x; unfold tripleSubset
          cases decide (x = m₁) <;> cases decide (x = m₂) <;> cases decide (x = m₃) <;> rfl
      · have ha3 : (col m₃).getLsbD anchor.val = true := by
          cases h1 : (col m₁).getLsbD anchor.val <;>
          cases h2 : (col m₂).getLsbD anchor.val <;>
          cases h3 : (col m₃).getLsbD anchor.val <;> simp_all
        refine ⟨m₃, m₁, m₂, h13.symm, h23.symm, h12, ha3, ?_, ?_⟩
        · rw [← hcomp, BitVec.xor_comm (col m₃) (col m₁), BitVec.xor_assoc (col m₁) (col m₃) (col m₂),
              BitVec.xor_comm (col m₃) (col m₂), ← BitVec.xor_assoc]
        · funext x; unfold tripleSubset
          cases decide (x = m₁) <;> cases decide (x = m₂) <;> cases decide (x = m₃) <;> rfl
  obtain ⟨a, u, v, hau, hav, huv, ha_anc, hxor_auv, htrip_eq⟩ := hex_anchor
  by_cases hres0 : (syn ^^^ col a) = 0#D
  · left
    have hcola : col a = syn := by
      have h0 := xor_solve_right hres0
      rw [BitVec.zero_xor] at h0
      exact h0
    refine ⟨a, hcola, ?_⟩
    rw [htrip_eq, subsetWeight_triple w hau hav huv]
    have hwu := hw u
    have hwv := hw v
    omega
  · right
    have hpiv_bit : (syn ^^^ col a).getLsbD (pivotFn (syn ^^^ col a)).val = true :=
      hpiv_spec (syn ^^^ col a) hres0
    have hres_uv : col u ^^^ col v = syn ^^^ col a := by
      have hassoc : col a ^^^ (col u ^^^ col v) = syn := by
        rw [← BitVec.xor_assoc]; exact hxor_auv
      exact xor_solve_right hassoc
    have hpiv_uv : ((col u ^^^ col v).getLsbD (pivotFn (syn ^^^ col a)).val) = true := by
      rw [hres_uv]; exact hpiv_bit
    rw [BitVec.getLsbD_xor] at hpiv_uv
    by_cases hu_piv : (col u).getLsbD (pivotFn (syn ^^^ col a)).val = true
    · exact ⟨a, u, v, hau, hav, huv, ha_anc, hres0, hu_piv, xor_solve_right hres_uv, htrip_eq⟩
    · have hv_piv : (col v).getLsbD (pivotFn (syn ^^^ col a)).val = true := by
        cases h1 : (col u).getLsbD (pivotFn (syn ^^^ col a)).val <;>
        cases h2 : (col v).getLsbD (pivotFn (syn ^^^ col a)).val <;> simp_all
      refine ⟨a, v, u, hav, hau, huv.symm, ha_anc, hres0, hv_piv, xor_solve_left hres_uv, ?_⟩
      rw [htrip_eq]; funext x; unfold tripleSubset
      cases decide (x = a) <;> cases decide (x = u) <;> cases decide (x = v) <;> rfl

/-- **Path 3 Certified Global MAP Optimality (`path3_certified_map`)**:
    Over strictly positive weights (`∀ m, 0 < w m`), scanning singletons, `anchor`-incident
    pairs, and `anchor` + `pivotFn`-incident nonzero-residual triples with
    `bestCost < fourFloor w` and unambiguous minimum observable returns the exact global
    minimum-weight explanation across ALL $2^M$ subsets! -/
theorem path3_certified_map {D M K : Nat}
    (w : Fin M → Nat) (hw : ∀ m : Fin M, 0 < w m)
    (col : Fin M → BitVec D) (obs : Fin M → BitVec K)
    (syn : BitVec D) (anchor : Fin D) (pivotFn : BitVec D → Fin D)
    (hpiv_spec : ∀ r : BitVec D, r ≠ 0#D → r.getLsbD (pivotFn r).val = true)
    (SStar : SubsetM M) (bestCost : Nat) (bestObs : BitVec K)
    (hsyn : syn ≠ 0#D)
    (hanc : syn.getLsbD anchor.val = true)
    (hwit_comp : IsCompatible col syn SStar)
    (hwit_cost : subsetWeight w SStar = bestCost)
    (hwit_obs  : subsetObs obs SStar = bestObs)
    (hfloor : bestCost < fourFloor w)
    (hscan1 : ∀ m : Fin M, col m = syn →
      bestCost ≤ w m ∧ (w m = bestCost → obs m = bestObs))
    (hscan2 : ∀ a b : Fin M, a ≠ b →
      (col a).getLsbD anchor.val = true → col b = syn ^^^ col a →
      bestCost ≤ w a + w b ∧ (w a + w b = bestCost → (obs a ^^^ obs b) = bestObs))
    (hscan3 : ∀ a b c : Fin M, a ≠ b → a ≠ c → b ≠ c →
      (col a).getLsbD anchor.val = true →
      (syn ^^^ col a) ≠ 0#D →
      (col b).getLsbD (pivotFn (syn ^^^ col a)).val = true →
      col c = (syn ^^^ col a) ^^^ col b →
      bestCost ≤ w a + w b + w c ∧
      (w a + w b + w c = bestCost → (obs a ^^^ obs b ^^^ obs c) = bestObs)) :
    (∃ S₀, IsCompatible col syn S₀ ∧ subsetWeight w S₀ = bestCost ∧ subsetObs obs S₀ = bestObs) ∧
    ∀ S : SubsetM M, IsCompatible col syn S →
      bestCost ≤ subsetWeight w S ∧
      (subsetWeight w S = bestCost → subsetObs obs S = bestObs) := by
  refine ⟨⟨SStar, hwit_comp, hwit_cost, hwit_obs⟩, fun S hcomp => ?_⟩
  have hcpos := card_pos_of_compatible_nonzero hsyn hcomp
  by_cases hc1 : card S = 1
  · obtain ⟨m, rfl⟩ := eq_singleton_of_card_one hc1
    unfold IsCompatible subsetSyndrome at hcomp
    rw [xorSubset_singleton] at hcomp
    rw [subsetWeight_singleton]
    unfold subsetObs; rw [xorSubset_singleton]
    exact hscan1 m hcomp
  · by_cases hc2 : card S = 2
    · obtain ⟨m₁, m₂, h12, rfl⟩ := eq_pair_of_card_two hc2
      obtain ⟨a, b, hab, ha_bit, hb_col, hpair_eq⟩ :=
        pair_anchor_complete col syn anchor hanc h12 hcomp
      rw [hpair_eq, subsetWeight_pair w hab]
      unfold subsetObs; rw [xorSubset_pair obs hab]
      exact hscan2 a b hab ha_bit hb_col
    · by_cases hc3 : card S = 3
      · obtain ⟨m₁, m₂, m₃, h12, h13, h23, rfl⟩ := eq_triple_of_card_three hc3
        rcases triple_anchor_pivot_complete w hw col syn anchor pivotFn hpiv_spec
                 hanc h12 h13 h23 hcomp with
          ⟨a, hcola, hstrict⟩ |
          ⟨a, b, c, hab, hac, hbc, ha_anc, hres0, hb_piv, hc_col, htrip_eq⟩
        · have h1 := (hscan1 a hcola).1
          exact ⟨by omega, fun hweq => absurd hweq (by omega)⟩
        · rw [htrip_eq, subsetWeight_triple w hab hac hbc]
          unfold subsetObs; rw [xorSubset_triple obs hab hac hbc]
          exact hscan3 a b c hab hac hbc ha_anc hres0 hb_piv hc_col
      · have hc4 : 4 ≤ card S := by omega
        have hff := kSmallestSum_le_subsetWeight w S hc4
        unfold fourFloor at hfloor
        exact ⟨by omega, fun hweq => absurd hweq (by omega)⟩

/-! ### Formalization of the 4-Mechanism `30 vs 9 + 9 + 9 = 27` Counterexample -/

/-- Detector columns of the 4-mechanism counterexample (`D = 4, M = 4, K = 1`):
    - `m = 0`: `{0, 1}` (`0b0011#4`), weight `30`, observable `0`
    - `m = 1`: `{0, 2}` (`0b0101#4`), weight `9`,  observable `1`
    - `m = 2`: `{1, 3}` (`0b1010#4`), weight `9`,  observable `0`
    - `m = 3`: `{2, 3}` (`0b1100#4`), weight `9`,  observable `0` -/
def ceCol : Fin 4 → BitVec 4
  | ⟨0, _⟩ => 0b0011#4
  | ⟨1, _⟩ => 0b0101#4
  | ⟨2, _⟩ => 0b1010#4
  | ⟨3, _⟩ => 0b1100#4

def ceWeight : Fin 4 → Nat
  | ⟨0, _⟩ => 30
  | ⟨1, _⟩ => 9
  | ⟨2, _⟩ => 9
  | ⟨3, _⟩ => 9

def ceObs : Fin 4 → BitVec 1
  | ⟨0, _⟩ => 0#1
  | ⟨1, _⟩ => 1#1
  | ⟨2, _⟩ => 0#1
  | ⟨3, _⟩ => 0#1

/-- Fired syndrome `{0, 1}` (`0b0011#4`). -/
def ceSyn : BitVec 4 := 0b0011#4

/-- Restricted local tile predicate: mechanism `m` touches at least one fired detector in `ceSyn`. -/
def inRestrictedTile (m : Fin 4) : Bool :=
  decide ((ceCol m &&& ceSyn) ≠ 0#4)

/-- A subset `S` lies inside the restricted local tile iff `S` uses only mechanisms touching `ceSyn`. -/
def SubsetInRestrictedTile (S : SubsetM 4) : Bool :=
  ([0, 1, 2, 3] : List (Fin 4)).all (fun m => !(S m) || inRestrictedTile m)

/-- All 16 subsets of `Fin 4`, for exhaustive kernel verification of global optimality. -/
def allSubsets4 : List (SubsetM 4) :=
  let bs := [false, true]
  bs.flatMap fun b0 =>
  bs.flatMap fun b1 =>
  bs.flatMap fun b2 =>
  bs.map fun b3 =>
    fun (m : Fin 4) => match m with
      | ⟨0, _⟩ => b0 | ⟨1, _⟩ => b1 | ⟨2, _⟩ => b2 | ⟨3, _⟩ => b3

/-- **Counterexample Theorem (`counterexample_30_vs_27_restricted_slack_fails`)**:
    1. All 4 mechanisms have strictly positive weights (`30, 9, 9, 9 > 0`).
    2. Mechanism `3` (`{2, 3}`) is excluded from the restricted local tile (`inRestrictedTile 3 = false`),
       leaving `singletonSubset 0` (cost `30`, observable `0#1`) as the UNIQUE compatible subset
       inside the restricted tile, and `30 ≤ 37` passes the restricted-tile slack gate!
    3. Yet globally, `tripleSubset 1 2 3` is syndrome-compatible (`0b0101 ^^^ 0b1010 ^^^ 0b1100 = 0b0011`)
       with **strictly lower cost `9 + 9 + 9 = 27 < 30`** and **opposite observable `1#1 ≠ 0#1`**!
    4. Meanwhile, the Lean-certified cost-floor gates reject `{0}` at Path 1 (`¬(30 < pairFloor = 18)`)
       and Path 2 (`¬(30 < tripleFloor = 27)`), and accept `{1, 2, 3}` at Path 3 (`27 < fourFloor = 57`)! -/
theorem counterexample_30_vs_27_restricted_slack_fails :
    (∀ m : Fin 4, 0 < ceWeight m) ∧
    inRestrictedTile 3 = false ∧
    subsetSyndrome ceCol (singletonSubset 0) = ceSyn ∧
    subsetWeight ceWeight (singletonSubset 0) = 30 ∧
    subsetObs ceObs (singletonSubset 0) = 0#1 ∧
    (30 ≤ 37) ∧
    (allSubsets4.all fun S =>
      !(SubsetInRestrictedTile S && decide (subsetSyndrome ceCol S = ceSyn)) ||
      decide (subsetWeight ceWeight S == 30 && subsetObs ceObs S == 0#1)) = true ∧
    subsetSyndrome ceCol (tripleSubset 1 2 3) = ceSyn ∧
    subsetWeight ceWeight (tripleSubset 1 2 3) = 27 ∧
    subsetObs ceObs (tripleSubset 1 2 3) = 1#1 ∧
    pairFloor ceWeight = 18 ∧
    tripleFloor ceWeight = 27 ∧
    fourFloor ceWeight = 57 ∧
    ¬ (30 < pairFloor ceWeight) ∧
    ¬ (30 < tripleFloor ceWeight) ∧
    (27 < fourFloor ceWeight) ∧
    (allSubsets4.all fun S =>
      !decide (subsetSyndrome ceCol S = ceSyn) ||
      decide (27 ≤ subsetWeight ceWeight S &&
              (subsetWeight ceWeight S != 27 || subsetObs ceObs S == 1#1))) = true := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide⟩

end ZeroIdleQldpc.CertifiedDecoder
