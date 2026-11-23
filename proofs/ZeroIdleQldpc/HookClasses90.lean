/-
  ZeroIdleQldpc.HookClasses90
  ===========================
  Formal verification of the 360-class bare vs 90-class augmented hook-equivalence
  partition of S_6 (all 6! = 720 gate orderings of a weight-6 check):
    - CNOT wires are represented as `BitVec 6` modulo the weight-6 stabilizer
      vector `allOnes6 = 0b111111#6`.
    - Bare suffix hook sets `{ h_s(p) mod 0b111111 | 0 ≤ s ≤ 5 }` partition the
      720 permutations of `Fin 6` into **360** equivalence classes (each of size 2,
      identifying `p` with its full reversal `revPerm p`).
    - Adjoining single-qubit data faults `{ e_u mod 0b111111 | u ∈ Fin 6 }`
      collapses the 720 permutations to **90** equivalence classes (each of size 8).
    - Two permutations induce the exact same augmented fault set **if and only if**
      they share the same reversal-coupled `coset90Key`!
-/

namespace ZeroIdleQldpc.HookClasses90

/-- All-ones stabilizer check vector `0b111111` on a weight-6 check. -/
def allOnes6 : BitVec 6 := 0b111111#6

/-- Single-qubit fault mask `e_u` on wire `u ∈ Fin 6`. -/
def wireBit (u : Fin 6) : BitVec 6 :=
  match u with
  | ⟨0, _⟩ => 0b000001#6
  | ⟨1, _⟩ => 0b000010#6
  | ⟨2, _⟩ => 0b000100#6
  | ⟨3, _⟩ => 0b001000#6
  | ⟨4, _⟩ => 0b010000#6
  | ⟨5, _⟩ => 0b100000#6

/-- Canonical coset representative of `v : BitVec 6` modulo `allOnes6 = 0b111111#6`.
    Clears bit 5 by XORing `0b111111#6` when bit 5 is set (`= min(v, v ^^^ 0b111111)`). -/
def canonCoset (v : BitVec 6) : BitVec 6 :=
  if v.getLsbD 5 then v ^^^ allOnes6 else v

private def fin6List : List (Fin 6) := [0, 1, 2, 3, 4, 5]

private theorem mem_fin6List (u : Fin 6) : u ∈ fin6List := by
  match u with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ => simp [fin6List]

private theorem fin6_all_spec {f : Fin 6 → Bool} (h : fin6List.all f = true) (u : Fin 6) :
    f u = true :=
  List.all_eq_true.mp h u (mem_fin6List u)

private theorem fin6_all2_spec {f : Fin 6 → Fin 6 → Bool}
    (h : (fin6List.all fun u => fin6List.all fun v => f u v) = true) (u v : Fin 6) :
    f u v = true :=
  fin6_all_spec (fin6_all_spec h u) v

private theorem xor_allOnes_invol (v : BitVec 6) : (v ^^^ allOnes6) ^^^ allOnes6 = v := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

private theorem canonCoset_bit5_false (v : BitVec 6) : (canonCoset v).getLsbD 5 = false := by
  have ha5 : allOnes6.getLsbD 5 = true := rfl
  unfold canonCoset
  cases h : v.getLsbD 5
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact h
  · simp only [↓reduceIte]
    rw [BitVec.getLsbD_xor, h, ha5]
    rfl

theorem canonCoset_idem (v : BitVec 6) : canonCoset (canonCoset v) = canonCoset v := by
  change (if (canonCoset v).getLsbD 5 then canonCoset v ^^^ allOnes6 else canonCoset v) = canonCoset v
  rw [canonCoset_bit5_false v]
  rfl

theorem canonCoset_xor_allOnes (v : BitVec 6) : canonCoset (v ^^^ allOnes6) = canonCoset v := by
  have ha5 : allOnes6.getLsbD 5 = true := by simp [allOnes6]
  unfold canonCoset
  rw [BitVec.getLsbD_xor, ha5]
  cases v.getLsbD 5 <;> simp [xor_allOnes_invol]

/-- Two 6-bit fault masks represent the same coset mod `0b111111` iff they are equal
    or bitwise complements (`u = v ∨ u = v ^^^ 0b111111#6`). -/
theorem canonCoset_eq_iff (u v : BitVec 6) :
    canonCoset u = canonCoset v ↔ (u = v ∨ u = v ^^^ allOnes6) := by
  constructor
  · intro h
    unfold canonCoset at h
    by_cases hu : u.getLsbD 5 = true <;> by_cases hv : v.getLsbD 5 = true
    · simp only [hu, hv, ↓reduceIte] at h
      left
      have h' := congrArg (· ^^^ allOnes6) h
      rw [xor_allOnes_invol, xor_allOnes_invol] at h'
      exact h'
    · simp only [hu, hv, Bool.false_eq_true, ↓reduceIte] at h
      right
      have h' := congrArg (· ^^^ allOnes6) h
      rw [xor_allOnes_invol] at h'
      exact h'
    · simp only [hu, hv, Bool.false_eq_true, ↓reduceIte] at h
      exact Or.inr h
    · simp only [hu, hv, Bool.false_eq_true, ↓reduceIte] at h
      exact Or.inl h
  · rintro (rfl | rfl)
    · rfl
    · exact canonCoset_xor_allOnes v

/-! ### 32-Coset Set Representation & Extensionality -/

structure C2  where (f t : Bool)
structure C4  where (f t : C2)
structure C8  where (f t : C4)
structure C16 where (f t : C8)

/-- Exact subset of the 32 canonical cosets `{ c : BitVec 6 | c.getLsbD 5 = false }`. -/
structure CosetSet where
  f : C16
  t : C16

def emptyCosetSet : CosetSet :=
  let z2  : C2  := ⟨false, false⟩
  let z4  : C4  := ⟨z2, z2⟩
  let z8  : C8  := ⟨z4, z4⟩
  let z16 : C16 := ⟨z8, z8⟩
  ⟨z16, z16⟩

private def getC2 (x : C2) (b0 : Bool) : Bool := if b0 then x.t else x.f
private def getC4 (x : C4) (b1 b0 : Bool) : Bool := getC2 (if b1 then x.t else x.f) b0
private def getC8 (x : C8) (b2 b1 b0 : Bool) : Bool := getC4 (if b2 then x.t else x.f) b1 b0
private def getC16 (x : C16) (b3 b2 b1 b0 : Bool) : Bool := getC8 (if b3 then x.t else x.f) b2 b1 b0

/-- Test whether the coset of `v : BitVec 6` (mod `0b111111`) belongs to `s : CosetSet`. -/
def memCosetSet (s : CosetSet) (v : BitVec 6) : Bool :=
  let c := canonCoset v
  getC16 (if c.getLsbD 4 then s.t else s.f)
    (c.getLsbD 3) (c.getLsbD 2) (c.getLsbD 1) (c.getLsbD 0)

private def setC2 (x : C2) (b0 : Bool) : C2 := if b0 then ⟨x.f, true⟩ else ⟨true, x.t⟩
private def setC4 (x : C4) (b1 b0 : Bool) : C4 := if b1 then ⟨x.f, setC2 x.t b0⟩ else ⟨setC2 x.f b0, x.t⟩
private def setC8 (x : C8) (b2 b1 b0 : Bool) : C8 := if b2 then ⟨x.f, setC4 x.t b1 b0⟩ else ⟨setC4 x.f b1 b0, x.t⟩
private def setC16 (x : C16) (b3 b2 b1 b0 : Bool) : C16 :=
  if b3 then ⟨x.f, setC8 x.t b2 b1 b0⟩ else ⟨setC8 x.f b2 b1 b0, x.t⟩

/-- Insert the coset of `v : BitVec 6` (mod `0b111111`) into `s : CosetSet`. -/
def insertCoset (s : CosetSet) (v : BitVec 6) : CosetSet :=
  let c := canonCoset v
  if c.getLsbD 4 then
    ⟨s.f, setC16 s.t (c.getLsbD 3) (c.getLsbD 2) (c.getLsbD 1) (c.getLsbD 0)⟩
  else
    ⟨setC16 s.f (c.getLsbD 3) (c.getLsbD 2) (c.getLsbD 1) (c.getLsbD 0), s.t⟩

private def unionC2 (a b : C2) : C2 := ⟨a.f || b.f, a.t || b.t⟩
private def unionC4 (a b : C4) : C4 := ⟨unionC2 a.f b.f, unionC2 a.t b.t⟩
private def unionC8 (a b : C8) : C8 := ⟨unionC4 a.f b.f, unionC4 a.t b.t⟩
private def unionC16 (a b : C16) : C16 := ⟨unionC8 a.f b.f, unionC8 a.t b.t⟩

/-- Set union of two `CosetSet`s. -/
def unionCosetSet (a b : CosetSet) : CosetSet :=
  ⟨unionC16 a.f b.f, unionC16 a.t b.t⟩

theorem mem_emptyCosetSet (w : BitVec 6) : memCosetSet emptyCosetSet w = false := by
  unfold memCosetSet emptyCosetSet getC16 getC8 getC4 getC2
  dsimp only
  cases (canonCoset w).getLsbD 4 <;> cases (canonCoset w).getLsbD 3 <;>
  cases (canonCoset w).getLsbD 2 <;> cases (canonCoset w).getLsbD 1 <;>
  cases (canonCoset w).getLsbD 0 <;> rfl

private theorem getC2_setC2 (x : C2) (a b : Bool) :
    getC2 (setC2 x a) b = (getC2 x b || (b == a)) := by
  cases x with | mk xf xt =>
  cases xf <;> cases xt <;> cases a <;> cases b <;> rfl

private theorem getC4_setC4 (x : C4) (a1 a0 b1 b0 : Bool) :
    getC4 (setC4 x a1 a0) b1 b0 = (getC4 x b1 b0 || ((b1 == a1) && (b0 == a0))) := by
  cases x; cases a1 <;> cases b1 <;> simp [getC4, setC4, getC2_setC2]

private theorem getC8_setC8 (x : C8) (a2 a1 a0 b2 b1 b0 : Bool) :
    getC8 (setC8 x a2 a1 a0) b2 b1 b0 =
    (getC8 x b2 b1 b0 || ((b2 == a2) && ((b1 == a1) && (b0 == a0)))) := by
  cases x; cases a2 <;> cases b2 <;> simp [getC8, setC8, getC4_setC4]

private theorem getC16_setC16 (x : C16) (a3 a2 a1 a0 b3 b2 b1 b0 : Bool) :
    getC16 (setC16 x a3 a2 a1 a0) b3 b2 b1 b0 =
    (getC16 x b3 b2 b1 b0 || ((b3 == a3) && ((b2 == a2) && ((b1 == a1) && (b0 == a0))))) := by
  cases x; cases a3 <;> cases b3 <;> simp [getC16, setC16, getC8_setC8]

private theorem bitvec6_eq_of_bits {u v : BitVec 6}
    (h5 : u.getLsbD 5 = v.getLsbD 5) (h4 : u.getLsbD 4 = v.getLsbD 4)
    (h3 : u.getLsbD 3 = v.getLsbD 3) (h2 : u.getLsbD 2 = v.getLsbD 2)
    (h1 : u.getLsbD 1 = v.getLsbD 1) (h0 : u.getLsbD 0 = v.getLsbD 0) : u = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  match i, hi with
  | 0, _ => exact h0 | 1, _ => exact h1 | 2, _ => exact h2
  | 3, _ => exact h3 | 4, _ => exact h4 | 5, _ => exact h5

private theorem canonCoset_five_bits_eq (w v : BitVec 6) :
    (((canonCoset w).getLsbD 4 == (canonCoset v).getLsbD 4) &&
     (((canonCoset w).getLsbD 3 == (canonCoset v).getLsbD 3) &&
      (((canonCoset w).getLsbD 2 == (canonCoset v).getLsbD 2) &&
       (((canonCoset w).getLsbD 1 == (canonCoset v).getLsbD 1) &&
        ((canonCoset w).getLsbD 0 == (canonCoset v).getLsbD 0))))) =
    decide (canonCoset w = canonCoset v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro ⟨e4, e3, e2, e1, e0⟩
    exact bitvec6_eq_of_bits
      ((canonCoset_bit5_false w).trans (canonCoset_bit5_false v).symm)
      e4 e3 e2 e1 e0
  · intro heq; rw [heq]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem mem_insertCoset (s : CosetSet) (v w : BitVec 6) :
    memCosetSet (insertCoset s v) w = (memCosetSet s w || decide (canonCoset w = canonCoset v)) := by
  rw [← canonCoset_five_bits_eq w v]
  unfold memCosetSet insertCoset
  dsimp only
  cases s with | mk sf st =>
  cases (canonCoset v).getLsbD 4 <;> cases (canonCoset w).getLsbD 4
  · simp [getC16_setC16]
  · simp
  · simp
  · simp [getC16_setC16]

private theorem getC2_unionC2 (a b : C2) (b0 : Bool) :
    getC2 (unionC2 a b) b0 = (getC2 a b0 || getC2 b b0) := by
  cases a; cases b; cases b0 <;> rfl

private theorem getC4_unionC4 (a b : C4) (b1 b0 : Bool) :
    getC4 (unionC4 a b) b1 b0 = (getC4 a b1 b0 || getC4 b b1 b0) := by
  cases a; cases b; cases b1 <;> simp [getC4, unionC4, getC2_unionC2]

private theorem getC8_unionC8 (a b : C8) (b2 b1 b0 : Bool) :
    getC8 (unionC8 a b) b2 b1 b0 = (getC8 a b2 b1 b0 || getC8 b b2 b1 b0) := by
  cases a; cases b; cases b2 <;> simp [getC8, unionC8, getC4_unionC4]

private theorem getC16_unionC16 (a b : C16) (b3 b2 b1 b0 : Bool) :
    getC16 (unionC16 a b) b3 b2 b1 b0 = (getC16 a b3 b2 b1 b0 || getC16 b b3 b2 b1 b0) := by
  cases a; cases b; cases b3 <;> simp [getC16, unionC16, getC8_unionC8]

theorem mem_unionCosetSet (a b : CosetSet) (w : BitVec 6) :
    memCosetSet (unionCosetSet a b) w = (memCosetSet a w || memCosetSet b w) := by
  unfold memCosetSet unionCosetSet
  dsimp only
  cases (canonCoset w).getLsbD 4 <;> simp [getC16_unionC16]

private def vecOf5Bits (b4 b3 b2 b1 b0 : Bool) : BitVec 6 :=
  BitVec.ofNat 6
    ((if b4 then 16 else 0) + (if b3 then 8 else 0) +
     (if b2 then 4 else 0) + (if b1 then 2 else 0) + (if b0 then 1 else 0))

private def bList : List Bool := [false, true]

private theorem mem_bList (b : Bool) : b ∈ bList := by cases b <;> simp [bList]

private theorem b_all_spec {f : Bool → Bool} (h : bList.all f = true) (b : Bool) : f b = true :=
  List.all_eq_true.mp h b (mem_bList b)

private theorem canon_vecOf5Bits (b4 b3 b2 b1 b0 : Bool) :
    let c := canonCoset (vecOf5Bits b4 b3 b2 b1 b0)
    c.getLsbD 4 = b4 ∧ c.getLsbD 3 = b3 ∧ c.getLsbD 2 = b2 ∧ c.getLsbD 1 = b1 ∧ c.getLsbD 0 = b0 := by
  have h : (bList.all fun b4 => bList.all fun b3 => bList.all fun b2 =>
            bList.all fun b1 => bList.all fun b0 =>
              let c := canonCoset (vecOf5Bits b4 b3 b2 b1 b0)
              (c.getLsbD 4 == b4) && (c.getLsbD 3 == b3) && (c.getLsbD 2 == b2) &&
              (c.getLsbD 1 == b1) && (c.getLsbD 0 == b0)) = true := by decide
  have hb := b_all_spec (b_all_spec (b_all_spec (b_all_spec (b_all_spec h b4) b3) b2) b1) b0
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  exact ⟨hb.1.1.1.1, hb.1.1.1.2, hb.1.1.2, hb.1.2, hb.2⟩

private theorem c2_ext {a b : C2} (h : ∀ b0, getC2 a b0 = getC2 b b0) : a = b := by
  cases a; cases b
  have e0 : _ = _ := h false
  have e1 : _ = _ := h true
  simp only [getC2, Bool.false_eq_true, ↓reduceIte] at e0 e1
  rw [e0, e1]

private theorem c4_ext {a b : C4} (h : ∀ b1 b0, getC4 a b1 b0 = getC4 b b1 b0) : a = b := by
  cases a; cases b
  have e0 := c2_ext (fun b0 => h false b0)
  have e1 := c2_ext (fun b0 => h true b0)
  simp only [Bool.false_eq_true, ↓reduceIte] at e0 e1
  rw [e0, e1]

private theorem c8_ext {a b : C8} (h : ∀ b2 b1 b0, getC8 a b2 b1 b0 = getC8 b b2 b1 b0) : a = b := by
  cases a; cases b
  have e0 := c4_ext (fun b1 b0 => h false b1 b0)
  have e1 := c4_ext (fun b1 b0 => h true b1 b0)
  simp only [Bool.false_eq_true, ↓reduceIte] at e0 e1
  rw [e0, e1]

private theorem c16_ext {a b : C16} (h : ∀ b3 b2 b1 b0, getC16 a b3 b2 b1 b0 = getC16 b b3 b2 b1 b0) : a = b := by
  cases a; cases b
  have e0 := c8_ext (fun b2 b1 b0 => h false b2 b1 b0)
  have e1 := c8_ext (fun b2 b1 b0 => h true b2 b1 b0)
  simp only [Bool.false_eq_true, ↓reduceIte] at e0 e1
  rw [e0, e1]

/-- Two `CosetSet`s are equal iff they contain the exact same `BitVec 6` cosets. -/
theorem CosetSet.ext {s₁ s₂ : CosetSet} (h : ∀ v : BitVec 6, memCosetSet s₁ v = memCosetSet s₂ v) :
    s₁ = s₂ := by
  cases s₁ with | mk f1 t1 =>
  cases s₂ with | mk f2 t2 =>
  have hf : f1 = f2 := c16_ext fun b3 b2 b1 b0 => by
    have hv := h (vecOf5Bits false b3 b2 b1 b0)
    obtain ⟨e4, e3, e2, e1, e0⟩ := canon_vecOf5Bits false b3 b2 b1 b0
    unfold memCosetSet at hv
    dsimp only at e4 e3 e2 e1 e0 hv
    rw [e4, e3, e2, e1, e0] at hv
    simpa using hv
  have ht : t1 = t2 := c16_ext fun b3 b2 b1 b0 => by
    have hv := h (vecOf5Bits true b3 b2 b1 b0)
    obtain ⟨e4, e3, e2, e1, e0⟩ := canon_vecOf5Bits true b3 b2 b1 b0
    unfold memCosetSet at hv
    dsimp only at e4 e3 e2 e1 e0 hv
    rw [e4, e3, e2, e1, e0] at hv
    simpa using hv
  subst hf ht; rfl

/-! ### Permutations of `Fin 6` ($S_6$, Order $6! = 720$) & Hook Fault Sets -/

/-- A 6-wire gate ordering `(p0, p1, p2, p3, p4, p5)` of `Fin 6`. -/
structure Perm6 where
  p0 : Fin 6
  p1 : Fin 6
  p2 : Fin 6
  p3 : Fin 6
  p4 : Fin 6
  p5 : Fin 6
  deriving DecidableEq, Repr

/-- Validity predicate for `Perm6`: all 6 entries are pairwise distinct. -/
def IsPerm6 (p : Perm6) : Bool :=
  (p.p1 != p.p0) &&
  (p.p2 != p.p0 && p.p2 != p.p1) &&
  (p.p3 != p.p0 && p.p3 != p.p1 && p.p3 != p.p2) &&
  (p.p4 != p.p0 && p.p4 != p.p1 && p.p4 != p.p2 && p.p4 != p.p3) &&
  (p.p5 != p.p0 && p.p5 != p.p1 && p.p5 != p.p2 && p.p5 != p.p3 && p.p5 != p.p4)

/-- Suffix hook mask `h_s(p)` for step `s ∈ Fin 6` (`0 ≤ s ≤ 5`). -/
def suffixHook (p : Perm6) (s : Fin 6) : BitVec 6 :=
  let h5 := wireBit p.p5
  let h4 := h5 ||| wireBit p.p4
  let h3 := h4 ||| wireBit p.p3
  let h2 := h3 ||| wireBit p.p2
  let h1 := h2 ||| wireBit p.p1
  let h0 := h1 ||| wireBit p.p0
  match s with
  | ⟨0, _⟩ => h0 | ⟨1, _⟩ => h1 | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3 | ⟨4, _⟩ => h4 | ⟨5, _⟩ => h5

/-- Bare suffix hook coset set `{ h_s(p) mod 0b111111 | 0 ≤ s ≤ 5 }`. -/
def bareHookSet (p : Perm6) : CosetSet :=
  let s := insertCoset emptyCosetSet (suffixHook p 0)
  let s := insertCoset s (suffixHook p 1)
  let s := insertCoset s (suffixHook p 2)
  let s := insertCoset s (suffixHook p 3)
  let s := insertCoset s (suffixHook p 4)
  insertCoset s (suffixHook p 5)

/-- Single-qubit data-fault coset set `{ e_u mod 0b111111 | u ∈ Fin 6 }`. -/
def singleDataSet : CosetSet :=
  let s := insertCoset emptyCosetSet (wireBit 0)
  let s := insertCoset s (wireBit 1)
  let s := insertCoset s (wireBit 2)
  let s := insertCoset s (wireBit 3)
  let s := insertCoset s (wireBit 4)
  insertCoset s (wireBit 5)

/-- Augmented hook+data fault set `{ h_s(p) mod 0b111111 | 0 ≤ s ≤ 5 } ∪ { e_u mod 0b111111 | u ∈ Fin 6 }`. -/
def augmentedHookSet (p : Perm6) : CosetSet :=
  unionCosetSet (bareHookSet p) singleDataSet

theorem mem_singleDataSet_wireBit (u : Fin 6) :
    memCosetSet singleDataSet (wireBit u) = true := by
  unfold singleDataSet
  match u with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ => simp [mem_insertCoset]

/-! ### Canonical Keys (`coset90Key`, `canonBarePerm`, `canonAugPerm`) -/

def permLt (a b : Perm6) : Bool :=
  if a.p0 != b.p0 then a.p0 < b.p0
  else if a.p1 != b.p1 then a.p1 < b.p1
  else if a.p2 != b.p2 then a.p2 < b.p2
  else if a.p3 != b.p3 then a.p3 < b.p3
  else if a.p4 != b.p4 then a.p4 < b.p4
  else a.p5 < b.p5

private theorem permLt_irrefl (a : Perm6) : permLt a a = false := by
  unfold permLt; simp

private theorem permLt_asymm {a b : Perm6} (h : permLt a b = true) : permLt b a = false := by
  unfold permLt at h ⊢
  by_cases e0 : a.p0 = b.p0
  · simp only [e0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases e1 : a.p1 = b.p1
    · simp only [e1, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases e2 : a.p2 = b.p2
      · simp only [e2, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases e3 : a.p3 = b.p3
        · simp only [e3, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases e4 : a.p4 = b.p4
          · simp only [e4, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
            simp only [decide_eq_true_eq] at h
            exact decide_eq_false (by change ¬(b.p5.val < a.p5.val); have : a.p5.val < b.p5.val := h; omega)
          · rw [bne_iff_ne.mpr e4] at h; rw [bne_iff_ne.mpr (Ne.symm e4)]
            simp only [↓reduceIte, decide_eq_true_eq] at h ⊢
            exact decide_eq_false (by change ¬(b.p4.val < a.p4.val); have : a.p4.val < b.p4.val := h; omega)
        · rw [bne_iff_ne.mpr e3] at h; rw [bne_iff_ne.mpr (Ne.symm e3)]
          simp only [↓reduceIte, decide_eq_true_eq] at h ⊢
          exact decide_eq_false (by change ¬(b.p3.val < a.p3.val); have : a.p3.val < b.p3.val := h; omega)
      · rw [bne_iff_ne.mpr e2] at h; rw [bne_iff_ne.mpr (Ne.symm e2)]
        simp only [↓reduceIte, decide_eq_true_eq] at h ⊢
        exact decide_eq_false (by change ¬(b.p2.val < a.p2.val); have : a.p2.val < b.p2.val := h; omega)
    · rw [bne_iff_ne.mpr e1] at h; rw [bne_iff_ne.mpr (Ne.symm e1)]
      simp only [↓reduceIte, decide_eq_true_eq] at h ⊢
      exact decide_eq_false (by change ¬(b.p1.val < a.p1.val); have : a.p1.val < b.p1.val := h; omega)
  · rw [bne_iff_ne.mpr e0] at h; rw [bne_iff_ne.mpr (Ne.symm e0)]
    simp only [↓reduceIte, decide_eq_true_eq] at h ⊢
    exact decide_eq_false (by change ¬(b.p0.val < a.p0.val); have : a.p0.val < b.p0.val := h; omega)

private theorem permLt_total {a b : Perm6} (hne : a ≠ b) : permLt a b = true ∨ permLt b a = true := by
  unfold permLt
  by_cases e0 : a.p0 = b.p0
  · simp only [e0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    by_cases e1 : a.p1 = b.p1
    · simp only [e1, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      by_cases e2 : a.p2 = b.p2
      · simp only [e2, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        by_cases e3 : a.p3 = b.p3
        · simp only [e3, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          by_cases e4 : a.p4 = b.p4
          · simp only [e4, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
            have e5 : a.p5 ≠ b.p5 := fun h5 => hne (by cases a; cases b; simp_all)
            have hv5 : a.p5.val ≠ b.p5.val := fun hv => e5 (Fin.ext hv)
            by_cases hlt : a.p5 < b.p5
            · exact Or.inl (decide_eq_true hlt)
            · exact Or.inr (decide_eq_true (by change b.p5.val < a.p5.val; have : ¬(a.p5.val < b.p5.val) := hlt; omega))
          · rw [bne_iff_ne.mpr e4, bne_iff_ne.mpr (Ne.symm e4)]; simp only [↓reduceIte]
            have hv : a.p4.val ≠ b.p4.val := fun hv => e4 (Fin.ext hv)
            by_cases hlt : a.p4 < b.p4
            · exact Or.inl (decide_eq_true hlt)
            · exact Or.inr (decide_eq_true (by change b.p4.val < a.p4.val; have : ¬(a.p4.val < b.p4.val) := hlt; omega))
        · rw [bne_iff_ne.mpr e3, bne_iff_ne.mpr (Ne.symm e3)]; simp only [↓reduceIte]
          have hv : a.p3.val ≠ b.p3.val := fun hv => e3 (Fin.ext hv)
          by_cases hlt : a.p3 < b.p3
          · exact Or.inl (decide_eq_true hlt)
          · exact Or.inr (decide_eq_true (by change b.p3.val < a.p3.val; have : ¬(a.p3.val < b.p3.val) := hlt; omega))
      · rw [bne_iff_ne.mpr e2, bne_iff_ne.mpr (Ne.symm e2)]; simp only [↓reduceIte]
        have hv : a.p2.val ≠ b.p2.val := fun hv => e2 (Fin.ext hv)
        by_cases hlt : a.p2 < b.p2
        · exact Or.inl (decide_eq_true hlt)
        · exact Or.inr (decide_eq_true (by change b.p2.val < a.p2.val; have : ¬(a.p2.val < b.p2.val) := hlt; omega))
    · rw [bne_iff_ne.mpr e1, bne_iff_ne.mpr (Ne.symm e1)]; simp only [↓reduceIte]
      have hv : a.p1.val ≠ b.p1.val := fun hv => e1 (Fin.ext hv)
      by_cases hlt : a.p1 < b.p1
      · exact Or.inl (decide_eq_true hlt)
      · exact Or.inr (decide_eq_true (by change b.p1.val < a.p1.val; have : ¬(a.p1.val < b.p1.val) := hlt; omega))
  · rw [bne_iff_ne.mpr e0, bne_iff_ne.mpr (Ne.symm e0)]; simp only [↓reduceIte]
    have hv : a.p0.val ≠ b.p0.val := fun hv => e0 (Fin.ext hv)
    by_cases hlt : a.p0 < b.p0
    · exact Or.inl (decide_eq_true hlt)
    · exact Or.inr (decide_eq_true (by change b.p0.val < a.p0.val; have : ¬(a.p0.val < b.p0.val) := hlt; omega))

private theorem permMin_comm (a b : Perm6) :
    (if permLt b a then b else a) = (if permLt a b then a else b) := by
  by_cases hab : a = b
  · subst hab; simp [permLt_irrefl]
  · rcases permLt_total hab with h1 | h2
    · rw [h1, permLt_asymm h1]; simp
    · rw [h2, permLt_asymm h2]; simp

/-- Full gate-order reversal `(p5, p4, p3, p2, p1, p0)`. -/
def revPerm (p : Perm6) : Perm6 :=
  ⟨p.p5, p.p4, p.p3, p.p2, p.p1, p.p0⟩

theorem revPerm_involutive (p : Perm6) : revPerm (revPerm p) = p := by
  cases p; rfl

/-- Canonical bare representative `min(p, revPerm p)` (360 classes of size 2). -/
def canonBarePerm (p : Perm6) : Perm6 :=
  let r := revPerm p
  if permLt r p then r else p

theorem canonBarePerm_revPerm (p : Perm6) : canonBarePerm (revPerm p) = canonBarePerm p := by
  unfold canonBarePerm
  rw [revPerm_involutive]
  exact permMin_comm (revPerm p) p

/-- Unordered wire pair `(min a b, max a b)`. -/
def sortedPair (a b : Fin 6) : Fin 6 × Fin 6 :=
  if b < a then (b, a) else (a, b)

theorem sortedPair_comm (a b : Fin 6) : sortedPair a b = sortedPair b a := by
  unfold sortedPair
  by_cases h1 : b < a <;> by_cases h2 : a < b
  · have h1' : b.val < a.val := h1; have h2' : a.val < b.val := h2; omega
  · simp [h1, h2]
  · simp [h1, h2]
  · have hab : a = b := Fin.ext (by
      have h1' : ¬(b.val < a.val) := h1
      have h2' : ¬(a.val < b.val) := h2
      omega)
    subst hab; simp

/-- The 90-class reversal-coupled canonical key:
    `min ((pair(p0,p1), p2, p3, pair(p4,p5)), (pair(p4,p5), p3, p2, pair(p0,p1)))`. -/
structure Coset90Key where
  endL0 : Fin 6
  endL1 : Fin 6
  midL  : Fin 6
  midR  : Fin 6
  endR0 : Fin 6
  endR1 : Fin 6
  deriving DecidableEq, Repr

/-- Compute the 90-class key of permutation `p`. -/
def coset90Key (p : Perm6) : Coset90Key :=
  let (a0, a1) := sortedPair p.p0 p.p1
  let (a4, a5) := sortedPair p.p4 p.p5
  let fwd : Perm6 := ⟨a0, a1, p.p2, p.p3, a4, a5⟩
  let bwd : Perm6 := ⟨a4, a5, p.p3, p.p2, a0, a1⟩
  let c := if permLt bwd fwd then bwd else fwd
  ⟨c.p0, c.p1, c.p2, c.p3, c.p4, c.p5⟩

/-- Canonical permutation representative of `coset90Key p`. -/
def canonAugPerm (p : Perm6) : Perm6 :=
  let k := coset90Key p
  ⟨k.endL0, k.endL1, k.midL, k.midR, k.endR0, k.endR1⟩

theorem coset90Key_eq_iff_canonAugPerm_eq (p q : Perm6) :
    coset90Key p = coset90Key q ↔ canonAugPerm p = canonAugPerm q := by
  constructor
  · intro h; unfold canonAugPerm; rw [h]
  · intro h
    unfold canonAugPerm at h
    cases hk1 : coset90Key p with | mk a0 a1 m1 m2 b0 b1 =>
    cases hk2 : coset90Key q with | mk c0 c1 n1 n2 d0 d1 =>
    rw [hk1, hk2] at h
    injection h with e0 e1 e2 e3 e4 e5
    subst e0 e1 e2 e3 e4 e5
    rfl

/-! ### Fast Inductive `Wire6` Counter (Single ~1.5s Pass for 720, 360, and 90!) -/

private inductive Wire6 | w0 | w1 | w2 | w3 | w4 | w5 deriving DecidableEq

private def ofFin6 (u : Fin 6) : Wire6 :=
  match u with
  | ⟨0, _⟩ => .w0 | ⟨1, _⟩ => .w1 | ⟨2, _⟩ => .w2
  | ⟨3, _⟩ => .w3 | ⟨4, _⟩ => .w4 | ⟨5, _⟩ => .w5

private def toFin6 : Wire6 → Fin 6
  | .w0 => 0 | .w1 => 1 | .w2 => 2 | .w3 => 3 | .w4 => 4 | .w5 => 5

private theorem toFin6_ofFin6 (u : Fin 6) : toFin6 (ofFin6 u) = u :=
  (beq_iff_eq ..).mp <| fin6_all_spec (f := fun u => toFin6 (ofFin6 u) == u) (by decide) u
private theorem ofFin6_toFin6 (w : Wire6) : ofFin6 (toFin6 w) = w := by cases w <;> rfl

private def eqW6 : Wire6 → Wire6 → Bool
  | .w0, .w0 | .w1, .w1 | .w2, .w2 | .w3, .w3 | .w4, .w4 | .w5, .w5 => true
  | _, _ => false

private theorem eqW6_iff (a b : Wire6) : eqW6 a b = true ↔ a = b := by
  cases a <;> cases b <;> decide

private theorem toFin6_beq_eq_eqW6 (a b : Wire6) : (toFin6 a == toFin6 b) = eqW6 a b := by
  cases a <;> cases b <;> rfl

private theorem eqW6_ofFin6 (x y : Fin 6) : eqW6 (ofFin6 x) (ofFin6 y) = (x == y) :=
  (beq_iff_eq ..).mp <| fin6_all2_spec
    (f := fun x y => eqW6 (ofFin6 x) (ofFin6 y) == (x == y)) (by decide) x y

private def w6Lt : Wire6 → Wire6 → Bool
  | .w0, .w0 => false | .w0, _ => true
  | .w1, .w0 | .w1, .w1 => false | .w1, _ => true
  | .w2, .w0 | .w2, .w1 | .w2, .w2 => false | .w2, _ => true
  | .w3, .w4 | .w3, .w5 => true | .w3, _ => false
  | .w4, .w5 => true | .w4, _ => false
  | .w5, _ => false

private theorem w6Lt_ofFin6 (x y : Fin 6) : w6Lt (ofFin6 x) (ofFin6 y) = decide (x < y) :=
  (beq_iff_eq ..).mp <| fin6_all2_spec
    (f := fun x y => w6Lt (ofFin6 x) (ofFin6 y) == decide (x < y)) (by decide) x y

private structure P6 where (p0 p1 p2 p3 p4 p5 : Wire6)

private def ofPerm6 (p : Perm6) : P6 :=
  ⟨ofFin6 p.p0, ofFin6 p.p1, ofFin6 p.p2, ofFin6 p.p3, ofFin6 p.p4, ofFin6 p.p5⟩

private def toPerm6 (q : P6) : Perm6 :=
  ⟨toFin6 q.p0, toFin6 q.p1, toFin6 q.p2, toFin6 q.p3, toFin6 q.p4, toFin6 q.p5⟩

private theorem toPerm6_ofPerm6 (p : Perm6) : toPerm6 (ofPerm6 p) = p := by
  cases p; simp [toPerm6, ofPerm6, toFin6_ofFin6]

private theorem ofPerm6_toPerm6 (q : P6) : ofPerm6 (toPerm6 q) = q := by
  cases q; simp [toPerm6, ofPerm6, ofFin6_toFin6]

private theorem ofPerm6_inj {p q : Perm6} (h : ofPerm6 p = ofPerm6 q) : p = q := by
  rw [← toPerm6_ofPerm6 p, ← toPerm6_ofPerm6 q, h]

private def eqP6 : P6 → P6 → Bool
  | ⟨a0, a1, a2, a3, a4, a5⟩, ⟨b0, b1, b2, b3, b4, b5⟩ =>
    eqW6 a0 b0 && eqW6 a1 b1 && eqW6 a2 b2 &&
    eqW6 a3 b3 && eqW6 a4 b4 && eqW6 a5 b5

private theorem eqP6_iff (a b : P6) : eqP6 a b = true ↔ a = b := by
  cases a; cases b
  simp only [eqP6, Bool.and_eq_true, eqW6_iff, P6.mk.injEq]
  exact ⟨fun ⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩ => ⟨e0, e1, e2, e3, e4, e5⟩,
         fun ⟨e0, e1, e2, e3, e4, e5⟩ => ⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩⟩

private def p6Lt : P6 → P6 → Bool
  | ⟨a0, a1, a2, a3, a4, a5⟩, ⟨b0, b1, b2, b3, b4, b5⟩ =>
    if !eqW6 a0 b0 then w6Lt a0 b0
    else if !eqW6 a1 b1 then w6Lt a1 b1
    else if !eqW6 a2 b2 then w6Lt a2 b2
    else if !eqW6 a3 b3 then w6Lt a3 b3
    else if !eqW6 a4 b4 then w6Lt a4 b4
    else w6Lt a5 b5

private theorem p6Lt_ofPerm6 (a b : Perm6) : p6Lt (ofPerm6 a) (ofPerm6 b) = permLt a b := by
  unfold p6Lt permLt ofPerm6
  simp only [eqW6_ofFin6, w6Lt_ofFin6, bne]

private def canonBareW (p : P6) : P6 :=
  let r : P6 := ⟨p.p5, p.p4, p.p3, p.p2, p.p1, p.p0⟩
  if p6Lt r p then r else p

private theorem canonBareW_ofPerm6 (p : Perm6) :
    canonBareW (ofPerm6 p) = ofPerm6 (canonBarePerm p) := by
  unfold canonBareW canonBarePerm revPerm
  dsimp only
  change (if p6Lt (ofPerm6 ⟨p.p5, p.p4, p.p3, p.p2, p.p1, p.p0⟩) (ofPerm6 p)
          then ofPerm6 ⟨p.p5, p.p4, p.p3, p.p2, p.p1, p.p0⟩ else ofPerm6 p) = _
  rw [p6Lt_ofPerm6]
  cases permLt ⟨p.p5, p.p4, p.p3, p.p2, p.p1, p.p0⟩ p <;> rfl

private def sortedPairW (a b : Wire6) : Wire6 × Wire6 :=
  if w6Lt b a then (b, a) else (a, b)

private theorem sortedPairW_ofFin6 (a b : Fin 6) :
    sortedPairW (ofFin6 a) (ofFin6 b) = (ofFin6 (sortedPair a b).1, ofFin6 (sortedPair a b).2) := by
  unfold sortedPairW sortedPair; rw [w6Lt_ofFin6]
  by_cases hba : b < a <;> simp [hba]

private def canonAugW (p : P6) : P6 :=
  let (a0, a1) := sortedPairW p.p0 p.p1
  let (a4, a5) := sortedPairW p.p4 p.p5
  let fwd : P6 := ⟨a0, a1, p.p2, p.p3, a4, a5⟩
  let bwd : P6 := ⟨a4, a5, p.p3, p.p2, a0, a1⟩
  if p6Lt bwd fwd then bwd else fwd

private theorem canonAugW_ofPerm6 (p : Perm6) :
    canonAugW (ofPerm6 p) = ofPerm6 (canonAugPerm p) := by
  unfold canonAugW canonAugPerm coset90Key
  dsimp only [ofPerm6]
  rw [sortedPairW_ofFin6 p.p0 p.p1, sortedPairW_ofFin6 p.p4 p.p5]
  let sp01 := sortedPair p.p0 p.p1
  let sp45 := sortedPair p.p4 p.p5
  let fwd6 : Perm6 := ⟨sp01.1, sp01.2, p.p2, p.p3, sp45.1, sp45.2⟩
  let bwd6 : Perm6 := ⟨sp45.1, sp45.2, p.p3, p.p2, sp01.1, sp01.2⟩
  change (if p6Lt (ofPerm6 bwd6) (ofPerm6 fwd6) then ofPerm6 bwd6 else ofPerm6 fwd6) = _
  rw [p6Lt_ofPerm6]
  cases permLt bwd6 fwd6 <;> rfl

private def w6List : List Wire6 := [.w0, .w1, .w2, .w3, .w4, .w5]

private def sumNatList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNatList xs

/-- Count permutations in $S_6$ satisfying `pred : Perm6 → Bool`. -/
def countPerms6 (pred : Perm6 → Bool) : Nat :=
  sumNatList <| ([0, 1, 2, 3, 4, 5] : List (Fin 6)).map fun p0 =>
  sumNatList <| ([0, 1, 2, 3, 4, 5] : List (Fin 6)).map fun p1 => if p1 == p0 then 0 else
  sumNatList <| ([0, 1, 2, 3, 4, 5] : List (Fin 6)).map fun p2 => if p2 == p0 || p2 == p1 then 0 else
  sumNatList <| ([0, 1, 2, 3, 4, 5] : List (Fin 6)).map fun p3 => if p3 == p0 || p3 == p1 || p3 == p2 then 0 else
  sumNatList <| ([0, 1, 2, 3, 4, 5] : List (Fin 6)).map fun p4 => if p4 == p0 || p4 == p1 || p4 == p2 || p4 == p3 then 0 else
  sumNatList <| ([0, 1, 2, 3, 4, 5] : List (Fin 6)).map fun p5 =>
    if p5 == p0 || p5 == p1 || p5 == p2 || p5 == p3 || p5 == p4 then 0
    else if pred ⟨p0, p1, p2, p3, p4, p5⟩ then 1 else 0

private def countW6 (pred : P6 → Bool) : Nat :=
  sumNatList <| w6List.map fun p0 =>
  sumNatList <| w6List.map fun p1 => if eqW6 p1 p0 then 0 else
  sumNatList <| w6List.map fun p2 => if eqW6 p2 p0 || eqW6 p2 p1 then 0 else
  sumNatList <| w6List.map fun p3 => if eqW6 p3 p0 || eqW6 p3 p1 || eqW6 p3 p2 then 0 else
  sumNatList <| w6List.map fun p4 => if eqW6 p4 p0 || eqW6 p4 p1 || eqW6 p4 p2 || eqW6 p4 p3 then 0 else
  sumNatList <| w6List.map fun p5 =>
    if eqW6 p5 p0 || eqW6 p5 p1 || eqW6 p5 p2 || eqW6 p5 p3 || eqW6 p5 p4 then 0
    else if pred ⟨p0, p1, p2, p3, p4, p5⟩ then 1 else 0

private theorem map_fin6_eq_w6 {α : Type} (g : Fin 6 → α) :
    ([0, 1, 2, 3, 4, 5] : List (Fin 6)).map g = w6List.map (fun w => g (toFin6 w)) := rfl

private theorem countPerms6_eq_countW6 (pred : Perm6 → Bool) :
    countPerms6 pred = countW6 (fun q => pred (toPerm6 q)) := by
  unfold countPerms6 countW6 toPerm6
  simp only [map_fin6_eq_w6, toFin6_beq_eq_eqW6]

private theorem countW6_congr {f g : P6 → Bool} (h : ∀ q, f q = g q) :
    countW6 f = countW6 g := by
  have heq : f = g := funext h
  rw [heq]

private structure TripleCount where (tot bare aug : Nat) deriving DecidableEq

private def sumTriple : List TripleCount → TripleCount
  | [] => ⟨0, 0, 0⟩
  | x :: xs =>
    match sumTriple xs with
    | ⟨rt, rb, ra⟩ => ⟨x.tot + rt, x.bare + rb, x.aug + ra⟩

/-- Single-pass O(720) counter computing `(720, 360, 90)` simultaneously! -/
private def statsW6 : TripleCount :=
  sumTriple <| w6List.map fun p0 =>
  sumTriple <| (w6List.filter (!eqW6 · p0)).map fun p1 =>
  sumTriple <| (w6List.filter (fun x => !eqW6 x p0 && !eqW6 x p1)).map fun p2 =>
  sumTriple <| (w6List.filter (fun x => !eqW6 x p0 && !eqW6 x p1 && !eqW6 x p2)).map fun p3 =>
  sumTriple <| (w6List.filter (fun x => !eqW6 x p0 && !eqW6 x p1 && !eqW6 x p2 && !eqW6 x p3)).map fun p4 =>
  sumTriple <| (w6List.filter (fun x => !eqW6 x p0 && !eqW6 x p1 && !eqW6 x p2 && !eqW6 x p3 && !eqW6 x p4)).map fun p5 =>
    let q : P6 := ⟨p0, p1, p2, p3, p4, p5⟩
    ⟨1, if eqP6 (canonBareW q) q then 1 else 0, if eqP6 (canonAugW q) q then 1 else 0⟩

private theorem statsW6_eq : statsW6 = ⟨720, 360, 90⟩ := by decide

private theorem sumNat_filter_eq (l : List Wire6) (cond : Wire6 → Bool) (f : Wire6 → Nat) :
    sumNatList ((l.filter cond).map f) =
    sumNatList (l.map fun x => if cond x then f x else 0) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter, List.map]
    cases cond x <;> simp [sumNatList, ih]

private theorem sumTriple_tot {α : Type} (l : List α) (g : α → TripleCount) :
    (sumTriple (l.map g)).tot = sumNatList (l.map fun x => (g x).tot) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map, sumTriple, sumNatList]
    rw [← ih]

private theorem sumTriple_bare {α : Type} (l : List α) (g : α → TripleCount) :
    (sumTriple (l.map g)).bare = sumNatList (l.map fun x => (g x).bare) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map, sumTriple, sumNatList]
    rw [← ih]

private theorem sumTriple_aug {α : Type} (l : List α) (g : α → TripleCount) :
    (sumTriple (l.map g)).aug = sumNatList (l.map fun x => (g x).aug) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map, sumTriple, sumNatList]
    rw [← ih]

private theorem cond_neg_iff (a : Bool) (t : Nat) :
    (if !a then t else 0) = (if a then 0 else t) := by
  cases a <;> rfl

private theorem statsW6_components :
    statsW6.tot = countW6 (fun _ => true) ∧
    statsW6.bare = countW6 (fun q => eqP6 (canonBareW q) q) ∧
    statsW6.aug = countW6 (fun q => eqP6 (canonAugW q) q) := by
  have hnot2 : ∀ a b : Bool, (!a && !b) = !(a || b) := by intro a b; cases a <;> cases b <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold statsW6 countW6
    simp only [sumTriple_tot, sumNat_filter_eq, hnot2, cond_neg_iff]
    rfl
  · unfold statsW6 countW6
    simp only [sumTriple_bare, sumNat_filter_eq, hnot2, cond_neg_iff]
  · unfold statsW6 countW6
    simp only [sumTriple_aug, sumNat_filter_eq, hnot2, cond_neg_iff]

/-- Exactly $6! = 720$ valid permutations exist in $S_6$. -/
theorem total_perms6_eq_720 : countPerms6 (fun _ => true) = 720 := by
  rw [countPerms6_eq_countW6, ← statsW6_components.1, statsW6_eq]

/-- **Main Theorem 1 (`bare_hook_classes_eq_360`)**:
    Across all 720 permutations of `Fin 6`, the bare suffix hook sets
    `{ h_s(p) mod 0b111111 | 0 ≤ s ≤ 5 }` partition $S_6$ into **360** canonical classes. -/
theorem bare_hook_classes_eq_360 :
    countPerms6 (fun p => canonBarePerm p == p) = 360 := by
  rw [countPerms6_eq_countW6]
  have hcongr : countW6 (fun q => canonBarePerm (toPerm6 q) == toPerm6 q) =
                countW6 (fun q => eqP6 (canonBareW q) q) := by
    apply countW6_congr; intro q; apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, eqP6_iff]
    exact ⟨fun h => by have h' := congrArg ofPerm6 h; rw [← canonBareW_ofPerm6, ofPerm6_toPerm6] at h'; exact h',
           fun h => ofPerm6_inj (by rw [← canonBareW_ofPerm6, ofPerm6_toPerm6]; exact h)⟩
  rw [hcongr, ← statsW6_components.2.1, statsW6_eq]

/-- **Main Theorem 2 (`augmented_hook_classes_eq_90`)**:
    Adjoining single-qubit data faults `{ e_u mod 0b111111 | u ∈ Fin 6 }` collapses
    the 720 permutations of $S_6$ to **90** canonical equivalence classes. -/
theorem augmented_hook_classes_eq_90 :
    countPerms6 (fun p => canonAugPerm p == p) = 90 := by
  rw [countPerms6_eq_countW6]
  have hcongr : countW6 (fun q => canonAugPerm (toPerm6 q) == toPerm6 q) =
                countW6 (fun q => eqP6 (canonAugW q) q) := by
    apply countW6_congr; intro q; apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, eqP6_iff]
    exact ⟨fun h => by have h' := congrArg ofPerm6 h; rw [← canonAugW_ofPerm6, ofPerm6_toPerm6] at h'; exact h',
           fun h => ofPerm6_inj (by rw [← canonAugW_ofPerm6, ofPerm6_toPerm6]; exact h)⟩
  rw [hcongr, ← statsW6_components.2.2, statsW6_eq]

/-! ### Algebraic Proof of `coset90_key_sound_and_complete` & `bare_hook_eq_iff` -/

private structure Mask6 where (b0 b1 b2 b3 b4 b5 : Bool) deriving DecidableEq

private def ofBitVec6 (v : BitVec 6) : Mask6 :=
  ⟨v.getLsbD 0, v.getLsbD 1, v.getLsbD 2, v.getLsbD 3, v.getLsbD 4, v.getLsbD 5⟩

private theorem bool_beq_iff (a b : Bool) : Bool.beq a b = true ↔ a = b := by
  cases a <;> cases b <;> decide

private def eqMask6 : Mask6 → Mask6 → Bool
  | ⟨a0, a1, a2, a3, a4, a5⟩, ⟨b0, b1, b2, b3, b4, b5⟩ =>
    Bool.beq a0 b0 && Bool.beq a1 b1 && Bool.beq a2 b2 &&
    Bool.beq a3 b3 && Bool.beq a4 b4 && Bool.beq a5 b5

private theorem eqMask6_iff (x y : Mask6) : eqMask6 x y = true ↔ x = y := by
  cases x; cases y
  simp only [eqMask6, Bool.and_eq_true, bool_beq_iff, Mask6.mk.injEq]
  exact ⟨fun ⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩ => ⟨e0, e1, e2, e3, e4, e5⟩,
         fun ⟨e0, e1, e2, e3, e4, e5⟩ => ⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩⟩

private theorem ofBitVec6_inj {u v : BitVec 6} (h : ofBitVec6 u = ofBitVec6 v) : u = v := by
  unfold ofBitVec6 at h
  injection h with e0 e1 e2 e3 e4 e5
  exact bitvec6_eq_of_bits e5 e4 e3 e2 e1 e0

private def wireMask6 : Wire6 → Mask6
  | .w0 => ⟨true,  false, false, false, false, false⟩
  | .w1 => ⟨false, true,  false, false, false, false⟩
  | .w2 => ⟨false, false, true,  false, false, false⟩
  | .w3 => ⟨false, false, false, true,  false, false⟩
  | .w4 => ⟨false, false, false, false, true,  false⟩
  | .w5 => ⟨false, false, false, false, false, true⟩

private def orMask6 : Mask6 → Mask6 → Mask6
  | ⟨a0, a1, a2, a3, a4, a5⟩, ⟨b0, b1, b2, b3, b4, b5⟩ =>
    ⟨a0 || b0, a1 || b1, a2 || b2, a3 || b3, a4 || b4, a5 || b5⟩

private def xorMask6 : Mask6 → Mask6 → Mask6
  | ⟨a0, a1, a2, a3, a4, a5⟩, ⟨b0, b1, b2, b3, b4, b5⟩ =>
    ⟨xor a0 b0, xor a1 b1, xor a2 b2, xor a3 b3, xor a4 b4, xor a5 b5⟩

private def negMask6 : Mask6 → Mask6
  | ⟨a0, a1, a2, a3, a4, a5⟩ => ⟨!a0, !a1, !a2, !a3, !a4, !a5⟩

private theorem ofBitVec6_wireBit (u : Fin 6) : ofBitVec6 (wireBit u) = wireMask6 (ofFin6 u) := by
  match u with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ =>
    unfold wireBit ofFin6 wireMask6 ofBitVec6; simp

private theorem ofBitVec6_or (u v : BitVec 6) :
    ofBitVec6 (u ||| v) = orMask6 (ofBitVec6 u) (ofBitVec6 v) := by
  unfold ofBitVec6 orMask6; simp

private theorem ofBitVec6_xor (u v : BitVec 6) :
    ofBitVec6 (u ^^^ v) = xorMask6 (ofBitVec6 u) (ofBitVec6 v) := by
  unfold ofBitVec6 xorMask6; simp

private theorem ofBitVec6_neg (u : BitVec 6) :
    ofBitVec6 (u ^^^ allOnes6) = negMask6 (ofBitVec6 u) := by
  unfold ofBitVec6 negMask6 allOnes6; simp

private def allP6 (pred : P6 → Bool) : Bool :=
  w6List.all fun p0 =>
  (w6List.filter (fun x => !eqW6 x p0)).all fun p1 =>
  (w6List.filter (fun x => !eqW6 x p0 && !eqW6 x p1)).all fun p2 =>
  (w6List.filter (fun x => !eqW6 x p0 && !eqW6 x p1 && !eqW6 x p2)).all fun p3 =>
  (w6List.filter (fun x => !eqW6 x p0 && !eqW6 x p1 && !eqW6 x p2 && !eqW6 x p3)).all fun p4 =>
  (w6List.filter (fun x => !eqW6 x p0 && !eqW6 x p1 && !eqW6 x p2 && !eqW6 x p3 && !eqW6 x p4)).all fun p5 =>
    pred ⟨p0, p1, p2, p3, p4, p5⟩

private theorem mem_w6List (x : Wire6) : x ∈ w6List := by
  cases x <;> simp [w6List]

private def IsP6 : P6 → Bool
  | ⟨p0, p1, p2, p3, p4, p5⟩ =>
    !eqW6 p1 p0 &&
    (!eqW6 p2 p0 && !eqW6 p2 p1) &&
    (!eqW6 p3 p0 && !eqW6 p3 p1 && !eqW6 p3 p2) &&
    (!eqW6 p4 p0 && !eqW6 p4 p1 && !eqW6 p4 p2 && !eqW6 p4 p3) &&
    (!eqW6 p5 p0 && !eqW6 p5 p1 && !eqW6 p5 p2 && !eqW6 p5 p3 && !eqW6 p5 p4)

private theorem isP6_ofPerm6 (p : Perm6) : IsP6 (ofPerm6 p) = IsPerm6 p := by
  unfold IsP6 IsPerm6 ofPerm6; simp only [eqW6_ofFin6, bne]

private theorem allP6_spec {pred : P6 → Bool} (hall : allP6 pred = true)
    (p : P6) (hp : IsP6 p = true) : pred p = true := by
  cases p with | mk p0 p1 p2 p3 p4 p5 =>
  unfold IsP6 at hp
  have ⟨hp14, hc5⟩ := (Bool.and_eq_true _ _).mp hp
  have ⟨hp13, hc4⟩ := (Bool.and_eq_true _ _).mp hp14
  have ⟨hp12, hc3⟩ := (Bool.and_eq_true _ _).mp hp13
  have ⟨hc1,  hc2⟩ := (Bool.and_eq_true _ _).mp hp12
  have h0 := List.all_eq_true.mp hall p0 (mem_w6List p0)
  have h1 := List.all_eq_true.mp h0 p1 (List.mem_filter.mpr ⟨mem_w6List p1, hc1⟩)
  have h2 := List.all_eq_true.mp h1 p2 (List.mem_filter.mpr ⟨mem_w6List p2, hc2⟩)
  have h3 := List.all_eq_true.mp h2 p3 (List.mem_filter.mpr ⟨mem_w6List p3, hc3⟩)
  have h4 := List.all_eq_true.mp h3 p4 (List.mem_filter.mpr ⟨mem_w6List p4, hc4⟩)
  exact List.all_eq_true.mp h4 p5 (List.mem_filter.mpr ⟨mem_w6List p5, hc5⟩)

private def augIdemOnly : P6 → Bool
  | ⟨a0, a1, a2, a3, a4, a5⟩ =>
    let q : P6 := ⟨a0, a1, a2, a3, a4, a5⟩
    eqP6 (canonAugW q) q

private theorem augIdemOnly_eq (ca : P6) :
    augIdemOnly ca = eqP6 (canonAugW ca) ca := by
  cases ca; rfl

/-- Lightweight 6-bit suffix & canonicalizer-idempotence check. -/
private theorem perm_suffix_props_w6 :
    allP6 (fun p =>
      let m0 := wireMask6 p.p0; let m1 := wireMask6 p.p1; let m2 := wireMask6 p.p2
      let m3 := wireMask6 p.p3; let m4 := wireMask6 p.p4; let m5 := wireMask6 p.p5
      let h4 := orMask6 m5 m4
      let h3 := orMask6 h4 m3
      let h2 := orMask6 h3 m2
      let h1 := orMask6 h2 m1
      let h0 := orMask6 h1 m0
      let ones : Mask6 := ⟨true, true, true, true, true, true⟩
      eqMask6 h0 ones &&
      eqMask6 h1 (negMask6 m0) &&
      eqMask6 h2 (negMask6 (orMask6 m0 m1)) &&
      eqMask6 h3 (negMask6 (orMask6 (orMask6 m0 m1) m2)) &&
      eqMask6 (xorMask6 (xorMask6 (xorMask6 (xorMask6 (xorMask6 m0 m1) m2) m3) m4) m5) ones &&
      augIdemOnly (canonAugW p)) = true := by decide

private structure PermDistinct (p : Perm6) : Prop where
  ne01 : p.p0 ≠ p.p1
  ne02 : p.p0 ≠ p.p2
  ne03 : p.p0 ≠ p.p3
  ne04 : p.p0 ≠ p.p4
  ne05 : p.p0 ≠ p.p5
  ne12 : p.p1 ≠ p.p2
  ne13 : p.p1 ≠ p.p3
  ne14 : p.p1 ≠ p.p4
  ne15 : p.p1 ≠ p.p5
  ne23 : p.p2 ≠ p.p3
  ne24 : p.p2 ≠ p.p4
  ne25 : p.p2 ≠ p.p5
  ne34 : p.p3 ≠ p.p4
  ne35 : p.p3 ≠ p.p5
  ne45 : p.p4 ≠ p.p5

private theorem isPerm6_distinct {p : Perm6} (hp : IsPerm6 p = true) : PermDistinct p := by
  unfold IsPerm6 at hp
  simp only [Bool.and_eq_true, bne_iff_ne] at hp
  exact {
    ne01 := Ne.symm hp.1.1.1.1
    ne02 := Ne.symm hp.1.1.1.2.1
    ne03 := Ne.symm hp.1.1.2.1.1
    ne04 := Ne.symm hp.1.2.1.1.1
    ne05 := Ne.symm hp.2.1.1.1.1
    ne12 := Ne.symm hp.1.1.1.2.2
    ne13 := Ne.symm hp.1.1.2.1.2
    ne14 := Ne.symm hp.1.2.1.1.2
    ne15 := Ne.symm hp.2.1.1.1.2
    ne23 := Ne.symm hp.1.1.2.2
    ne24 := Ne.symm hp.1.2.1.2
    ne25 := Ne.symm hp.2.1.1.2
    ne34 := Ne.symm hp.1.2.2
    ne35 := Ne.symm hp.2.1.2
    ne45 := Ne.symm hp.2.2
  }

private theorem distinct_isPerm6 {p : Perm6} (d : PermDistinct p) : IsPerm6 p = true := by
  unfold IsPerm6
  simp only [Bool.and_eq_true, bne_iff_ne]
  exact ⟨⟨⟨⟨d.ne01.symm, ⟨d.ne02.symm, d.ne12.symm⟩⟩,
            ⟨⟨d.ne03.symm, d.ne13.symm⟩, d.ne23.symm⟩⟩,
           ⟨⟨⟨d.ne04.symm, d.ne14.symm⟩, d.ne24.symm⟩, d.ne34.symm⟩⟩,
          ⟨⟨⟨⟨d.ne05.symm, d.ne15.symm⟩, d.ne25.symm⟩, d.ne35.symm⟩, d.ne45.symm⟩⟩

private def swap01 (p : Perm6) : Perm6 := ⟨p.p1, p.p0, p.p2, p.p3, p.p4, p.p5⟩
private def swap45 (p : Perm6) : Perm6 := ⟨p.p0, p.p1, p.p2, p.p3, p.p5, p.p4⟩

private theorem isPerm6_revPerm {p : Perm6} (hp : IsPerm6 p = true) : IsPerm6 (revPerm p) = true := by
  have d := isPerm6_distinct hp
  exact distinct_isPerm6 {
    ne01 := d.ne45.symm, ne02 := d.ne35.symm, ne03 := d.ne25.symm, ne04 := d.ne15.symm, ne05 := d.ne05.symm,
    ne12 := d.ne34.symm, ne13 := d.ne24.symm, ne14 := d.ne14.symm, ne15 := d.ne04.symm,
    ne23 := d.ne23.symm, ne24 := d.ne13.symm, ne25 := d.ne03.symm,
    ne34 := d.ne12.symm, ne35 := d.ne02.symm,
    ne45 := d.ne01.symm
  }

private theorem isPerm6_swap01 {p : Perm6} (hp : IsPerm6 p = true) : IsPerm6 (swap01 p) = true := by
  have d := isPerm6_distinct hp
  exact distinct_isPerm6 {
    ne01 := d.ne01.symm, ne02 := d.ne12, ne03 := d.ne13, ne04 := d.ne14, ne05 := d.ne15,
    ne12 := d.ne02, ne13 := d.ne03, ne14 := d.ne04, ne15 := d.ne05,
    ne23 := d.ne23, ne24 := d.ne24, ne25 := d.ne25,
    ne34 := d.ne34, ne35 := d.ne35,
    ne45 := d.ne45
  }

private theorem isPerm6_swap45 {p : Perm6} (hp : IsPerm6 p = true) : IsPerm6 (swap45 p) = true := by
  have d := isPerm6_distinct hp
  exact distinct_isPerm6 {
    ne01 := d.ne01, ne02 := d.ne02, ne03 := d.ne03, ne04 := d.ne05, ne05 := d.ne04,
    ne12 := d.ne12, ne13 := d.ne13, ne14 := d.ne15, ne15 := d.ne14,
    ne23 := d.ne23, ne24 := d.ne25, ne25 := d.ne24,
    ne34 := d.ne35, ne35 := d.ne34,
    ne45 := d.ne45.symm
  }

private theorem suffix_cosets_of_isPerm6 {p : Perm6} (hp : IsPerm6 p = true) :
    suffixHook p 0 = allOnes6 ∧
    suffixHook p 1 = wireBit p.p0 ^^^ allOnes6 ∧
    suffixHook p 2 = (wireBit p.p0 ||| wireBit p.p1) ^^^ allOnes6 ∧
    suffixHook p 3 = (wireBit p.p0 ||| wireBit p.p1 ||| wireBit p.p2) ^^^ allOnes6 ∧
    suffixHook p 4 = (wireBit p.p4 ||| wireBit p.p5) ∧
    suffixHook p 5 = wireBit p.p5 ∧
    (wireBit p.p0 ^^^ wireBit p.p1 ^^^ wireBit p.p2 ^^^
     wireBit p.p3 ^^^ wireBit p.p4 ^^^ wireBit p.p5) = allOnes6 := by
  have hp' : IsP6 (ofPerm6 p) = true := by rw [isP6_ofPerm6]; exact hp
  have hm := allP6_spec perm_suffix_props_w6 (ofPerm6 p) hp'
  simp only [Bool.and_eq_true, eqMask6_iff] at hm
  have e0 := hm.1.1.1.1.1
  have e1 := hm.1.1.1.1.2
  have e2 := hm.1.1.1.2
  have e3 := hm.1.1.2
  have ex := hm.1.2
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · apply ofBitVec6_inj; unfold suffixHook; simp only [ofBitVec6_or, ofBitVec6_wireBit]; exact e0
  · apply ofBitVec6_inj; unfold suffixHook; simp only [ofBitVec6_or, ofBitVec6_neg, ofBitVec6_wireBit]; exact e1
  · apply ofBitVec6_inj; unfold suffixHook; simp only [ofBitVec6_or, ofBitVec6_neg, ofBitVec6_wireBit]; exact e2
  · apply ofBitVec6_inj; unfold suffixHook; simp only [ofBitVec6_or, ofBitVec6_neg, ofBitVec6_wireBit]; exact e3
  · unfold suffixHook; exact BitVec.or_comm _ _
  · apply ofBitVec6_inj; simp only [ofBitVec6_xor, ofBitVec6_wireBit]; exact ex

private theorem isPerm6_canonAugPerm {p : Perm6} (hp : IsPerm6 p = true) :
    IsPerm6 (canonAugPerm p) = true := by
  let p₁ := if p.p1 < p.p0 then swap01 p else p
  have hp₁ : IsPerm6 p₁ = true := by
    dsimp only [p₁]; by_cases h : p.p1 < p.p0 <;> simp [h, hp, isPerm6_swap01]
  let p₂ := if p₁.p5 < p₁.p4 then swap45 p₁ else p₁
  have hp₂ : IsPerm6 p₂ = true := by
    dsimp only [p₂]; by_cases h : p₁.p5 < p₁.p4 <;> simp [h, hp₁, isPerm6_swap45]
  let bwd := swap01 (swap45 (revPerm p₂))
  have hbwd : IsPerm6 bwd = true := isPerm6_swap01 (isPerm6_swap45 (isPerm6_revPerm hp₂))
  have hf : p₂ = ⟨(sortedPair p.p0 p.p1).1, (sortedPair p.p0 p.p1).2, p.p2, p.p3,
                  (sortedPair p.p4 p.p5).1, (sortedPair p.p4 p.p5).2⟩ := by
    dsimp only [p₂, p₁, swap01, swap45, sortedPair]
    by_cases h01 : p.p1 < p.p0 <;> simp only [h01, ↓reduceIte] <;>
    by_cases h45 : p.p5 < p.p4 <;> simp only [h45, ↓reduceIte]
  have hb : bwd = ⟨(sortedPair p.p4 p.p5).1, (sortedPair p.p4 p.p5).2, p.p3, p.p2,
                   (sortedPair p.p0 p.p1).1, (sortedPair p.p0 p.p1).2⟩ := by
    dsimp only [bwd]; rw [hf]; rfl
  have hce : canonAugPerm p = (if permLt bwd p₂ then bwd else p₂) := by
    unfold canonAugPerm coset90Key; dsimp only; rw [← hf, ← hb]
  rw [hce]
  by_cases hr : permLt bwd p₂ = true <;> simp [hr, hbwd, hp₂]

/-- Every canonical representative in both the 360-class bare partition and
    the 90-class augmented partition is itself a valid permutation in $S_6$ and idempotent. -/
theorem canon_representatives_valid_and_idempotent (p : Perm6) (hp : IsPerm6 p = true) :
    IsPerm6 (canonBarePerm p) = true ∧
    canonBarePerm (canonBarePerm p) = canonBarePerm p ∧
    IsPerm6 (canonAugPerm p) = true ∧
    canonAugPerm (canonAugPerm p) = canonAugPerm p := by
  have hp' : IsP6 (ofPerm6 p) = true := by rw [isP6_ofPerm6]; exact hp
  have hm := allP6_spec perm_suffix_props_w6 (ofPerm6 p) hp'
  rw [augIdemOnly_eq] at hm
  simp only [Bool.and_eq_true] at hm
  refine ⟨?_, ?_, isPerm6_canonAugPerm hp, ?_⟩
  · unfold canonBarePerm
    by_cases hlt : permLt (revPerm p) p = true <;> simp [hlt, hp, isPerm6_revPerm]
  · unfold canonBarePerm
    by_cases hlt : permLt (revPerm p) p = true
    · simp only [hlt, ↓reduceIte]
      rw [revPerm_involutive, permLt_asymm hlt]; rfl
    · have hfl : permLt (revPerm p) p = false := Bool.eq_false_iff.mpr hlt
      simp only [hfl, Bool.false_eq_true, ↓reduceIte]
  · apply ofPerm6_inj
    rw [← canonAugW_ofPerm6, ← canonAugW_ofPerm6]
    exact (eqP6_iff _ _).mp hm.2

private theorem canonCoset_zero : canonCoset 0#6 = 0#6 := by
  unfold canonCoset; simp

private theorem canonCoset_allOnes : canonCoset allOnes6 = 0#6 := by
  have h := canonCoset_xor_allOnes 0#6
  rw [BitVec.zero_xor] at h
  rw [h, canonCoset_zero]

private theorem bool_or6_rev (a b c d e f : Bool) :
    (a || f || e || d || c || b) = (a || b || c || d || e || f) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

private theorem mem_bareHookSet_explicit {p : Perm6} (hp : IsPerm6 p = true) (v : BitVec 6) :
    memCosetSet (bareHookSet p) v =
    (decide (canonCoset v = 0#6) ||
     decide (canonCoset v = canonCoset (wireBit p.p0)) ||
     decide (canonCoset v = canonCoset (wireBit p.p0 ||| wireBit p.p1)) ||
     decide (canonCoset v = canonCoset (wireBit p.p0 ||| wireBit p.p1 ||| wireBit p.p2)) ||
     decide (canonCoset v = canonCoset (wireBit p.p4 ||| wireBit p.p5)) ||
     decide (canonCoset v = canonCoset (wireBit p.p5))) := by
  obtain ⟨s0, s1, s2, s3, s4, s5, _⟩ := suffix_cosets_of_isPerm6 hp
  unfold bareHookSet
  simp only [mem_insertCoset, mem_emptyCosetSet, Bool.false_or]
  rw [s0, s1, s2, s3, s4, s5, canonCoset_allOnes,
      canonCoset_xor_allOnes, canonCoset_xor_allOnes, canonCoset_xor_allOnes]

theorem bareHookSet_revPerm {p : Perm6} (hp : IsPerm6 p = true) :
    bareHookSet (revPerm p) = bareHookSet p := by
  have hrev := isPerm6_revPerm hp
  obtain ⟨_, _, _, s3p, _, _, _⟩ := suffix_cosets_of_isPerm6 hp
  apply CosetSet.ext
  intro v
  rw [mem_bareHookSet_explicit hrev v, mem_bareHookSet_explicit hp v]
  unfold revPerm
  dsimp only
  have hp3 : canonCoset (wireBit p.p5 ||| wireBit p.p4 ||| wireBit p.p3) =
             canonCoset (wireBit p.p0 ||| wireBit p.p1 ||| wireBit p.p2) := by
    have h3eq : (wireBit p.p5 ||| wireBit p.p4 ||| wireBit p.p3) = suffixHook p 3 := rfl
    rw [h3eq, s3p, canonCoset_xor_allOnes]
  have hp45 : (wireBit p.p5 ||| wireBit p.p4) = (wireBit p.p4 ||| wireBit p.p5) := BitVec.or_comm _ _
  have hp01 : (wireBit p.p1 ||| wireBit p.p0) = (wireBit p.p0 ||| wireBit p.p1) := BitVec.or_comm _ _
  rw [hp3, hp45, hp01]
  exact bool_or6_rev _ _ _ _ _ _

theorem bareHookSet_canonBarePerm {p : Perm6} (hp : IsPerm6 p = true) :
    bareHookSet (canonBarePerm p) = bareHookSet p := by
  unfold canonBarePerm
  by_cases h : permLt (revPerm p) p = true
  · simp only [h, ↓reduceIte]; exact bareHookSet_revPerm hp
  · simp [h]

private theorem mem_singleDataSet_of_eq_wire (v : BitVec 6) (u : Fin 6)
    (h : decide (canonCoset v = canonCoset (wireBit u)) = true) :
    memCosetSet singleDataSet v = true := by
  have heq : canonCoset v = canonCoset (wireBit u) := of_decide_eq_true h
  have hm := mem_singleDataSet_wireBit u
  unfold memCosetSet at hm ⊢
  rw [heq]; exact hm

private theorem aug_swap01 {p : Perm6} (hp : IsPerm6 p = true) :
    augmentedHookSet (swap01 p) = augmentedHookSet p := by
  have hs := isPerm6_swap01 hp
  apply CosetSet.ext; intro v
  unfold augmentedHookSet
  rw [mem_unionCosetSet, mem_unionCosetSet,
      mem_bareHookSet_explicit hs v, mem_bareHookSet_explicit hp v]
  unfold swap01; dsimp only
  rw [BitVec.or_comm (wireBit p.p1) (wireBit p.p0)]
  by_cases hm : memCosetSet singleDataSet v = true
  · simp [hm]
  · have h0 : decide (canonCoset v = canonCoset (wireBit p.p0)) = false := by
      cases h : decide (canonCoset v = canonCoset (wireBit p.p0))
      · rfl
      · exact absurd (mem_singleDataSet_of_eq_wire v p.p0 h) hm
    have h1 : decide (canonCoset v = canonCoset (wireBit p.p1)) = false := by
      cases h : decide (canonCoset v = canonCoset (wireBit p.p1))
      · rfl
      · exact absurd (mem_singleDataSet_of_eq_wire v p.p1 h) hm
    rw [h0, h1]

private theorem aug_swap45 {p : Perm6} (hp : IsPerm6 p = true) :
    augmentedHookSet (swap45 p) = augmentedHookSet p := by
  have hs := isPerm6_swap45 hp
  apply CosetSet.ext; intro v
  unfold augmentedHookSet
  rw [mem_unionCosetSet, mem_unionCosetSet,
      mem_bareHookSet_explicit hs v, mem_bareHookSet_explicit hp v]
  unfold swap45; dsimp only
  rw [BitVec.or_comm (wireBit p.p5) (wireBit p.p4)]
  by_cases hm : memCosetSet singleDataSet v = true
  · simp [hm]
  · have h4 : decide (canonCoset v = canonCoset (wireBit p.p4)) = false := by
      cases h : decide (canonCoset v = canonCoset (wireBit p.p4))
      · rfl
      · exact absurd (mem_singleDataSet_of_eq_wire v p.p4 h) hm
    have h5 : decide (canonCoset v = canonCoset (wireBit p.p5)) = false := by
      cases h : decide (canonCoset v = canonCoset (wireBit p.p5))
      · rfl
      · exact absurd (mem_singleDataSet_of_eq_wire v p.p5 h) hm
    rw [h4, h5]

private theorem aug_revPerm {p : Perm6} (hp : IsPerm6 p = true) :
    augmentedHookSet (revPerm p) = augmentedHookSet p := by
  unfold augmentedHookSet; rw [bareHookSet_revPerm hp]

theorem augmentedHookSet_canonAugPerm {p : Perm6} (hp : IsPerm6 p = true) :
    augmentedHookSet (canonAugPerm p) = augmentedHookSet p := by
  have h1 : IsPerm6 (if p.p1 < p.p0 then swap01 p else p) = true ∧
            augmentedHookSet (if p.p1 < p.p0 then swap01 p else p) = augmentedHookSet p := by
    by_cases h01 : p.p1 < p.p0
    · simp only [h01, ↓reduceIte]; exact ⟨isPerm6_swap01 hp, aug_swap01 hp⟩
    · simp only [h01, ↓reduceIte, hp, true_and]
  let p₁ := if p.p1 < p.p0 then swap01 p else p
  have hp₁ : IsPerm6 p₁ = true := h1.1
  have ha₁ : augmentedHookSet p₁ = augmentedHookSet p := h1.2
  have h2 : IsPerm6 (if p₁.p5 < p₁.p4 then swap45 p₁ else p₁) = true ∧
            augmentedHookSet (if p₁.p5 < p₁.p4 then swap45 p₁ else p₁) = augmentedHookSet p := by
    by_cases h45 : p₁.p5 < p₁.p4
    · simp only [h45, ↓reduceIte]; exact ⟨isPerm6_swap45 hp₁, (aug_swap45 hp₁).trans ha₁⟩
    · simp only [h45, ↓reduceIte, hp₁, ha₁, and_self]
  let p₂ := if p₁.p5 < p₁.p4 then swap45 p₁ else p₁
  have hp₂ : IsPerm6 p₂ = true := h2.1
  have ha₂ : augmentedHookSet p₂ = augmentedHookSet p := h2.2
  let bwd := swap01 (swap45 (revPerm p₂))
  have hbwd_aug : augmentedHookSet bwd = augmentedHookSet p := by
    dsimp only [bwd]
    rw [aug_swap01 (isPerm6_swap45 (isPerm6_revPerm hp₂)),
        aug_swap45 (isPerm6_revPerm hp₂),
        aug_revPerm hp₂, ha₂]
  have hcanon_eq : canonAugPerm p = (if permLt bwd p₂ then bwd else p₂) := by
    have hf : p₂ = ⟨(sortedPair p.p0 p.p1).1, (sortedPair p.p0 p.p1).2, p.p2, p.p3,
                    (sortedPair p.p4 p.p5).1, (sortedPair p.p4 p.p5).2⟩ := by
      dsimp only [p₂, p₁, swap01, swap45, sortedPair]
      by_cases h01 : p.p1 < p.p0 <;> simp only [h01, ↓reduceIte] <;>
      by_cases h45 : p.p5 < p.p4 <;> simp only [h45, ↓reduceIte]
    have hb : bwd = ⟨(sortedPair p.p4 p.p5).1, (sortedPair p.p4 p.p5).2, p.p3, p.p2,
                     (sortedPair p.p0 p.p1).1, (sortedPair p.p0 p.p1).2⟩ := by
      dsimp only [bwd]; rw [hf]; rfl
    unfold canonAugPerm coset90Key
    dsimp only
    rw [← hf, ← hb]
  rw [hcanon_eq]
  by_cases hr : permLt bwd p₂ = true
  · simp only [hr, ↓reduceIte]; exact hbwd_aug
  · simp only [hr, Bool.false_eq_true, ↓reduceIte]; exact ha₂

/-! ### Fast Bit-Level Lemmas for Completeness (Zero Multi-Thousand-Case `decide`s!) -/

private def popcount6 (v : BitVec 6) : Nat :=
  (if v.getLsbD 0 then 1 else 0) + (if v.getLsbD 1 then 1 else 0) +
  (if v.getLsbD 2 then 1 else 0) + (if v.getLsbD 3 then 1 else 0) +
  (if v.getLsbD 4 then 1 else 0) + (if v.getLsbD 5 then 1 else 0)

private def cosetHamming (v : BitVec 6) : Nat :=
  let w := popcount6 v
  if w ≤ 6 - w then w else 6 - w

private def popMask6 (m : Mask6) : Nat :=
  (if m.b0 then 1 else 0) + (if m.b1 then 1 else 0) +
  (if m.b2 then 1 else 0) + (if m.b3 then 1 else 0) +
  (if m.b4 then 1 else 0) + (if m.b5 then 1 else 0)

private theorem popcount6_eq_popMask6 (v : BitVec 6) : popcount6 v = popMask6 (ofBitVec6 v) := rfl

private theorem popMask6_neg_and_le6 (m : Mask6) :
    popMask6 (negMask6 m) = 6 - popMask6 m ∧ popMask6 m ≤ 6 := by
  have h : (bList.all fun b0 => bList.all fun b1 => bList.all fun b2 =>
            bList.all fun b3 => bList.all fun b4 => bList.all fun b5 =>
              let x : Mask6 := ⟨b0, b1, b2, b3, b4, b5⟩
              (popMask6 (negMask6 x) == 6 - popMask6 x) && decide (popMask6 x ≤ 6)) = true := by
    decide
  cases m with | mk b0 b1 b2 b3 b4 b5 =>
  have hb := b_all_spec (b_all_spec (b_all_spec (b_all_spec (b_all_spec (b_all_spec h b0) b1) b2) b3) b4) b5
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
  exact hb

private theorem popcount6_xor_allOnes (v : BitVec 6) :
    popcount6 (v ^^^ allOnes6) = 6 - popcount6 v := by
  rw [popcount6_eq_popMask6, popcount6_eq_popMask6, ofBitVec6_neg]
  exact (popMask6_neg_and_le6 (ofBitVec6 v)).1

private theorem popcount6_le_6 (v : BitVec 6) : popcount6 v ≤ 6 :=
  (popMask6_neg_and_le6 (ofBitVec6 v)).2

private theorem cosetHamming_xor_allOnes (v : BitVec 6) :
    cosetHamming (v ^^^ allOnes6) = cosetHamming v := by
  unfold cosetHamming
  rw [popcount6_xor_allOnes]
  have hle := popcount6_le_6 v
  by_cases h1 : 6 - popcount6 v ≤ 6 - (6 - popcount6 v) <;>
  by_cases h2 : popcount6 v ≤ 6 - popcount6 v <;>
  simp only [h1, h2, ↓reduceIte] <;> omega

private theorem cosetHamming_congr {u v : BitVec 6} (h : canonCoset u = canonCoset v) :
    cosetHamming u = cosetHamming v := by
  rcases (canonCoset_eq_iff u v).mp h with rfl | rfl
  · rfl
  · exact cosetHamming_xor_allOnes v

private theorem cosetHamming_zero : cosetHamming 0#6 = 0 := by
  unfold cosetHamming popcount6; simp

private theorem w6_all_spec {f : Wire6 → Bool} (h : w6List.all f = true) (a : Wire6) :
    f a = true := List.all_eq_true.mp h a (mem_w6List a)

private theorem w6_all2_spec {f : Wire6 → Wire6 → Bool}
    (h : (w6List.all fun a => w6List.all fun b => f a b) = true) (a b : Wire6) :
    f a b = true := w6_all_spec (w6_all_spec h a) b

private theorem w6_all3_spec {f : Wire6 → Wire6 → Wire6 → Bool}
    (h : (w6List.all fun a => w6List.all fun b => w6List.all fun c => f a b c) = true)
    (a b c : Wire6) : f a b c = true := w6_all_spec (w6_all2_spec h a b) c

private theorem popcount6_wire (u : Fin 6) : popcount6 (wireBit u) = 1 := by
  rw [popcount6_eq_popMask6, ofBitVec6_wireBit]
  cases ofFin6 u <;> rfl

private theorem cosetHamming_wire (u : Fin 6) : cosetHamming (wireBit u) = 1 := by
  unfold cosetHamming; rw [popcount6_wire]; rfl

private theorem pair_popcount2 {u0 u1 : Fin 6} (h : u0 ≠ u1) :
    popcount6 (wireBit u0 ||| wireBit u1) = 2 := by
  rw [popcount6_eq_popMask6, ofBitVec6_or, ofBitVec6_wireBit, ofBitVec6_wireBit]
  have hp := w6_all2_spec
    (f := fun a b => eqW6 a b || (popMask6 (orMask6 (wireMask6 a) (wireMask6 b)) == 2))
    (by decide) (ofFin6 u0) (ofFin6 u1)
  rw [eqW6_ofFin6, beq_eq_false_iff_ne.mpr h, Bool.false_or] at hp
  exact (beq_iff_eq ..).mp hp

private theorem cosetHamming_pair {u v : Fin 6} (h : u ≠ v) :
    cosetHamming (wireBit u ||| wireBit v) = 2 := by
  unfold cosetHamming; rw [pair_popcount2 h]; rfl

private theorem cosetHamming_triple {u v w : Fin 6} (h1 : u ≠ v) (h2 : u ≠ w) (h3 : v ≠ w) :
    cosetHamming (wireBit u ||| wireBit v ||| wireBit w) = 3 := by
  have hpop : popcount6 (wireBit u ||| wireBit v ||| wireBit w) = 3 := by
    rw [popcount6_eq_popMask6, ofBitVec6_or, ofBitVec6_or,
        ofBitVec6_wireBit, ofBitVec6_wireBit, ofBitVec6_wireBit]
    have hp := w6_all3_spec
      (f := fun a b c => eqW6 a b || (eqW6 a c || (eqW6 b c ||
        (popMask6 (orMask6 (orMask6 (wireMask6 a) (wireMask6 b)) (wireMask6 c)) == 3))))
      (by decide) (ofFin6 u) (ofFin6 v) (ofFin6 w)
    rw [eqW6_ofFin6, eqW6_ofFin6, eqW6_ofFin6,
        beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2, beq_eq_false_iff_ne.mpr h3,
        Bool.false_or, Bool.false_or, Bool.false_or] at hp
    exact (beq_iff_eq ..).mp hp
  unfold cosetHamming; rw [hpop]; rfl

private theorem mem_singleDataSet_cosetHamming {v : BitVec 6}
    (hm : memCosetSet singleDataSet v = true) : cosetHamming v = 1 := by
  unfold singleDataSet at hm
  simp only [mem_insertCoset, mem_emptyCosetSet, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at hm
  rcases hm with ((((h0 | h1) | h2) | h3) | h4) | h5
  · exact (cosetHamming_congr h0).trans (cosetHamming_wire 0)
  · exact (cosetHamming_congr h1).trans (cosetHamming_wire 1)
  · exact (cosetHamming_congr h2).trans (cosetHamming_wire 2)
  · exact (cosetHamming_congr h3).trans (cosetHamming_wire 3)
  · exact (cosetHamming_congr h4).trans (cosetHamming_wire 4)
  · exact (cosetHamming_congr h5).trans (cosetHamming_wire 5)

private theorem wireBit_inj {x y : Fin 6} (h : wireBit x = wireBit y) : x = y := by
  have hm : wireMask6 (ofFin6 x) = wireMask6 (ofFin6 y) := by
    rw [← ofBitVec6_wireBit, ← ofBitVec6_wireBit, h]
  have hw : ofFin6 x = ofFin6 y := by
    revert hm; cases ofFin6 x <;> cases ofFin6 y <;> intro hm <;> cases hm <;> rfl
  rw [← toFin6_ofFin6 x, ← toFin6_ofFin6 y, hw]

private theorem single_coset_inj {u v : Fin 6}
    (h : canonCoset (wireBit u) = canonCoset (wireBit v)) : u = v := by
  rcases (canonCoset_eq_iff _ _).mp h with heq | hcomp
  · exact wireBit_inj heq
  · have hp := congrArg popcount6 hcomp
    rw [popcount6_xor_allOnes, popcount6_wire, popcount6_wire] at hp
    omega

private theorem wireBit_getLsbD (u k : Fin 6) :
    (wireBit u).getLsbD k.val = decide (u = k) := by
  match u, k with
  | ⟨0, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨1, _⟩ | ⟨0, _⟩, ⟨2, _⟩ | ⟨0, _⟩, ⟨3, _⟩ | ⟨0, _⟩, ⟨4, _⟩ | ⟨0, _⟩, ⟨5, _⟩
  | ⟨1, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨2, _⟩ | ⟨1, _⟩, ⟨3, _⟩ | ⟨1, _⟩, ⟨4, _⟩ | ⟨1, _⟩, ⟨5, _⟩
  | ⟨2, _⟩, ⟨0, _⟩ | ⟨2, _⟩, ⟨1, _⟩ | ⟨2, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨3, _⟩ | ⟨2, _⟩, ⟨4, _⟩ | ⟨2, _⟩, ⟨5, _⟩
  | ⟨3, _⟩, ⟨0, _⟩ | ⟨3, _⟩, ⟨1, _⟩ | ⟨3, _⟩, ⟨2, _⟩ | ⟨3, _⟩, ⟨3, _⟩ | ⟨3, _⟩, ⟨4, _⟩ | ⟨3, _⟩, ⟨5, _⟩
  | ⟨4, _⟩, ⟨0, _⟩ | ⟨4, _⟩, ⟨1, _⟩ | ⟨4, _⟩, ⟨2, _⟩ | ⟨4, _⟩, ⟨3, _⟩ | ⟨4, _⟩, ⟨4, _⟩ | ⟨4, _⟩, ⟨5, _⟩
  | ⟨5, _⟩, ⟨0, _⟩ | ⟨5, _⟩, ⟨1, _⟩ | ⟨5, _⟩, ⟨2, _⟩ | ⟨5, _⟩, ⟨3, _⟩ | ⟨5, _⟩, ⟨4, _⟩ | ⟨5, _⟩, ⟨5, _⟩ =>
    unfold wireBit; simp

private theorem pair_xor_eq_or {u0 u1 : Fin 6} (h : u0 ≠ u1) :
    (wireBit u0 ^^^ wireBit u1) = (wireBit u0 ||| wireBit u1) := by
  apply ofBitVec6_inj
  rw [ofBitVec6_xor, ofBitVec6_or, ofBitVec6_wireBit, ofBitVec6_wireBit]
  have hp := w6_all2_spec
    (f := fun a b => eqW6 a b ||
      eqMask6 (xorMask6 (wireMask6 a) (wireMask6 b)) (orMask6 (wireMask6 a) (wireMask6 b)))
    (by decide) (ofFin6 u0) (ofFin6 u1)
  rw [eqW6_ofFin6, beq_eq_false_iff_ne.mpr h, Bool.false_or] at hp
  exact (eqMask6_iff _ _).mp hp

private theorem disjoint_pair_wire {u0 u1 x : Fin 6} (h0 : x ≠ u0) (h1 : x ≠ u1) :
    ((wireBit u0 ||| wireBit u1) &&& wireBit x) = 0#6 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let k : Fin 6 := ⟨i, hi⟩
  change (((wireBit u0 ||| wireBit u1) &&& wireBit x).getLsbD k.val) = (0#6 : BitVec 6).getLsbD k.val
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero, wireBit_getLsbD]
  by_cases hxk : x = k
  · subst hxk
    rw [decide_eq_false h0.symm, decide_eq_false h1.symm]
    rfl
  · rw [decide_eq_false hxk, Bool.and_false]

private theorem sortedPair_mem_inj {a b c d : Fin 6}
    (hpair : sortedPair a b = sortedPair c d) (hac : a = c) : b = d := by
  subst hac
  unfold sortedPair at hpair
  by_cases h1 : b < a <;> by_cases h2 : d < a <;>
    simp only [h1, h2, ↓reduceIte, Prod.mk.injEq] at hpair
  · exact hpair.1
  · exact hpair.1.trans hpair.2
  · exact hpair.2.trans hpair.1
  · exact hpair.2

private theorem sortedPair_disjoint_ne {u0 u1 v0 v1 : Fin 6}
    (hne : u0 ≠ v0 ∧ u0 ≠ v1) : sortedPair u0 u1 ≠ sortedPair v0 v1 := by
  intro heq
  unfold sortedPair at heq
  by_cases h1 : u1 < u0 <;> by_cases h2 : v1 < v0 <;>
    simp only [h1, h2, ↓reduceIte, Prod.mk.injEq] at heq
  · exact hne.1 heq.2
  · exact hne.2 heq.2
  · exact hne.2 heq.1
  · exact hne.1 heq.1

private theorem pair_or_eq_of_sortedPair_eq {u0 u1 v0 v1 : Fin 6}
    (h : sortedPair u0 u1 = sortedPair v0 v1) :
    (wireBit u0 ||| wireBit u1) = (wireBit v0 ||| wireBit v1) := by
  unfold sortedPair at h
  by_cases h1 : u1 < u0 <;> by_cases h2 : v1 < v0 <;>
    simp only [h1, h2, ↓reduceIte, Prod.mk.injEq] at h <;>
    rcases h with ⟨rfl, rfl⟩
  · rfl
  · exact BitVec.or_comm _ _
  · exact BitVec.or_comm _ _
  · rfl

private theorem pair_coset_eq_sortedPair {u0 u1 v0 v1 : Fin 6}
    (hu : u0 ≠ u1) (hv : v0 ≠ v1)
    (h : canonCoset (wireBit u0 ||| wireBit u1) = canonCoset (wireBit v0 ||| wireBit v1)) :
    sortedPair u0 u1 = sortedPair v0 v1 := by
  rcases (canonCoset_eq_iff _ _).mp h with heq | hcomp
  · have hb0 : ((wireBit u0 ||| wireBit u1).getLsbD u0.val) =
               ((wireBit v0 ||| wireBit v1).getLsbD u0.val) := by rw [heq]
    simp only [BitVec.getLsbD_or, wireBit_getLsbD, decide_true, Bool.true_or] at hb0
    have hb1 : ((wireBit u0 ||| wireBit u1).getLsbD u1.val) =
               ((wireBit v0 ||| wireBit v1).getLsbD u1.val) := by rw [heq]
    simp only [BitVec.getLsbD_or, wireBit_getLsbD, decide_true, Bool.or_true] at hb1
    rcases (Bool.or_eq_true _ _).mp hb0.symm with hv0 | hv1
    · have e0 : v0 = u0 := of_decide_eq_true hv0
      subst e0
      rw [decide_eq_false hu, Bool.false_or] at hb1
      have e1 : v1 = u1 := of_decide_eq_true hb1.symm
      subst e1; rfl
    · have e0 : v1 = u0 := of_decide_eq_true hv1
      subst e0
      rw [decide_eq_false hu, Bool.or_false] at hb1
      have e1 : v0 = u1 := of_decide_eq_true hb1.symm
      subst e1; exact sortedPair_comm _ _
  · have hpL := pair_popcount2 hu
    have hpR := pair_popcount2 hv
    have hc := congrArg popcount6 hcomp
    rw [popcount6_xor_allOnes, hpL, hpR] at hc
    omega

private theorem and_wireBit_zero_getLsbD (m : BitVec 6) (x : Fin 6)
    (h : (m &&& wireBit x) = 0#6) : m.getLsbD x.val = false := by
  have hx : (m &&& wireBit x).getLsbD x.val = (0#6 : BitVec 6).getLsbD x.val := by rw [h]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, wireBit_getLsbD, decide_true, Bool.and_true] at hx
  exact hx

private theorem exists_bit_of_popcount2 (m : BitVec 6) (hp : popcount6 m = 2) :
    ∃ u : Fin 6, m.getLsbD u.val = true := by
  cases b0 : m.getLsbD 0
  · cases b1 : m.getLsbD 1
    · cases b2 : m.getLsbD 2
      · cases b3 : m.getLsbD 3
        · cases b4 : m.getLsbD 4
          · cases b5 : m.getLsbD 5
            · unfold popcount6 at hp
              rw [b0, b1, b2, b3, b4, b5] at hp
              contradiction
            · exact ⟨⟨5, by omega⟩, b5⟩
          · exact ⟨⟨4, by omega⟩, b4⟩
        · exact ⟨⟨3, by omega⟩, b3⟩
      · exact ⟨⟨2, by omega⟩, b2⟩
    · exact ⟨⟨1, by omega⟩, b1⟩
  · exact ⟨⟨0, by omega⟩, b0⟩

private theorem allOnes6_getLsbD (u : Fin 6) : allOnes6.getLsbD u.val = true := by
  match u with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ => unfold allOnes6; simp

private theorem triple_ext_inj {mPair : BitVec 6} {x y : Fin 6}
    (hp2 : popcount6 mPair = 2)
    (hx : (mPair &&& wireBit x) = 0#6)
    (hy : (mPair &&& wireBit y) = 0#6)
    (heq : canonCoset (mPair ||| wireBit x) = canonCoset (mPair ||| wireBit y)) :
    x = y := by
  let _ := hy
  rcases (canonCoset_eq_iff _ _).mp heq with hdir | hcomp
  · have hbx : ((mPair ||| wireBit x).getLsbD x.val) =
               ((mPair ||| wireBit y).getLsbD x.val) := by rw [hdir]
    simp only [BitVec.getLsbD_or, wireBit_getLsbD, and_wireBit_zero_getLsbD mPair x hx,
               decide_true, Bool.false_or] at hbx
    exact (of_decide_eq_true hbx.symm).symm
  · obtain ⟨u, hu⟩ := exists_bit_of_popcount2 mPair hp2
    have hbu : ((mPair ||| wireBit x).getLsbD u.val) =
               (((mPair ||| wireBit y) ^^^ allOnes6).getLsbD u.val) := by rw [hcomp]
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, hu, allOnes6_getLsbD, Bool.true_or] at hbu
    cases hbu

private theorem weight2_mem_aug {q : Perm6} (hq : IsPerm6 q = true) {v : BitVec 6}
    (hw2 : cosetHamming v = 2) (hmem : memCosetSet (augmentedHookSet q) v = true) :
    canonCoset v = canonCoset (wireBit q.p0 ||| wireBit q.p1) ∨
    canonCoset v = canonCoset (wireBit q.p4 ||| wireBit q.p5) := by
  have dq := isPerm6_distinct hq
  unfold augmentedHookSet at hmem
  rw [mem_unionCosetSet, mem_bareHookSet_explicit hq v] at hmem
  by_cases hs : memCosetSet singleDataSet v = true
  · have := mem_singleDataSet_cosetHamming hs; omega
  · simp only [hs, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq] at hmem
    rcases hmem with ((((h0 | h1) | h2) | h3) | h4) | h5
    · have hcz : canonCoset 0#6 = 0#6 := by decide
      have := (cosetHamming_congr (h0.trans hcz.symm)).trans cosetHamming_zero; omega
    · have := (cosetHamming_congr h1).trans (cosetHamming_wire q.p0); omega
    · exact Or.inl h2
    · have := (cosetHamming_congr h3).trans (cosetHamming_triple dq.ne01 dq.ne02 dq.ne12); omega
    · exact Or.inr h4
    · have := (cosetHamming_congr h5).trans (cosetHamming_wire q.p5); omega

private theorem weight3_mem_aug {q : Perm6} (hq : IsPerm6 q = true) {v : BitVec 6}
    (hw3 : cosetHamming v = 3) (hmem : memCosetSet (augmentedHookSet q) v = true) :
    canonCoset v = canonCoset (wireBit q.p0 ||| wireBit q.p1 ||| wireBit q.p2) := by
  have dq := isPerm6_distinct hq
  unfold augmentedHookSet at hmem
  rw [mem_unionCosetSet, mem_bareHookSet_explicit hq v] at hmem
  by_cases hs : memCosetSet singleDataSet v = true
  · have := mem_singleDataSet_cosetHamming hs; omega
  · simp only [hs, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq] at hmem
    rcases hmem with ((((h0 | h1) | h2) | h3) | h4) | h5
    · have hcz : canonCoset 0#6 = 0#6 := by decide
      have := (cosetHamming_congr (h0.trans hcz.symm)).trans cosetHamming_zero; omega
    · have := (cosetHamming_congr h1).trans (cosetHamming_wire q.p0); omega
    · have := (cosetHamming_congr h2).trans (cosetHamming_pair dq.ne01); omega
    · exact h3
    · have := (cosetHamming_congr h4).trans (cosetHamming_pair dq.ne45); omega
    · have := (cosetHamming_congr h5).trans (cosetHamming_wire q.p5); omega

private theorem weight1_mem_bare {q : Perm6} (hq : IsPerm6 q = true) {u : Fin 6}
    (hmem : memCosetSet (bareHookSet q) (wireBit u) = true) :
    u = q.p0 ∨ u = q.p5 := by
  have dq := isPerm6_distinct hq
  have hw1 : cosetHamming (wireBit u) = 1 := cosetHamming_wire u
  rw [mem_bareHookSet_explicit hq (wireBit u)] at hmem
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hmem
  rcases hmem with ((((h0 | h1) | h2) | h3) | h4) | h5
  · have hcz : canonCoset 0#6 = 0#6 := by decide
    have := (cosetHamming_congr (h0.trans hcz.symm)).trans cosetHamming_zero; omega
  · exact Or.inl (single_coset_inj h1)
  · have := (cosetHamming_congr h2).trans (cosetHamming_pair dq.ne01); omega
  · have := (cosetHamming_congr h3).trans (cosetHamming_triple dq.ne01 dq.ne02 dq.ne12); omega
  · have := (cosetHamming_congr h4).trans (cosetHamming_pair dq.ne45); omega
  · exact Or.inr (single_coset_inj h5)

private theorem bool_xor6_eq_d (a b c d e f : Bool) :
    d = xor (xor (xor (xor (xor (xor (xor (xor a b) c) d) e) f) (xor a b)) c) (xor e f) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

private theorem bool_xor6_eq_c (a b c d e f : Bool) :
    c = xor (xor (xor (xor (xor (xor (xor (xor a b) c) d) e) f) (xor e f)) d) (xor a b) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

private theorem xor6_solve_d {a b c d e f : BitVec 6}
    (h : a ^^^ b ^^^ c ^^^ d ^^^ e ^^^ f = allOnes6) :
    d = allOnes6 ^^^ (a ^^^ b) ^^^ c ^^^ (e ^^^ f) := by
  rw [← h]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  exact bool_xor6_eq_d _ _ _ _ _ _

private theorem xor6_solve_c {a b c d e f : BitVec 6}
    (h : a ^^^ b ^^^ c ^^^ d ^^^ e ^^^ f = allOnes6) :
    c = allOnes6 ^^^ (e ^^^ f) ^^^ d ^^^ (a ^^^ b) := by
  rw [← h]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  exact bool_xor6_eq_c _ _ _ _ _ _

/-- **Main Theorem 3 (`coset90_key_sound_and_complete`)**:
    Two valid permutations of `Fin 6` induce the exact same augmented fault set
    **if and only if** they have the same reversal-coupled `coset90Key`! -/
theorem coset90_key_sound_and_complete (p q : Perm6)
    (hp : IsPerm6 p = true) (hq : IsPerm6 q = true) :
    augmentedHookSet p = augmentedHookSet q ↔ coset90Key p = coset90Key q := by
  constructor
  · intro heq
    have dp := isPerm6_distinct hp
    have dq := isPerm6_distinct hq
    obtain ⟨_, _, _, _, _, _, xorp⟩ := suffix_cosets_of_isPerm6 hp
    obtain ⟨_, _, _, s3q, _, _, xorq⟩ := suffix_cosets_of_isPerm6 hq
    have hm01 : memCosetSet (augmentedHookSet q) (wireBit p.p0 ||| wireBit p.p1) = true := by
      rw [← heq]; unfold augmentedHookSet
      rw [mem_unionCosetSet, mem_bareHookSet_explicit hp]; simp
    have hm45 : memCosetSet (augmentedHookSet q) (wireBit p.p4 ||| wireBit p.p5) = true := by
      rw [← heq]; unfold augmentedHookSet
      rw [mem_unionCosetSet, mem_bareHookSet_explicit hp]; simp
    have hm012 : memCosetSet (augmentedHookSet q) (wireBit p.p0 ||| wireBit p.p1 ||| wireBit p.p2) = true := by
      rw [← heq]; unfold augmentedHookSet
      rw [mem_unionCosetSet, mem_bareHookSet_explicit hp]; simp
    have hsp_ne : sortedPair p.p0 p.p1 ≠ sortedPair p.p4 p.p5 :=
      sortedPair_disjoint_ne ⟨dp.ne04, dp.ne05⟩
    have hc01 := weight2_mem_aug hq (cosetHamming_pair dp.ne01) hm01
    have hc45 := weight2_mem_aug hq (cosetHamming_pair dp.ne45) hm45
    have hc012 := weight3_mem_aug hq (cosetHamming_triple dp.ne01 dp.ne02 dp.ne12) hm012
    rcases hc01 with h01_fwd | h01_rev
    · have e_endL := pair_coset_eq_sortedPair dp.ne01 dq.ne01 h01_fwd
      have e_endR : sortedPair p.p4 p.p5 = sortedPair q.p4 q.p5 := by
        rcases hc45 with h45_bad | h45_ok
        · exact absurd (e_endL.trans (pair_coset_eq_sortedPair dp.ne45 dq.ne01 h45_bad).symm) hsp_ne
        · exact pair_coset_eq_sortedPair dp.ne45 dq.ne45 h45_ok
      have m_eqL := pair_or_eq_of_sortedPair_eq e_endL
      have m_eqR := pair_or_eq_of_sortedPair_eq e_endR
      rw [m_eqL] at hc012
      have ep2 : p.p2 = q.p2 := triple_ext_inj (pair_popcount2 dq.ne01)
        (by rw [← m_eqL]; exact disjoint_pair_wire dp.ne02.symm dp.ne12.symm)
        (disjoint_pair_wire dq.ne02.symm dq.ne12.symm) hc012
      have ep3 : p.p3 = q.p3 := by
        apply wireBit_inj
        have hp3 := xor6_solve_d xorp
        have hq3 := xor6_solve_d xorq
        rw [pair_xor_eq_or dp.ne01, pair_xor_eq_or dp.ne45] at hp3
        rw [pair_xor_eq_or dq.ne01, pair_xor_eq_or dq.ne45] at hq3
        rw [hp3, hq3, m_eqL, m_eqR, ep2]
      unfold coset90Key
      rw [e_endL, e_endR, ep2, ep3]
    · have e_endL := pair_coset_eq_sortedPair dp.ne01 dq.ne45 h01_rev
      have e_endR : sortedPair p.p4 p.p5 = sortedPair q.p0 q.p1 := by
        rcases hc45 with h45_ok | h45_bad
        · exact pair_coset_eq_sortedPair dp.ne45 dq.ne01 h45_ok
        · exact absurd (e_endL.trans (pair_coset_eq_sortedPair dp.ne45 dq.ne45 h45_bad).symm) hsp_ne
      have m_eqL := pair_or_eq_of_sortedPair_eq e_endL
      have m_eqR := pair_or_eq_of_sortedPair_eq e_endR
      have hq3_coset : canonCoset (wireBit q.p0 ||| wireBit q.p1 ||| wireBit q.p2) =
                       canonCoset ((wireBit q.p4 ||| wireBit q.p5) ||| wireBit q.p3) := by
        have h3eq : suffixHook q 3 = ((wireBit q.p4 ||| wireBit q.p5) ||| wireBit q.p3) := by
          change (wireBit q.p5 ||| wireBit q.p4) ||| wireBit q.p3 = _
          rw [BitVec.or_comm (wireBit q.p5) (wireBit q.p4)]
        rw [← h3eq, s3q, canonCoset_xor_allOnes]
      rw [hq3_coset, m_eqL] at hc012
      have ep2 : p.p2 = q.p3 := triple_ext_inj (pair_popcount2 dq.ne45)
        (by rw [← m_eqL]; exact disjoint_pair_wire dp.ne02.symm dp.ne12.symm)
        (disjoint_pair_wire dq.ne34 dq.ne35) hc012
      have ep3 : p.p3 = q.p2 := by
        apply wireBit_inj
        have hp3 := xor6_solve_d xorp
        have hq2 := xor6_solve_c xorq
        rw [pair_xor_eq_or dp.ne01, pair_xor_eq_or dp.ne45] at hp3
        rw [pair_xor_eq_or dq.ne01, pair_xor_eq_or dq.ne45] at hq2
        rw [hp3, hq2, m_eqL, m_eqR, ep2]
      unfold coset90Key
      rw [e_endL, e_endR, ep2, ep3]
      let sp01 := sortedPair q.p0 q.p1
      let sp45 := sortedPair q.p4 q.p5
      let fwdQ : Perm6 := ⟨sp01.1, sp01.2, q.p2, q.p3, sp45.1, sp45.2⟩
      let bwdQ : Perm6 := ⟨sp45.1, sp45.2, q.p3, q.p2, sp01.1, sp01.2⟩
      have hcomm := permMin_comm bwdQ fwdQ
      dsimp only [sp01, sp45, fwdQ, bwdQ] at hcomm ⊢
      rw [hcomm]
  · intro hkey
    rw [coset90Key_eq_iff_canonAugPerm_eq] at hkey
    rw [← augmentedHookSet_canonAugPerm hp, ← augmentedHookSet_canonAugPerm hq, hkey]

/-- Two valid permutations have identical bare suffix hook sets iff they share the same
    canonical bare representative (`p = q ∨ p = revPerm q`). -/
theorem bare_hook_eq_iff_canonBarePerm_eq (p q : Perm6)
    (hp : IsPerm6 p = true) (hq : IsPerm6 q = true) :
    bareHookSet p = bareHookSet q ↔ canonBarePerm p = canonBarePerm q := by
  constructor
  · intro hbare
    have haug : augmentedHookSet p = augmentedHookSet q := by
      unfold augmentedHookSet; rw [hbare]
    have dp := isPerm6_distinct hp
    have dq := isPerm6_distinct hq
    have hp0_mem : memCosetSet (bareHookSet q) (wireBit p.p0) = true := by
      rw [← hbare, mem_bareHookSet_explicit hp]; simp
    have hp0_end := weight1_mem_bare hq hp0_mem
    have hp5_mem : memCosetSet (bareHookSet q) (wireBit p.p5) = true := by
      rw [← hbare, mem_bareHookSet_explicit hp]; simp
    have hp5_end := weight1_mem_bare hq hp5_mem
    have hm01 : memCosetSet (augmentedHookSet q) (wireBit p.p0 ||| wireBit p.p1) = true := by
      rw [← haug]; unfold augmentedHookSet
      rw [mem_unionCosetSet, mem_bareHookSet_explicit hp]; simp
    have hm45 : memCosetSet (augmentedHookSet q) (wireBit p.p4 ||| wireBit p.p5) = true := by
      rw [← haug]; unfold augmentedHookSet
      rw [mem_unionCosetSet, mem_bareHookSet_explicit hp]; simp
    have hm012 : memCosetSet (augmentedHookSet q) (wireBit p.p0 ||| wireBit p.p1 ||| wireBit p.p2) = true := by
      rw [← haug]; unfold augmentedHookSet
      rw [mem_unionCosetSet, mem_bareHookSet_explicit hp]; simp
    obtain ⟨_, _, _, _, _, _, xorp⟩ := suffix_cosets_of_isPerm6 hp
    obtain ⟨_, _, _, s3q, _, _, xorq⟩ := suffix_cosets_of_isPerm6 hq
    have hc01 := weight2_mem_aug hq (cosetHamming_pair dp.ne01) hm01
    have hc45 := weight2_mem_aug hq (cosetHamming_pair dp.ne45) hm45
    have hc012 := weight3_mem_aug hq (cosetHamming_triple dp.ne01 dp.ne02 dp.ne12) hm012
    have hsp_ne : sortedPair p.p0 p.p1 ≠ sortedPair p.p4 p.p5 :=
      sortedPair_disjoint_ne ⟨dp.ne04, dp.ne05⟩
    rcases hc01 with h01_fwd | h01_rev
    · have e_endL := pair_coset_eq_sortedPair dp.ne01 dq.ne01 h01_fwd
      have e_endR : sortedPair p.p4 p.p5 = sortedPair q.p4 q.p5 := by
        rcases hc45 with h45_bad | h45_ok
        · exact absurd (e_endL.trans (pair_coset_eq_sortedPair dp.ne45 dq.ne01 h45_bad).symm) hsp_ne
        · exact pair_coset_eq_sortedPair dp.ne45 dq.ne45 h45_ok
      have ep0 : p.p0 = q.p0 := by
        rcases hp0_end with h0 | h5
        · exact h0
        · rw [h5] at e_endL
          exact absurd e_endL (sortedPair_disjoint_ne ⟨dq.ne05.symm, dq.ne15.symm⟩)
      have ep1 : p.p1 = q.p1 := sortedPair_mem_inj e_endL ep0
      have ep5 : p.p5 = q.p5 := by
        rcases hp5_end with h0 | h5
        · exact absurd (ep0.trans h0.symm) dp.ne05
        · exact h5
      have ep4 : p.p4 = q.p4 := sortedPair_mem_inj
        ((sortedPair_comm p.p5 p.p4).trans (e_endR.trans (sortedPair_comm q.p4 q.p5))) ep5
      have m_eqL := pair_or_eq_of_sortedPair_eq e_endL
      have m_eqR := pair_or_eq_of_sortedPair_eq e_endR
      rw [m_eqL] at hc012
      have ep2 : p.p2 = q.p2 := triple_ext_inj (pair_popcount2 dq.ne01)
        (by rw [← m_eqL]; exact disjoint_pair_wire dp.ne02.symm dp.ne12.symm)
        (disjoint_pair_wire dq.ne02.symm dq.ne12.symm) hc012
      have ep3 : p.p3 = q.p3 := by
        apply wireBit_inj
        have hp3 := xor6_solve_d xorp; have hq3 := xor6_solve_d xorq
        rw [pair_xor_eq_or dp.ne01, pair_xor_eq_or dp.ne45] at hp3
        rw [pair_xor_eq_or dq.ne01, pair_xor_eq_or dq.ne45] at hq3
        rw [hp3, hq3, m_eqL, m_eqR, ep2]
      have hpq : p = q := by cases p; cases q; simp_all
      rw [hpq]
    · have e_endL := pair_coset_eq_sortedPair dp.ne01 dq.ne45 h01_rev
      have e_endR : sortedPair p.p4 p.p5 = sortedPair q.p0 q.p1 := by
        rcases hc45 with h45_ok | h45_bad
        · exact pair_coset_eq_sortedPair dp.ne45 dq.ne01 h45_ok
        · exact absurd (e_endL.trans (pair_coset_eq_sortedPair dp.ne45 dq.ne45 h45_bad).symm) hsp_ne
      have ep0 : p.p0 = q.p5 := by
        rcases hp0_end with h0 | h5
        · rw [h0] at e_endL
          exact absurd e_endL (sortedPair_disjoint_ne ⟨dq.ne04, dq.ne05⟩)
        · exact h5
      have ep1 : p.p1 = q.p4 := sortedPair_mem_inj
        (e_endL.trans (sortedPair_comm q.p4 q.p5)) ep0
      have ep5 : p.p5 = q.p0 := by
        rcases hp5_end with h0 | h5
        · exact h0
        · exact absurd (ep0.trans h5.symm) dp.ne05
      have ep4 : p.p4 = q.p1 := sortedPair_mem_inj
        ((sortedPair_comm p.p5 p.p4).trans e_endR) ep5
      have m_eqL := pair_or_eq_of_sortedPair_eq e_endL
      have m_eqR := pair_or_eq_of_sortedPair_eq e_endR
      have hq3_coset : canonCoset (wireBit q.p0 ||| wireBit q.p1 ||| wireBit q.p2) =
                       canonCoset ((wireBit q.p4 ||| wireBit q.p5) ||| wireBit q.p3) := by
        have h3eq : suffixHook q 3 = ((wireBit q.p4 ||| wireBit q.p5) ||| wireBit q.p3) := by
          change (wireBit q.p5 ||| wireBit q.p4) ||| wireBit q.p3 = _
          rw [BitVec.or_comm (wireBit q.p5) (wireBit q.p4)]
        rw [← h3eq, s3q, canonCoset_xor_allOnes]
      rw [hq3_coset, m_eqL] at hc012
      have ep2 : p.p2 = q.p3 := triple_ext_inj (pair_popcount2 dq.ne45)
        (by rw [← m_eqL]; exact disjoint_pair_wire dp.ne02.symm dp.ne12.symm)
        (disjoint_pair_wire dq.ne34 dq.ne35) hc012
      have ep3 : p.p3 = q.p2 := by
        apply wireBit_inj
        have hp3 := xor6_solve_d xorp; have hq2 := xor6_solve_c xorq
        rw [pair_xor_eq_or dp.ne01, pair_xor_eq_or dp.ne45] at hp3
        rw [pair_xor_eq_or dq.ne01, pair_xor_eq_or dq.ne45] at hq2
        rw [hp3, hq2, m_eqL, m_eqR, ep2]
      have hp_rev : p = revPerm q := by
        cases p; cases q; unfold revPerm; simp_all
      rw [hp_rev, canonBarePerm_revPerm]
  · intro hceq
    rw [← bareHookSet_canonBarePerm hp, ← bareHookSet_canonBarePerm hq, hceq]

end ZeroIdleQldpc.HookClasses90
