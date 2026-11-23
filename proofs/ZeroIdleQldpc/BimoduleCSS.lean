/-
  ZeroIdleQldpc.BimoduleCSS
  =========================
  Formal proof that Two-Block Group-Algebra (2BGA) CSS parity-check matrices
    H_X = [ L(A) | R(B) ]   and   H_Z = [ R(B)^T | L(A)^T ]
  satisfy exact GF(2) orthogonality (H_X H_Z^T = 0 mod 2) over ANY finite group G
  (abelian or non-abelian), using ONLY multiplication associativity so that the
  left regular action L(a)(x) = a * x commutes with the right regular action
  R(b)(x) = x * b.

  Includes an explicit non-abelian witness on the dihedral/symmetric group
  D_3 ≅ S_3 of order 6.
-/

namespace ZeroIdleQldpc.BimoduleCSS

/-- Finite group structure on `Fin m` with NO commutativity hypothesis. -/
structure FinGroup (m : Nat) where
  one : Fin m
  mul : Fin m → Fin m → Fin m
  inv : Fin m → Fin m
  mul_assoc : ∀ a b c : Fin m, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : Fin m, mul one a = a
  mul_one : ∀ a : Fin m, mul a one = a
  inv_mul_cancel : ∀ a : Fin m, mul (inv a) a = one
  mul_inv_cancel : ∀ a : Fin m, mul a (inv a) = one

/-- Left regular action `L(a)(x) = a * x`. -/
def L {m : Nat} (G : FinGroup m) (a x : Fin m) : Fin m :=
  G.mul a x

/-- Right regular action `R(b)(x) = x * b`. -/
def R {m : Nat} (G : FinGroup m) (b x : Fin m) : Fin m :=
  G.mul x b

/-- Bimodule commutativity: left multiplication and right multiplication commute
    over every finite group solely by associativity `(a * x) * b = a * (x * b)`. -/
theorem left_right_comm {m : Nat} (G : FinGroup m) (a b x : Fin m) :
    L G a (R G b x) = R G b (L G a x) :=
  (G.mul_assoc a x b).symm

/-! ### GF(2) (`Bool`) Algebra Helpers -/

/-- Fold XOR (`GF(2)` sum) over `Fin n`. -/
def xorSum : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => false
  | n + 1, f =>
    xor (xorSum n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
        (f ⟨n, Nat.lt_succ_self n⟩)

/-- `GF(2)` inner product of two length-`n` binary vectors. -/
def dotGF2 {n : Nat} (u v : Fin n → Bool) : Bool :=
  xorSum n (fun k => u k && v k)

theorem xorSum_congr {n : Nat} {f g : Fin n → Bool} (h : ∀ i, f i = g i) :
    xorSum n f = xorSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorSum]
    rw [ih (fun i => h _), h]

theorem xorSum_false (n : Nat) : xorSum n (fun _ => false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [xorSum, ih]

theorem xorSum_xor {n : Nat} (f g : Fin n → Bool) :
    xorSum n (fun i => xor (f i) (g i)) = xor (xorSum n f) (xorSum n g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorSum, ih]
    cases xorSum n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) <;>
    cases xorSum n (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) <;>
    cases f ⟨n, Nat.lt_succ_self n⟩ <;>
    cases g ⟨n, Nat.lt_succ_self n⟩ <;> rfl

theorem xorSum_and_right {n : Nat} (f : Fin n → Bool) (c : Bool) :
    (xorSum n f && c) = xorSum n (fun i => f i && c) := by
  induction n with
  | zero => cases c <;> rfl
  | succ n ih =>
    simp only [xorSum]
    have hd : ∀ x y z : Bool, (xor x y && z) = xor (x && z) (y && z) := by
      intro x y z; cases x <;> cases y <;> cases z <;> rfl
    rw [hd, ih]

theorem xorSum_and_left {n : Nat} (c : Bool) (f : Fin n → Bool) :
    (c && xorSum n f) = xorSum n (fun i => c && f i) := by
  induction n with
  | zero => cases c <;> rfl
  | succ n ih =>
    simp only [xorSum]
    have hd : ∀ x y z : Bool, (x && xor y z) = xor (x && y) (x && z) := by
      intro x y z; cases x <;> cases y <;> cases z <;> rfl
    rw [hd, ih]

theorem xorSum_comm {n k : Nat} (h : Fin n → Fin k → Bool) :
    xorSum n (fun a => xorSum k (fun b => h a b)) =
    xorSum k (fun b => xorSum n (fun a => h a b)) := by
  induction n with
  | zero =>
    simp only [xorSum]
    exact (xorSum_false k).symm
  | succ n ih =>
    simp only [xorSum]
    rw [ih, (xorSum_xor _ _).symm]

/-- Kronecker-delta collapse over `Fin n`: `⊕_x ([target = x] && g x) = g target`. -/
theorem xorSum_delta : ∀ (n : Nat) (target : Fin n) (g : Fin n → Bool),
    xorSum n (fun x => decide (target = x) && g x) = g target
  | 0, target, _ => Fin.elim0 target
  | n + 1, target, g => by
    simp only [xorSum]
    by_cases hlast : target = ⟨n, Nat.lt_succ_self n⟩
    · subst hlast
      have hzero : xorSum n (fun i =>
          decide ((⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) =
                  ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) &&
          g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) = false := by
        refine Eq.trans (xorSum_congr fun i => ?_) (xorSum_false n)
        have hne : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) ≠
                   ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
          intro heq
          have hv : n = i.val := congrArg Fin.val heq
          exact Nat.ne_of_lt i.isLt hv.symm
        simp [hne]
      rw [hzero]
      simp
    · have hlt : target.val < n := by
        have hne_val : target.val ≠ n := fun hv => hlast (Fin.ext hv)
        omega
      let t' : Fin n := ⟨target.val, hlt⟩
      have hsub : xorSum n (fun i =>
          decide (target = ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) &&
          g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) =
          xorSum n (fun i => decide (t' = i) && g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) := by
        apply xorSum_congr
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
      rw [hsub, xorSum_delta n t' (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)]
      have ht' : (⟨t'.val, Nat.lt_succ_of_lt t'.isLt⟩ : Fin (n + 1)) = target :=
        Fin.ext rfl
      rw [ht']
      simp [hlast]

/-- Splitting `xorSum (a + b)` into left `Fin a` and right `Fin b` halves. -/
theorem xorSum_add (a : Nat) : ∀ (b : Nat) (f : Fin (a + b) → Bool),
    xorSum (a + b) f =
    xor (xorSum a (fun i => f ⟨i.val, by omega⟩))
        (xorSum b (fun j => f ⟨a + j.val, by omega⟩))
  | 0, f => by
    simp only [xorSum, Bool.xor_false]
    rfl
  | b + 1, f => by
    have hstep : xorSum (a + (b + 1)) f =
        xor (xorSum (a + b) (fun i => f ⟨i.val, by omega⟩))
            (f ⟨a + b, by omega⟩) := rfl
    rw [hstep, xorSum_add a b (fun i => f ⟨i.val, by omega⟩)]
    simp only [xorSum]
    cases xorSum a (fun i => f ⟨i.val, by omega⟩) <;>
    cases xorSum b (fun j => f ⟨a + j.val, by omega⟩) <;>
    cases f ⟨a + b, by omega⟩ <;> rfl

theorem xorSum_cast {a b : Nat} (hab : a = b) (f : Fin a → Bool) :
    xorSum a f = xorSum b (fun i => f ⟨i.val, by omega⟩) := by
  subst hab
  exact xorSum_congr (fun _ => rfl)

/-! ### 2-Block Group-Algebra (2BGA) CSS Matrices -/

/-- Concatenate two length-`m` block vectors into a length-`2 * m` row vector. -/
def twoBlockVec {m : Nat} (leftBlock rightBlock : Fin m → Bool) (q : Fin (2 * m)) : Bool :=
  if h : q.val < m then
    leftBlock ⟨q.val, h⟩
  else
    rightBlock ⟨q.val - m, by omega⟩

theorem dotGF2_twoBlock {m : Nat} (uL uR vL vR : Fin m → Bool) :
    dotGF2 (twoBlockVec uL uR) (twoBlockVec vL vR) =
    xor (dotGF2 uL vL) (dotGF2 uR vR) := by
  unfold dotGF2
  let f : Fin (2 * m) → Bool := fun q => twoBlockVec uL uR q && twoBlockVec vL vR q
  rw [xorSum_cast (Nat.two_mul m) f, xorSum_add m m]
  have hL : xorSum m (fun i => f ⟨i.val, by omega⟩) =
            xorSum m (fun i => uL i && vL i) := by
    apply xorSum_congr
    intro i
    simp [f, twoBlockVec, i.isLt]
  have hR : xorSum m (fun j => f ⟨m + j.val, by omega⟩) =
            xorSum m (fun j => uR j && vR j) := by
    apply xorSum_congr
    intro j
    have hnot : ¬ (m + j.val < m) := by omega
    have hsub : m + j.val - m = j.val := by omega
    simp [f, twoBlockVec, hnot, hsub]
  rw [hL, hR]

/-- Convert a list of check-support group elements in `Fin m` into its `GF(2)`
    group-algebra parity indicator `Fin m → Bool` (handling multiplicity mod 2). -/
def listSupport {m : Nat} (terms : List (Fin m)) (g : Fin m) : Bool :=
  terms.foldl (fun acc t => xor acc (decide (t = g))) false

/-- Left group-algebra matrix block `L(A)_{i, x} = ⊕_{a : A(a)} [L_a(i) = x]`. -/
def matL {m : Nat} (G : FinGroup m) (A : Fin m → Bool) (i x : Fin m) : Bool :=
  xorSum m (fun a => A a && decide (L G a i = x))

/-- Right group-algebra matrix block `R(B)_{i, x} = ⊕_{b : B(b)} [R_b(i) = x]`. -/
def matR {m : Nat} (G : FinGroup m) (B : Fin m → Bool) (i x : Fin m) : Bool :=
  xorSum m (fun b => B b && decide (R G b i = x))

/-- Row `i` of `H_X = [ L(A) | R(B) ]`. -/
def hxRow {m : Nat} (G : FinGroup m) (A B : Fin m → Bool) (i : Fin m) : Fin (2 * m) → Bool :=
  twoBlockVec (matL G A i) (matR G B i)

/-- Row `j` of `H_Z = [ R(B)^T | L(A)^T ]`. -/
def hzRow {m : Nat} (G : FinGroup m) (A B : Fin m → Bool) (j : Fin m) : Fin (2 * m) → Bool :=
  twoBlockVec (fun x => matR G B x j) (fun x => matL G A x j)

/-- Row `i` of `H_X` from check-support lists `A, B : List (Fin m)`. -/
def hxRowList {m : Nat} (G : FinGroup m) (A B : List (Fin m)) (i : Fin m) : Fin (2 * m) → Bool :=
  hxRow G (listSupport A) (listSupport B) i

/-- Row `j` of `H_Z` from check-support lists `A, B : List (Fin m)`. -/
def hzRowList {m : Nat} (G : FinGroup m) (A B : List (Fin m)) (j : Fin m) : Fin (2 * m) → Bool :=
  hzRow G (listSupport A) (listSupport B) j

private theorem left_block_dot {m : Nat} (G : FinGroup m) (A B : Fin m → Bool) (i j : Fin m) :
    dotGF2 (matL G A i) (fun x => matR G B x j) =
    xorSum m (fun a => xorSum m (fun b => (A a && B b) && decide (R G b (L G a i) = j))) := by
  unfold dotGF2 matL matR
  have h1 : xorSum m (fun x =>
      xorSum m (fun a => A a && decide (L G a i = x)) &&
      xorSum m (fun b => B b && decide (R G b x = j))) =
      xorSum m (fun x => xorSum m (fun a => xorSum m (fun b =>
        (A a && B b) && (decide (L G a i = x) && decide (R G b x = j))))) := by
    apply xorSum_congr
    intro x
    rw [xorSum_and_right]
    apply xorSum_congr
    intro a
    rw [xorSum_and_left]
    apply xorSum_congr
    intro b
    cases A a <;> cases B b <;> cases decide (L G a i = x) <;> cases decide (R G b x = j) <;> rfl
  rw [h1, xorSum_comm]
  apply xorSum_congr
  intro a
  rw [xorSum_comm]
  apply xorSum_congr
  intro b
  rw [← xorSum_and_left, xorSum_delta m (L G a i) (fun x => decide (R G b x = j))]

private theorem right_block_dot {m : Nat} (G : FinGroup m) (A B : Fin m → Bool) (i j : Fin m) :
    dotGF2 (matR G B i) (fun y => matL G A y j) =
    xorSum m (fun a => xorSum m (fun b => (A a && B b) && decide (L G a (R G b i) = j))) := by
  unfold dotGF2 matL matR
  have h1 : xorSum m (fun y =>
      xorSum m (fun b => B b && decide (R G b i = y)) &&
      xorSum m (fun a => A a && decide (L G a y = j))) =
      xorSum m (fun y => xorSum m (fun b => xorSum m (fun a =>
        (A a && B b) && (decide (R G b i = y) && decide (L G a y = j))))) := by
    apply xorSum_congr
    intro y
    rw [xorSum_and_right]
    apply xorSum_congr
    intro b
    rw [xorSum_and_left]
    apply xorSum_congr
    intro a
    cases A a <;> cases B b <;> cases decide (R G b i = y) <;> cases decide (L G a y = j) <;> rfl
  rw [h1, xorSum_comm]
  have h2 : xorSum m (fun b => xorSum m (fun y => xorSum m (fun a =>
      (A a && B b) && (decide (R G b i = y) && decide (L G a y = j))))) =
      xorSum m (fun b => xorSum m (fun a =>
        (A a && B b) && decide (L G a (R G b i) = j))) := by
    apply xorSum_congr
    intro b
    rw [xorSum_comm]
    apply xorSum_congr
    intro a
    rw [← xorSum_and_left, xorSum_delta m (R G b i) (fun y => decide (L G a y = j))]
  rw [h2, xorSum_comm]

/-- **Main Algebraic Theorem (`css_orthogonality`)**:
    For ANY finite group `G` on `Fin m` (abelian or non-abelian!) and arbitrary
    subsets/predicates `A, B : Fin m → Bool`, every X-check row of `H_X = [L(A) | R(B)]`
    is `GF(2)`-orthogonal to every Z-check row of `H_Z = [R(B)^T | L(A)^T]`. -/
theorem css_orthogonality {m : Nat} (G : FinGroup m) (A B : Fin m → Bool) (i j : Fin m) :
    dotGF2 (hxRow G A B i) (hzRow G A B j) = false := by
  unfold hxRow hzRow
  rw [dotGF2_twoBlock, left_block_dot, right_block_dot]
  have heq :
      xorSum m (fun a => xorSum m (fun b => (A a && B b) && decide (R G b (L G a i) = j))) =
      xorSum m (fun a => xorSum m (fun b => (A a && B b) && decide (L G a (R G b i) = j))) := by
    apply xorSum_congr
    intro a
    apply xorSum_congr
    intro b
    rw [left_right_comm G a b i]
  rw [heq]
  cases xorSum m (fun a => xorSum m (fun b => (A a && B b) && decide (L G a (R G b i) = j))) <;> rfl

/-- List-support version of `css_orthogonality`: arbitrary check-support lists
    `A, B : List (Fin m)` yield `H_X H_Z^T = 0 mod 2` over any finite group `G`. -/
theorem css_orthogonality_list {m : Nat} (G : FinGroup m) (A B : List (Fin m)) (i j : Fin m) :
    dotGF2 (hxRowList G A B i) (hzRowList G A B j) = false :=
  css_orthogonality G (listSupport A) (listSupport B) i j

/-! ### Explicit Non-Abelian Group Witness: Dihedral/Symmetric Group `D_3 ≅ S_3` (Order 6) -/

/-- Multiplication in `D_3 = ⟨r, s | r^3 = s^2 = 1, r * s = s * r^2⟩`,
    encoding `s^k * r^j` (`k ∈ {0,1}`, `j ∈ {0,1,2}`) as `3 * k + j : Fin 6`. -/
def s3Mul (x y : Fin 6) : Fin 6 :=
  let k1 := x.val / 3
  let j1 := x.val % 3
  let k2 := y.val / 3
  let j2 := y.val % 3
  let k  := (k1 + k2) % 2
  let j  := if k2 == 0 then (j1 + j2) % 3 else (3 - j1 + j2) % 3
  have hk : k < 2 := Nat.mod_lt _ (by decide)
  have hj : j < 3 := by
    dsimp [j]
    split <;> exact Nat.mod_lt _ (by decide)
  ⟨3 * k + j, by omega⟩

/-- Inverse in `D_3`: rotations invert via `(3 - j) % 3`; reflections are involutions. -/
def s3Inv (x : Fin 6) : Fin 6 :=
  if x.val / 3 == 0 then
    ⟨(3 - x.val % 3) % 3, by have := Nat.mod_lt (3 - x.val % 3) (by decide : 0 < 3); omega⟩
  else
    x

/-- Verified non-abelian finite group `S_3 ≅ D_3` of order 6. -/
def S3 : FinGroup 6 where
  one := 0
  mul := s3Mul
  inv := s3Inv
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide
  mul_inv_cancel := by decide

/-- `S3` is genuinely non-abelian (`r * s = 5 ≠ 4 = s * r`). -/
theorem s3_non_abelian : ∃ a b : Fin 6, S3.mul a b ≠ S3.mul b a :=
  ⟨1, 3, by decide⟩

/-- Explicit weight-3 check supports over non-abelian `S3` satisfy `H_X H_Z^T = 0 mod 2`. -/
theorem s3_css_witness (i j : Fin 6) :
    dotGF2 (hxRowList S3 [0, 1, 3] [0, 2, 4] i)
           (hzRowList S3 [0, 1, 3] [0, 2, 4] j) = false :=
  css_orthogonality_list S3 [0, 1, 3] [0, 2, 4] i j

end ZeroIdleQldpc.BimoduleCSS
