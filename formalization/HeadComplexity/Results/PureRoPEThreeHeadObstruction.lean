import HeadComplexity.Polynomial.PureRoPEThreeHeadCross
import HeadComplexity.Results.RoPEComparison

set_option linter.style.header false

/-!
# The twelve-bit matching obstruction also excludes three pure rotary heads

The Boolean predicate and its local label certificates are adapted from
`TwelvePairLowerBound.lean` in VerifiedMechanisms/xorformer-runs, commit
1899d884da3affbf21a8528bcb74b409c9783876. The pure-head argument is new.
-/

namespace HeadComplexity.PureRoPEThreeHead

noncomputable section

open Finset PureRoPEThreeHeadCross
open scoped BigOperators

def spin (b : Bool) : ℝ := if b then 1 else -1

def linear {n : ℕ} (v : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ i, v i * spin (x i)

def flip {n : ℕ} (x : Fin n → Bool) : Fin n → Bool := fun i ↦ !(x i)

theorem linear_flip {n : ℕ} (v : Fin n → ℝ) (x : Fin n → Bool) :
    linear v (flip x) = -linear v x := by
  have hs (b : Bool) : spin (!b) = -spin b := by cases b <;> norm_num [spin]
  simp [linear, flip, hs, Finset.sum_neg_distrib]

theorem linear_add {n : ℕ} (u v : Fin n → ℝ) (x : Fin n → Bool) :
    linear (fun i ↦ u i + v i) x = linear u x + linear v x := by
  simp [linear, add_mul, Finset.sum_add_distrib]

theorem linear_smul {n : ℕ} (c : ℝ) (v : Fin n → ℝ) (x : Fin n → Bool) :
    linear (fun i ↦ c * v i) x = c * linear v x := by
  simp [linear, mul_assoc, Finset.mul_sum]

def centerConstant {n : ℕ} (p : PureRoPEAtom n) : ℝ :=
  (p.η + ∑ i, (p.a i * p.v₀ + p.b i * p.v₁) / 2) / p.centerScale

theorem centered_denominator {n : ℕ} (p : PureRoPEAtom n) (x : Fin n → Bool) :
    p.centerScale * (1 + linear p.centerBias x) =
      p.γ + ∑ i, if x i then p.b i else p.a i := by
  have hn := p.centerScale_pos.ne'
  have hterm (i) : p.centerScale * (p.centerBias i * spin (x i)) =
      (p.b i - p.a i) / 2 * spin (x i) := by
    unfold PureRoPEAtom.centerBias
    field_simp
  simp only [linear, mul_add, mul_one, Finset.mul_sum, hterm]
  unfold PureRoPEAtom.centerScale
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp [spin] <;> ring

theorem centered_numerator {n : ℕ} (p : PureRoPEAtom n) (x : Fin n → Bool) :
    p.centerScale * (centerConstant p + linear p.centerSlope x) =
      p.η + ∑ i, if x i then p.b i * p.v₁ else p.a i * p.v₀ := by
  have hn := p.centerScale_pos.ne'
  have hconst : p.centerScale * centerConstant p =
      p.η + ∑ i, (p.a i * p.v₀ + p.b i * p.v₁) / 2 := by
    unfold centerConstant
    field_simp
    simp [mul_comm]
  have hterm (i) : p.centerScale * (p.centerSlope i * spin (x i)) =
      (p.b i * p.v₁ - p.a i * p.v₀) / 2 * spin (x i) := by
    unfold PureRoPEAtom.centerSlope
    field_simp
  simp only [linear, mul_add, Finset.mul_sum, hconst, hterm]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp [spin] <;> ring

theorem centered_denominator_pos {n : ℕ} (p : PureRoPEAtom n) (x : Fin n → Bool) :
    0 < 1 + linear p.centerBias x := by
  have h := p.denominator_pos x
  rw [p.denominator_eq, ← centered_denominator p x] at h
  exact (mul_pos_iff_of_pos_left p.centerScale_pos).mp h

def k {n : ℕ} (p : PureRoPEAtom n) : ℝ := (p.v₁ - p.v₀) / 2
def ell {n : ℕ} (p : PureRoPEAtom n) : ℝ := (p.v₁ + p.v₀) / 2 - centerConstant p

theorem normalized_eval {n : ℕ} (p : PureRoPEAtom n) (x : Fin n → Bool) :
    p.eval x = centerConstant p +
      (k p * linear p.centerMass x + ell p * linear p.centerBias x) /
        (1 + linear p.centerBias x) := by
  have he : p.eval x = (centerConstant p + linear p.centerSlope x) /
      (1 + linear p.centerBias x) := by
    unfold PureRoPEAtom.eval
    rw [← centered_numerator, ← centered_denominator]
    exact mul_div_mul_left _ _ p.centerScale_pos.ne'
  rw [he]
  have hs : linear p.centerSlope x =
      k p * linear p.centerMass x + (p.v₁ + p.v₀) / 2 * linear p.centerBias x := by
    simp only [linear, p.centerSlope_eq]
    simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, k]
  rw [hs]
  have hden := (centered_denominator_pos p x).ne'
  unfold ell
  field_simp
  ring

def quadratic {n : ℕ} (c : ℝ) (k l : Fin 3 → ℝ)
    (s b : Fin 3 → Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  c + (k 0 * linear (s 0) x + l 0 * linear (b 0) x) *
      (linear (b 1) x + linear (b 2) x) +
    (k 1 * linear (s 1) x + l 1 * linear (b 1) x) *
      (linear (b 0) x + linear (b 2) x) +
    (k 2 * linear (s 2) x + l 2 * linear (b 2) x) *
      (linear (b 0) x + linear (b 1) x)

/-- Even Boolean signs of three pure heads have the pure quadratic form. -/
theorem exists_quadratic {n : ℕ} (f : (Fin n → Bool) → Bool)
    (heven : ∀ x, f (flip x) = f x) (hf : pureRoPEComputable n 3 f) :
    ∃ (c : ℝ) (k l : Fin 3 → ℝ) (s b : Fin 3 → Fin n → ℝ),
      (∀ h i, 0 < s h i) ∧ ∀ x, 0 < quadratic c k l s b x ↔ f x = true := by
  obtain ⟨p, c, hp⟩ := hf
  let T := c + ∑ h, centerConstant (p h)
  let B (h : Fin 3) := (p h).centerBias
  let S (h : Fin 3) := (p h).centerMass
  let U (h : Fin 3) (x) := k (p h) * linear (S h) x + ell (p h) * linear (B h) x
  let P (x : Fin n → Bool) :=
    T * (1 + linear (B 0) x) * (1 + linear (B 1) x) * (1 + linear (B 2) x) +
      U 0 x * (1 + linear (B 1) x) * (1 + linear (B 2) x) +
      U 1 x * (1 + linear (B 0) x) * (1 + linear (B 2) x) +
      U 2 x * (1 + linear (B 0) x) * (1 + linear (B 1) x)
  have hD (h : Fin 3) (x) : 0 < 1 + linear (B h) x := centered_denominator_pos (p h) x
  have hP (x) : 0 < P x ↔ f x = true := by
    have he : P x = ((1 + linear (B 0) x) * (1 + linear (B 1) x) *
        (1 + linear (B 2) x)) * (c + ∑ h, (p h).eval x) := by
      simp only [normalized_eval, Fin.sum_univ_three]
      dsimp only [P, T, U, S, B]
      simp only [Fin.sum_univ_three]
      have h0 := (hD 0 x).ne'
      have h1 := (hD 1 x).ne'
      have h2 := (hD 2 x).ne'
      dsimp only [B] at h0 h1 h2
      field_simp
      ring
    rw [he, mul_pos_iff_of_pos_left (mul_pos (mul_pos (hD 0 x) (hD 1 x)) (hD 2 x))]
    exact hp x
  refine ⟨T, fun h ↦ k (p h), fun h ↦ ell (p h) + T / 2, S, B, ?_, ?_⟩
  · intro h i
    exact (abs_nonneg ((p h).centerBias i)).trans_lt ((p h).abs_centerBias_lt_centerMass i)
  · intro x
    have hid : quadratic T (fun h ↦ k (p h)) (fun h ↦ ell (p h) + T / 2) S B x =
        (P x + P (flip x)) / 2 := by
      dsimp only [P, U]
      simp only [linear_flip]
      have hi := evenization T (fun h ↦ linear (B h) x) (fun h ↦ U h x)
      dsimp only [U] at hi
      dsimp only [quadratic]
      linear_combination -hi
    rw [hid]
    cases hx : f x with
    | true =>
      have h1 := (hP x).mpr hx
      have h2 := (hP (flip x)).mpr ((heven x).trans hx)
      exact iff_of_true (by linarith) rfl
    | false =>
      have h1 : P x ≤ 0 := le_of_not_gt (fun h ↦ by have := (hP x).mp h; simp [hx] at this)
      have h2 : P (flip x) ≤ 0 := le_of_not_gt (fun h ↦ by
        have := (hP (flip x)).mp h
        rw [heven x, hx] at this
        contradiction)
      exact iff_of_false (by linarith) (by simp)

def face {n : ℕ} (x : Fin n → Bool) (i j : Fin n) (s t : Bool) : Fin n → Bool :=
  Function.update (Function.update x i s) j t

theorem linear_update {n : ℕ} (a : Fin n → ℝ) (x : Fin n → Bool)
    (i : Fin n) (s : Bool) :
    linear a (Function.update x i s) = linear a x + a i * (spin s - spin (x i)) := by
  have hd : linear a (Function.update x i s) - linear a x =
      a i * (spin s - spin (x i)) := by
    unfold linear
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp [mul_sub]
    · intro j _ hji
      simp [Function.update_of_ne hji]
    · simp
  linarith

def zeroAtom (n : ℕ) : PureRoPEAtom n where
  a _ := 1
  b _ := 1
  γ := 1
  η := 0
  v₀ := 0
  v₁ := 0
  ha _ := zero_lt_one
  hb _ := zero_lt_one
  hγ := zero_lt_one

theorem zeroAtom_eval {n : ℕ} (x : Fin n → Bool) : (zeroAtom n).eval x = 0 := by
  simp [PureRoPEAtom.eval, zeroAtom]

theorem computable_succ {n H : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : pureRoPEComputable n H f) : pureRoPEComputable n (H + 1) f := by
  obtain ⟨p, c, hp⟩ := hf
  refine ⟨Fin.cases (zeroAtom n) p, c, fun x ↦ ?_⟩
  simpa only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, zeroAtom_eval, zero_add]
    using hp x

theorem computable_mono {n H K : ℕ} {f : (Fin n → Bool) → Bool}
    (hHK : H ≤ K) (hf : pureRoPEComputable n H f) : pureRoPEComputable n K f := by
  exact Nat.le_induction (P := fun J _ ↦ pureRoPEComputable n J f) hf
    (fun _ _ h ↦ computable_succ h) K hHK

namespace TwelvePair

def left : Fin 6 → Fin 12 := ![0, 2, 4, 6, 8, 10]
def right : Fin 6 → Fin 12 := ![1, 3, 5, 7, 9, 11]
def integerSpin (b : Bool) : ℤ := if b then 1 else -1
def scoreInt (x : Fin 12 → Bool) : ℤ :=
  22 + 20 * (∑ i : Fin 6, integerSpin (x (left i)) * integerSpin (x (right i))) -
    (∑ i : Fin 12, integerSpin (x i)) ^ 2
def function (x : Fin 12 → Bool) : Bool := decide (0 < scoreInt x)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Check global complementation on the full finite cube by kernel reduction.
theorem function_even : ∀ x, function (flip x) = function x := by decide +kernel

def zeroInput : Fin 12 → Bool := fun _ ↦ false
def singletonInput (j : Fin 6) : Fin 12 → Bool := Function.update zeroInput (right j) true
def doubleInput (j k : Fin 6) : Fin 12 → Bool :=
  Function.update (singletonInput j) (right k) true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Check the base, singleton, and doubleton integer labels in the kernel.
theorem slice_labels : function zeroInput = false ∧
    (∀ j, function (singletonInput j) = true) ∧
    (∀ j k, j ≠ k → function (doubleInput j k) = false) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Check the thirty off-diagonal cross faces by integer kernel reduction.
theorem cross_faces : ∀ i j : Fin 6, i ≠ j → ∀ s t : Bool,
    function (face zeroInput (left i) (right j) s t) = decide (s ≠ t) := by decide +kernel

def productScore (c : ℝ) (A V : Fin 3 → Fin 12 → ℝ) (x : Fin 12 → Bool) : ℝ :=
  c + ∑ h, linear (A h) x * linear (V h) x

def crossCoefficient (A V : Fin 3 → Fin 12 → ℝ) (i j : Fin 6) : ℝ :=
  ∑ h, (A h (left i) * V h (right j) + V h (left i) * A h (right j))

theorem product_face_difference (c : ℝ) (A V : Fin 3 → Fin 12 → ℝ)
    (x : Fin 12 → Bool) (i j : Fin 12) (hij : i ≠ j) :
    productScore c A V (face x i j false false) +
      productScore c A V (face x i j true true) -
      productScore c A V (face x i j false true) -
      productScore c A V (face x i j true false) =
      4 * ∑ h, (A h i * V h j + V h i * A h j) := by
  simp only [productScore, face, linear_update, Function.update_of_ne (Ne.symm hij),
    spin, Bool.false_eq_true, ite_false, ite_true, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 8000000 in
-- Normalize six identities among quadratic polynomials in the coefficients.
theorem column_identity (c : ℝ) (A V : Fin 3 → Fin 12 → ℝ) (j : Fin 6) :
    4 * (∑ i, crossCoefficient A V i j) =
      3 * productScore c A V (singletonInput j) - 3 * productScore c A V zeroInput +
      ∑ k : Fin 6, if k = j then 0 else
        productScore c A V (singletonInput k) - productScore c A V (doubleInput j k) := by
  fin_cases j <;>
    simp [productScore, singletonInput, doubleInput, crossCoefficient, left, right,
      linear, spin, zeroInput, Fin.sum_univ_succ] <;> ring

theorem column_sum_pos (c : ℝ) (A V : Fin 3 → Fin 12 → ℝ)
    (hs : ∀ x, 0 < productScore c A V x ↔ function x = true) (j : Fin 6) :
    0 < ∑ i, crossCoefficient A V i j := by
  have hp (k : Fin 6) : 0 < productScore c A V (singletonInput k) :=
    (hs _).mpr (slice_labels.2.1 k)
  have hz : productScore c A V zeroInput ≤ 0 := by
    have h := hs zeroInput
    rw [slice_labels.1] at h
    simpa using h
  have hn (k : Fin 6) (hjk : j ≠ k) : productScore c A V (doubleInput j k) ≤ 0 := by
    have h := hs (doubleInput j k)
    rw [slice_labels.2.2 j k hjk] at h
    simpa using h
  have hsum : 0 ≤ ∑ k : Fin 6, if k = j then 0 else
      productScore c A V (singletonInput k) - productScore c A V (doubleInput j k) := by
    apply Finset.sum_nonneg
    intro k _
    split_ifs with h
    · exact le_refl 0
    · linarith [hp k, hn k (Ne.symm h)]
  have hid := column_identity c A V j
  linarith [hp j]

theorem cross_negative (c : ℝ) (A V : Fin 3 → Fin 12 → ℝ)
    (hs : ∀ x, 0 < productScore c A V x ↔ function x = true)
    (i j : Fin 6) (hij : i ≠ j) : crossCoefficient A V i j < 0 := by
  have hidx : left i ≠ right j := by fin_cases i <;> fin_cases j <;> decide
  have hd := product_face_difference c A V zeroInput (left i) (right j) hidx
  have h00 := hs (face zeroInput (left i) (right j) false false)
  have h11 := hs (face zeroInput (left i) (right j) true true)
  have h01 := hs (face zeroInput (left i) (right j) false true)
  have h10 := hs (face zeroInput (left i) (right j) true false)
  rw [cross_faces i j hij] at h00 h11 h01 h10
  simp only [ne_eq, Bool.false_eq_true, Bool.true_eq_false, decide_true, decide_false,
    not_false_eq_true, not_true_eq_false, iff_true, iff_false, not_lt] at h00 h11 h01 h10
  change _ = 4 * crossCoefficient A V i j at hd
  linarith

def leftFactors (k l : Fin 3 → ℝ) (s b : Fin 3 → Fin 12 → ℝ) :
    Fin 3 → Fin 12 → ℝ := fun h i ↦ k h * s h i + l h * b h i

def rightFactors (b : Fin 3 → Fin 12 → ℝ) : Fin 3 → Fin 12 → ℝ :=
  ![fun i ↦ b 1 i + b 2 i, fun i ↦ b 0 i + b 2 i, fun i ↦ b 0 i + b 1 i]

theorem quadratic_eq_product (c : ℝ) (k l : Fin 3 → ℝ) (s b : Fin 3 → Fin 12 → ℝ)
    (x : Fin 12 → Bool) :
    quadratic c k l s b x = productScore c (leftFactors k l s b) (rightFactors b) x := by
  have h (i : Fin 3) : linear (leftFactors k l s b i) x =
      k i * linear (s i) x + l i * linear (b i) x := by
    change linear (fun j ↦ k i * s i j + l i * b i j) x = _
    rw [linear_add, linear_smul, linear_smul]
  simp [quadratic, productScore, rightFactors, linear_add, h, Fin.sum_univ_three]
  ring

theorem pure_cross (k l : Fin 3 → ℝ) (s b : Fin 3 → Fin 12 → ℝ) (i j : Fin 6) :
    crossCoefficient (leftFactors k l s b) (rightFactors b) i j =
      cross k l (fun h i ↦ s h (left i)) (fun h i ↦ b h (left i))
        (fun h j ↦ s h (right j)) (fun h j ↦ b h (right j)) i j := by
  simp [crossCoefficient, leftFactors, rightFactors, cross, columns, transform,
    dotProduct, Fin.sum_univ_succ]
  ring

theorem no_quadratic (c : ℝ) (k l : Fin 3 → ℝ) (s b : Fin 3 → Fin 12 → ℝ)
    (hs : ∀ h i, 0 < s h i)
    (hrep : ∀ x, 0 < quadratic c k l s b x ↔ function x = true) : False := by
  have hp : ∀ x, 0 < productScore c (leftFactors k l s b) (rightFactors b) x ↔
      function x = true := by intro x; rw [← quadratic_eq_product]; exact hrep x
  apply obstruction k l
    (fun h i ↦ s h (left i)) (fun h i ↦ b h (left i))
    (fun h j ↦ s h (right j)) (fun h j ↦ b h (right j))
    (fun h i ↦ hs h (left i)) (fun h j ↦ hs h (right j))
  · intro i j hij
    rw [← pure_cross]
    exact (cross_negative _ _ _ hp i j hij).le
  · intro j
    simp_rw [← pure_cross]
    exact column_sum_pos _ _ _ hp j

/-- The twelve-bit matching function is not a three-head pure-RoPE classifier. -/
theorem not_pureRoPEComputable_three : ¬ pureRoPEComputable 12 3 function := by
  intro hf
  obtain ⟨c, k, l, s, b, hs, hrep⟩ := exists_quadratic function function_even hf
  exact no_quadratic c k l s b hs hrep

theorem pureRoPEHStar_ge_four : 4 ≤ PureRoPEHStar 12 function := by
  by_contra h
  have hle : PureRoPEHStar 12 function ≤ 3 := by omega
  exact not_pureRoPEComputable_three (computable_mono hle (pureRoPEHStar_computable function))

theorem vanillaHStar_ge_four : 4 ≤ HStar 12 function :=
  pureRoPEHStar_ge_four.trans (pureRoPEHStar_le_vanilla function)

end TwelvePair

end
end HeadComplexity.PureRoPEThreeHead
