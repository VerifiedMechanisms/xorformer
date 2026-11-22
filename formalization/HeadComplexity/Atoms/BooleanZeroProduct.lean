import Mathlib.Tactic

set_option linter.style.header false

/-! Classification of normalized pairs of nonzero affine forms whose product
vanishes on a Boolean cube. This describes a base locus of the Hadamard square;
it is not a head-complexity lower bound. -/

namespace HeadComplexity.BooleanZeroProduct

open Finset

def affine {I : Type*} (c : ℝ) (a : I → ℝ) (s : Finset I) : ℝ :=
  c + ∑ i ∈ s, a i

theorem coefficient_relations {I : Type*} [DecidableEq I]
    (a b : I → ℝ)
    (h : ∀ s : Finset I, affine 0 a s * affine 1 b s = 0) :
    (∀ i, a i * (1 + b i) = 0) ∧
      (∀ i j, i ≠ j → a i * b j + a j * b i = 0) := by
  have hs (i : I) : a i * (1 + b i) = 0 := by
    simpa [affine] using h {i}
  refine ⟨hs, ?_⟩
  intro i j hij
  have hp : (a i + a j) * (1 + (b i + b j)) = 0 := by
    simpa [affine, hij] using h {i, j}
  have hi := hs i
  have hj := hs j
  nlinarith only [hp, hi, hj]

theorem normalized_classification {I : Type*} [DecidableEq I]
    (a b : I → ℝ) (ha : ∃ i, a i ≠ 0)
    (h : ∀ s : Finset I, affine 0 a s * affine 1 b s = 0) :
    (∃ i t, t ≠ 0 ∧
      (∀ k, a k = if k = i then t else 0) ∧
      (∀ k, b k = if k = i then -1 else 0)) ∨
    (∃ i j t, i ≠ j ∧ t ≠ 0 ∧
      (∀ k, a k = if k = i then t else if k = j then -t else 0) ∧
      (∀ k, b k = if k = i then -1 else if k = j then -1 else 0)) := by
  obtain ⟨hs, hc⟩ := coefficient_relations a b h
  have hb (i : I) (hi : a i ≠ 0) : b i = -1 := by
    have hz := (mul_eq_zero.mp (hs i)).resolve_left hi
    linarith
  obtain ⟨i, hi⟩ := ha
  have hbi := hb i hi
  have hout (k : I) (hk : a k = 0) : b k = 0 := by
    have hki : i ≠ k := by intro he; subst k; exact hi hk
    have hz := hc i k hki
    rw [hk, zero_mul, add_zero] at hz
    exact (mul_eq_zero.mp hz).resolve_left hi
  by_cases hex : ∃ j, j ≠ i ∧ a j ≠ 0
  · obtain ⟨j, hji, hj⟩ := hex
    have hij := Ne.symm hji
    have hbj := hb j hj
    have haj : a j = -a i := by
      have hz := hc i j hij
      rw [hbi, hbj] at hz
      linarith
    have hak (k : I) (hki : k ≠ i) (hkj : k ≠ j) : a k = 0 := by
      by_contra hk
      have hbk := hb k hk
      have h₁ := hc i k (Ne.symm hki)
      have h₂ := hc j k (Ne.symm hkj)
      rw [hbi, hbk] at h₁
      rw [hbj, hbk, haj] at h₂
      have : a i = 0 := by linarith
      exact hi this
    right
    refine ⟨i, j, a i, hij, hi, ?_, ?_⟩
    · intro k
      by_cases hki : k = i
      · subst k; simp
      by_cases hkj : k = j
      · subst k; simp [hji, haj]
      simp [hki, hkj, hak k hki hkj]
    · intro k
      by_cases hki : k = i
      · subst k; simp [hbi]
      by_cases hkj : k = j
      · subst k; simp [hji, hbj]
      simp [hki, hkj, hout k (hak k hki hkj)]
  · have hak (k : I) (hki : k ≠ i) : a k = 0 := by
      by_contra hk
      exact hex ⟨k, hki, hk⟩
    left
    refine ⟨i, a i, hi, ?_, ?_⟩
    · intro k
      by_cases hki : k = i
      · subst k; simp
      simp [hki, hak k hki]
    · intro k
      by_cases hki : k = i
      · subst k; simp [hbi]
      simp [hki, hout k (hak k hki)]

theorem nonzero_constant_needed {I : Type*} [DecidableEq I]
    (a b : I → ℝ) (ha : ∃ i, a i ≠ 0) (hb : ∃ j, b j ≠ 0) :
    ¬ (∀ s : Finset I, affine 0 a s * affine 0 b s = 0) := by
  intro h
  have hs (i : I) : a i * b i = 0 := by
    simpa [affine] using h {i}
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  have hbi : b i = 0 := (mul_eq_zero.mp (hs i)).resolve_left hi
  have haj : a j = 0 := (mul_eq_zero.mp (hs j)).resolve_right hj
  have hij : i ≠ j := by intro he; subst j; exact hi haj
  have hp : (a i + a j) * (b i + b j) = 0 := by
    simpa [affine, hij] using h {i, j}
  rw [haj, hbi, add_zero, zero_add] at hp
  exact hj ((mul_eq_zero.mp hp).resolve_left hi)

/-- The derivative of the six nonconstant reduced product coefficients at
`a = (1,2,3)` and `b = (4,5,7)`. The analytic interpretation is in the writeup. -/
def threeBitJacobian : Matrix (Fin 6) (Fin 6) ℤ := ![
  ![5, 0, 0, 2, 0, 0], ![0, 6, 0, 0, 3, 0],
  ![0, 0, 8, 0, 0, 4], ![5, 4, 0, 2, 1, 0],
  ![7, 0, 4, 3, 0, 1], ![0, 7, 5, 0, 3, 2]]

def threeBitInverseNumerator : Matrix (Fin 6) (Fin 6) ℤ := ![
  ![120, -80, -36, -48, -48, 96], ![-12, -4, 0, 12, 0, 0],
  ![12, -20, -12, -12, 0, 24], ![-288, 200, 90, 120, 120, -240],
  ![24, 16, 0, -24, 0, 0], ![-24, 40, 30, 24, 0, -48]]

theorem threeBitJacobian_mul_inverseNumerator :
    threeBitJacobian * threeBitInverseNumerator = (24 : ℤ) • 1 := by
  decide +kernel

theorem threeBitJacobian_det_ne_zero : threeBitJacobian.det ≠ 0 := by
  intro hz
  have heq := congrArg Matrix.det threeBitJacobian_mul_inverseNumerator
  rw [Matrix.det_mul, hz, zero_mul, Matrix.det_smul, Matrix.det_one] at heq
  norm_num at heq

theorem positive_factor_exchange_identity (t x : ℝ) :
    (1 + 2 * t - x / 3) * (1 + 3 * t + x / 2) =
      (1 + 2 * t) * (1 + 3 * t) + (x - x^2) / 6 := by
  ring

theorem positive_factor_exchange_boolean (t x : ℝ) (hx : x^2 = x) :
    (1 + 2 * t - x / 3) * (1 + 3 * t + x / 2) =
      (1 + 2 * t) * (1 + 3 * t) := by
  rw [positive_factor_exchange_identity, hx]
  ring

noncomputable def firstSlopes {I : Type*} [DecidableEq I] (choice : Option I) (i : I) : ℝ :=
  if some i = choice then 5 / 3 else 2

noncomputable def secondSlopes {I : Type*} [DecidableEq I] (choice : Option I) (i : I) : ℝ :=
  if some i = choice then 7 / 2 else 3

theorem exchange_slopes_positive {I : Type*} [DecidableEq I]
    (choice : Option I) (i : I) :
    0 < firstSlopes choice i ∧ 0 < secondSlopes choice i := by
  unfold firstSlopes secondSlopes
  split_ifs <;> norm_num

theorem firstSlopes_injective {I : Type*} [DecidableEq I] :
    Function.Injective (firstSlopes (I := I)) := by
  intro p q heq
  cases p with
  | none =>
    cases q with
    | none => rfl
    | some j =>
      have he := congrFun heq j
      norm_num [firstSlopes] at he
  | some i =>
    cases q with
    | none =>
      have he := congrFun heq i
      norm_num [firstSlopes] at he
    | some j =>
      by_cases hij : i = j
      · subst j; rfl
      have he := congrFun heq i
      norm_num [firstSlopes, hij] at he

#print axioms normalized_classification
#print axioms nonzero_constant_needed
#print axioms threeBitJacobian_det_ne_zero
#print axioms positive_factor_exchange_boolean
#print axioms firstSlopes_injective

end HeadComplexity.BooleanZeroProduct
