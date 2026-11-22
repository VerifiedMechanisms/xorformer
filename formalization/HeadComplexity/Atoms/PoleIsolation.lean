import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Tactic

set_option linter.style.header false

/-! A finite pole-isolation argument for auxiliary reciprocal-cube jet matrices.
It is independent of, and does not assert, a worst-case head lower bound. -/
namespace HeadComplexity.PoleIsolation

open Finset
open scoped BigOperators

variable {X : Type*}

noncomputable def kernel (a : X → X → ℤ) (E : X → X → ℝ) (ε : ℝ) :
    Matrix X X ℝ := fun x y ↦ ε ^ 3 * E x y / (ε + (a x y : ℝ)) ^ 3

theorem shifted_int_abs (a : ℤ) (ha : a ≠ 0) (ε : ℝ)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) :
    1 / 2 ≤ |ε + (a : ℝ)| := by
  have ha' : (1 : ℝ) ≤ |(a : ℝ)| := by
    have hi : (1 : ℤ) ≤ |a| := by
      have hpos := abs_pos.mpr ha
      omega
    exact_mod_cast hi
  have htri : |(a : ℝ)| ≤ |ε + (a : ℝ)| + ε := by
    calc
      |(a : ℝ)| = |(ε + (a : ℝ)) + (-ε)| := by congr 1; ring
      _ ≤ |ε + (a : ℝ)| + |-ε| := abs_add_le _ _
      _ = _ := by rw [abs_neg, abs_of_nonneg hε]
  linarith

theorem kernel_diag (a : X → X → ℤ) (E : X → X → ℝ)
    (ha : ∀ x, a x x = 0) (hE : ∀ x, E x x = 1)
    (ε : ℝ) (hε : 0 < ε) (x : X) : kernel a E ε x x = 1 := by
  simp [kernel, ha, hE, hε.ne']

theorem kernel_offdiag_bound (a : X → X → ℤ) (E : X → X → ℝ)
    (hE : ∀ x y, |E x y| ≤ 1)
    (hisolate : ∀ x y, x ≠ y → a x y = 0 → E x y = 0)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    (x y : X) (hxy : x ≠ y) : ‖kernel a E ε x y‖ ≤ 8 * ε ^ 3 := by
  by_cases ha : a x y = 0
  · simp [kernel, hisolate x y hxy ha]
    positivity
  · have hden := shifted_int_abs (a x y) ha ε hε.le hε'
    have hdenpos : 0 < |ε + (a x y : ℝ)| := by linarith
    have hcube : (1 : ℝ) / 8 ≤ |ε + (a x y : ℝ)| ^ 3 := by
      nlinarith [sq_nonneg (|ε + (a x y : ℝ)| - 1 / 2),
        mul_nonneg (sub_nonneg.mpr hden)
          (sq_nonneg (|ε + (a x y : ℝ)| - 1 / 2))]
    rw [Real.norm_eq_abs, kernel, abs_div, abs_mul, abs_pow, abs_pow,
      abs_of_pos hε]
    apply (div_le_iff₀ (pow_pos hdenpos 3)).mpr
    calc
      ε ^ 3 * |E x y| ≤ ε ^ 3 := mul_le_of_le_one_right (by positivity) (hE x y)
      _ ≤ 8 * ε ^ 3 * |ε + (a x y : ℝ)| ^ 3 := by
        nlinarith [mul_nonneg (show 0 ≤ ε ^ 3 by positivity)
          (show 0 ≤ |ε + (a x y : ℝ)| ^ 3 - 1 / 8 by linarith)]

/-- A sufficiently small pole perturbation has nonzero determinant. -/
theorem kernel_det_ne_zero (a : X → X → ℤ) (E : X → X → ℝ)
    [Fintype X] [DecidableEq X]
    (ha : ∀ x, a x x = 0) (hdiag : ∀ x, E x x = 1)
    (hE : ∀ x y, |E x y| ≤ 1)
    (hisolate : ∀ x y, x ≠ y → a x y = 0 → E x y = 0)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    (hbudget : (Fintype.card X : ℝ) * (8 * ε ^ 3) < 1) :
    (kernel a E ε).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro x
  rw [kernel_diag a E ha hdiag ε hε x, norm_one]
  calc
    (∑ y ∈ Finset.univ.erase x, ‖kernel a E ε x y‖) ≤
        ∑ y ∈ Finset.univ.erase x, 8 * ε ^ 3 := by
      apply Finset.sum_le_sum
      intro y hy
      exact kernel_offdiag_bound a E hE hisolate ε hε hε' x y
        (Ne.symm (Finset.mem_erase.mp hy).1)
    _ ≤ ∑ _y : X, 8 * ε ^ 3 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.erase_subset _ _
      · intros; positivity
    _ = (Fintype.card X : ℝ) * (8 * ε ^ 3) := by simp
    _ < 1 := hbudget

/-- The explicit perturbation used in the Boolean construction. -/
theorem explicit_kernel_det_ne_zero (a : X → X → ℤ) (E : X → X → ℝ)
    [Fintype X] [DecidableEq X] [Nonempty X]
    (ha : ∀ x, a x x = 0) (hdiag : ∀ x, E x x = 1)
    (hE : ∀ x y, |E x y| ≤ 1)
    (hisolate : ∀ x y, x ≠ y → a x y = 0 → E x y = 0) :
    (kernel a E (1 / (4 * Fintype.card X))).det ≠ 0 := by
  have hN : (1 : ℝ) ≤ Fintype.card X := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty X)
  have hNpos : (0 : ℝ) < Fintype.card X := by linarith
  have hden : (0 : ℝ) < 4 * Fintype.card X := by positivity
  apply kernel_det_ne_zero a E ha hdiag hE hisolate
  · positivity
  · apply (div_le_iff₀ hden).mpr
    linarith
  · have hid : (Fintype.card X : ℝ) * (8 * (1 / (4 * Fintype.card X)) ^ 3) =
        1 / (8 * (Fintype.card X : ℝ) ^ 2) := by
      field_simp
      ring
    rw [hid]
    apply (div_lt_one (by positivity)).mpr
    nlinarith [sq_nonneg ((Fintype.card X : ℝ) - 1)]

end HeadComplexity.PoleIsolation
