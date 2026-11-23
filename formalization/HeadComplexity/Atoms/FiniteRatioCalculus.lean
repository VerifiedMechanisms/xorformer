import HeadComplexity.Atoms.CertifiedContraction
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option linter.style.header false

/-!
Finite-dimensional calculus for sums of affine ratios. The norm is the
supremum norm on finite coordinate spaces. All estimates below are uniform
in the coefficient values once the displayed denominator lower bound holds.
-/

namespace HeadComplexity.FiniteRatioCalculus

open scoped BigOperators
open ContinuousLinearMap

variable {p m h : ℕ}

noncomputable def rowForm (a : Fin p → ℝ) : (Fin p → ℝ) →L[ℝ] ℝ :=
  ∑ i, a i • ContinuousLinearMap.proj i

theorem rowForm_apply (a z : Fin p → ℝ) : rowForm a z = ∑ i, a i * z i := by
  simp [rowForm]

theorem rowForm_bound (a z : Fin p → ℝ) :
    ‖rowForm a z‖ ≤ (∑ i, |a i|) * ‖z‖ := by
  rw [rowForm_apply, Real.norm_eq_abs]
  calc
    |∑ i, a i * z i| ≤ ∑ i, |a i * z i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| * ‖z‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm z i) (abs_nonneg _)
    _ = (∑ i, |a i|) * ‖z‖ := (Finset.sum_mul ..).symm

theorem rowForm_norm (a : Fin p → ℝ) : ‖rowForm a‖ ≤ ∑ i, |a i| := by
  exact opNorm_le_bound _ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (rowForm_bound a)

noncomputable def matrixMap (A : Fin m → Fin p → ℝ) :
    (Fin p → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi fun r ↦ rowForm (A r)

theorem matrixMap_apply (A : Fin m → Fin p → ℝ) (z : Fin p → ℝ) (r : Fin m) :
    matrixMap A z r = ∑ i, A r i * z i := by
  simp [matrixMap, rowForm_apply]

theorem matrixMap_norm (A : Fin m → Fin p → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hA : ∀ r, ∑ i, |A r i| ≤ M) : ‖matrixMap A‖ ≤ M := by
  apply opNorm_le_bound _ hM
  intro z
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM (norm_nonneg _))).2
  intro r
  exact (rowForm_bound (A r) z).trans (mul_le_mul_of_nonneg_right (hA r) (norm_nonneg _))

noncomputable def ratioSum (a b : Fin h → Fin p → ℝ) (c : Fin h → ℝ)
    (z : Fin p → ℝ) : ℝ :=
  ∑ j, rowForm (a j) z / (c j + rowForm (b j) z)

noncomputable def ratioDerivative (a b : Fin h → Fin p → ℝ) (c : Fin h → ℝ)
    (z : Fin p → ℝ) : (Fin p → ℝ) →L[ℝ] ℝ :=
  ∑ j, ((c j + rowForm (b j) z)⁻¹ • rowForm (a j) -
    (rowForm (a j) z / (c j + rowForm (b j) z)^2) • rowForm (b j))

theorem hasFDerivAt_ratioSum (a b : Fin h → Fin p → ℝ) (c : Fin h → ℝ)
    (z : Fin p → ℝ) (hb : ∀ j, c j + rowForm (b j) z ≠ 0) :
    HasFDerivAt (ratioSum a b c) (ratioDerivative a b c z) z := by
  unfold ratioSum ratioDerivative
  apply HasFDerivAt.fun_sum
  intro j _
  have hi := (hasDerivAt_inv (hb j)).comp_hasFDerivAt z
    ((rowForm (b j)).hasFDerivAt.const_add (c j))
  have hd := (rowForm (a j)).hasFDerivAt.mul hi
  convert hd using 1
  · ext w
    simp [div_eq_mul_inv, Function.comp_def]
  · ext w
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, Function.comp_apply]
    ring

theorem ratioDerivative_apply (a b : Fin h → Fin p → ℝ) (c : Fin h → ℝ)
    (z w : Fin p → ℝ) :
    ratioDerivative a b c z w = ∑ j,
      (rowForm (a j) w / (c j + rowForm (b j) z) -
      rowForm (a j) z * rowForm (b j) w / (c j + rowForm (b j) z)^2) := by
  simp only [ratioDerivative, sum_apply, sub_apply, smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem reciprocal_difference_bound {B C β δ : ℝ}
    (hβ : 0 < β) (hB : β ≤ B) (hC : β ≤ C) (hδ : |B - C| ≤ δ) :
    |B⁻¹ - C⁻¹| ≤ δ / β^2 := by
  have hBp : 0 < B := hβ.trans_le hB
  have hCp : 0 < C := hβ.trans_le hC
  have hprod : β^2 ≤ B * C := by nlinarith
  rw [inv_sub_inv hBp.ne' hCp.ne', abs_div, abs_of_pos (mul_pos hBp hCp), abs_sub_comm]
  exact (div_le_div_of_nonneg_right hδ (mul_pos hBp hCp).le).trans
    (div_le_div_of_nonneg_left (le_trans (abs_nonneg _) hδ) (sq_pos_of_pos hβ) hprod)

theorem reciprocal_square_difference_bound {B C β δ : ℝ}
    (hβ : 0 < β) (hB : β ≤ B) (hC : β ≤ C) (hδ : |B - C| ≤ δ) :
    |(B^2)⁻¹ - (C^2)⁻¹| ≤ 2 * δ / β^3 := by
  have hBp : 0 < B := hβ.trans_le hB
  have hCp : 0 < C := hβ.trans_le hC
  have hδp : 0 ≤ δ := (abs_nonneg _).trans hδ
  have h1 := reciprocal_difference_bound hβ hB hC hδ
  have h2 : |B⁻¹ + C⁻¹| ≤ 2 / β := by
    rw [abs_of_pos (add_pos (inv_pos.mpr hBp) (inv_pos.mpr hCp))]
    have hb := (one_div_le_one_div_of_le hβ hB)
    have hc := (one_div_le_one_div_of_le hβ hC)
    simp only [one_div] at hb hc
    simp only [div_eq_mul_inv]
    linarith
  have heq : (B^2)⁻¹ - (C^2)⁻¹ = (B⁻¹ - C⁻¹) * (B⁻¹ + C⁻¹) := by
    simp only [← inv_pow]
    ring
  rw [heq, abs_mul]
  calc
    |B⁻¹ - C⁻¹| * |B⁻¹ + C⁻¹| ≤ (δ / β^2) * (2 / β) :=
      mul_le_mul h1 h2 (abs_nonneg _) (div_nonneg hδp (sq_nonneg _))
    _ = 2 * δ / β^3 := by ring

theorem ratio_difference_bound {A A' B C β U δA δB : ℝ}
    (hβ : 0 < β) (hB : β ≤ B) (hC : β ≤ C)
    (hU : |A'| ≤ U) (hA : |A - A'| ≤ δA) (hD : |B - C| ≤ δB) :
    |A / B - A' / C| ≤ δA / β + U * δB / β^2 := by
  have hBp : 0 < B := hβ.trans_le hB
  have hAp : 0 ≤ δA := (abs_nonneg _).trans hA
  have hDp : 0 ≤ δB := (abs_nonneg _).trans hD
  have hUp : 0 ≤ U := (abs_nonneg _).trans hU
  have hI := reciprocal_difference_bound hβ hB hC hD
  have heq : A / B - A' / C = (A - A') / B + A' * (B⁻¹ - C⁻¹) := by ring
  rw [heq]
  calc
    |(A - A') / B + A' * (B⁻¹ - C⁻¹)| ≤
        |(A - A') / B| + |A' * (B⁻¹ - C⁻¹)| := abs_add_le _ _
    _ ≤ δA / β + U * (δB / β^2) := by
      apply add_le_add
      · rw [abs_div, abs_of_pos hBp]
        exact (div_le_div_of_nonneg_right hA hBp.le).trans
          (div_le_div_of_nonneg_left hAp hβ hB)
      · rw [abs_mul]
        exact mul_le_mul hU hI (abs_nonneg _) hUp
    _ = δA / β + U * δB / β^2 := by ring

theorem ratio_square_difference_bound {A A' B C β U δA δB : ℝ}
    (hβ : 0 < β) (hB : β ≤ B) (hC : β ≤ C)
    (hU : |A'| ≤ U) (hA : |A - A'| ≤ δA) (hD : |B - C| ≤ δB) :
    |A / B^2 - A' / C^2| ≤ δA / β^2 + 2 * U * δB / β^3 := by
  have hBp : 0 < B := hβ.trans_le hB
  have hAp : 0 ≤ δA := (abs_nonneg _).trans hA
  have hUp : 0 ≤ U := (abs_nonneg _).trans hU
  have hsq : β^2 ≤ B^2 := by nlinarith
  have hI := reciprocal_square_difference_bound hβ hB hC hD
  have heq : A / B^2 - A' / C^2 =
      (A - A') / B^2 + A' * ((B^2)⁻¹ - (C^2)⁻¹) := by ring
  rw [heq]
  calc
    |(A - A') / B^2 + A' * ((B^2)⁻¹ - (C^2)⁻¹)| ≤
        |(A - A') / B^2| + |A' * ((B^2)⁻¹ - (C^2)⁻¹)| := abs_add_le _ _
    _ ≤ δA / β^2 + U * (2 * δB / β^3) := by
      apply add_le_add
      · rw [abs_div, abs_of_nonneg (sq_nonneg B)]
        exact (div_le_div_of_nonneg_right hA (sq_nonneg B)).trans
          (div_le_div_of_nonneg_left hAp (sq_pos_of_pos hβ) hsq)
      · rw [abs_mul]
        exact mul_le_mul hU hI (abs_nonneg _) hUp
    _ = δA / β^2 + 2 * U * δB / β^3 := by ring

#print axioms matrixMap_norm
#print axioms hasFDerivAt_ratioSum
#print axioms ratio_square_difference_bound

end HeadComplexity.FiniteRatioCalculus
