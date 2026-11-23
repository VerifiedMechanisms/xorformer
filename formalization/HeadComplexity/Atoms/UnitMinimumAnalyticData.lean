import HeadComplexity.Atoms.UnitMinimumCenter
import HeadComplexity.Atoms.UnitMinimumCenterJacobian
import HeadComplexity.Atoms.FiniteRatioCalculus
import HeadComplexity.Atoms.ApproximateInverse

set_option linter.style.header false

namespace HeadComplexity.UnitMinimumAnalytic

open scoped BigOperators
open ContinuousLinearMap
open IntegerBinaryFiber (bit dot)
open UnitMinimumCenter (scale u b indices labels num den gamma columnHead columnInput)
open FiniteRatioCalculus

abbrev Space := Fin 108 → ℝ

def numeratorIndex (i : Fin 18) (h : Fin 3) : Fin 108 :=
  ⟨3 * i.val + h.val, by have := i.isLt; have := h.isLt; omega⟩

def denominatorIndex (i : Fin 18) (h : Fin 3) : Fin 108 :=
  ⟨54 + 3 * i.val + h.val, by have := i.isLt; have := h.isLt; omega⟩

theorem numeratorIndex_lt (i : Fin 18) (h : Fin 3) : (numeratorIndex i h).val < 54 := by
  have := i.isLt
  have := h.isLt
  simp only [numeratorIndex]
  omega

theorem denominatorIndex_ge (i : Fin 18) (h : Fin 3) : 54 ≤ (denominatorIndex i h).val := by
  simp only [denominatorIndex]
  omega

theorem index_columns (i : Fin 18) (h : Fin 3) :
    columnHead (numeratorIndex i h) = h ∧ columnInput (numeratorIndex i h) = i ∧
    columnHead (denominatorIndex i h) = h ∧ columnInput (denominatorIndex i h) = i := by
  have := i.isLt
  have := h.isLt
  simp only [Fin.ext_iff, columnHead, columnInput, numeratorIndex, denominatorIndex]
  omega

noncomputable def center : Space := fun c ↦
  if c.val < 54 then (u (columnHead c) (columnInput c) : ℝ) / scale
  else (b (columnHead c) (columnInput c) : ℝ) / scale

theorem center_numerator (i : Fin 18) (h : Fin 3) :
    center (numeratorIndex i h) = (u h i : ℝ) / scale := by
  simp only [center, ite_eq_left (numeratorIndex_lt i h), (index_columns i h).1,
    (index_columns i h).2.1]

theorem center_denominator (i : Fin 18) (h : Fin 3) :
    center (denominatorIndex i h) = (b h i : ℝ) / scale := by
  simp only [center, ite_eq_right (not_lt.mpr (denominatorIndex_ge i h)),
    (index_columns i h).2.2.1, (index_columns i h).2.2.2]

noncomputable def numeratorForm (h : Fin 3) (v : ℕ) : Space →L[ℝ] ℝ :=
  ∑ i : Fin 18, (bit v i.val : ℝ) • ContinuousLinearMap.proj (numeratorIndex i h)

noncomputable def denominatorForm (h : Fin 3) (v : ℕ) : Space →L[ℝ] ℝ :=
  ∑ i : Fin 18, (bit v i.val : ℝ) • ContinuousLinearMap.proj (denominatorIndex i h)

noncomputable def A (h : Fin 3) (v : ℕ) (z : Space) : ℝ := numeratorForm h v z

noncomputable def B (h : Fin 3) (v : ℕ) (z : Space) : ℝ := 1 + denominatorForm h v z

noncomputable def T (v : ℕ) (z : Space) : ℝ := ∑ h : Fin 3, A h v z / B h v z

theorem numeratorForm_apply (h : Fin 3) (v : ℕ) (z : Space) :
    numeratorForm h v z = ∑ i : Fin 18, (bit v i.val : ℝ) * z (numeratorIndex i h) := by
  simp [numeratorForm]

theorem denominatorForm_apply (h : Fin 3) (v : ℕ) (z : Space) :
    denominatorForm h v z = ∑ i : Fin 18, (bit v i.val : ℝ) * z (denominatorIndex i h) := by
  simp [denominatorForm]

theorem A_center (h : Fin 3) (v : ℕ) : A h v center = (num h v : ℝ) / scale := by
  simp only [A, numeratorForm_apply, center_numerator, num, dot]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem B_center (h : Fin 3) (v : ℕ) : B h v center = (den h v : ℝ) / scale := by
  have hs : (scale : ℝ) ≠ 0 := by norm_num [scale]
  simp only [B, denominatorForm_apply, center_denominator, den, dot]
  push_cast
  rw [add_div, div_self hs, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem T_center (v : ℕ) : T v center = (UnitMinimumCenter.score v : ℝ) := by
  have hs : (scale : ℝ) ≠ 0 := by norm_num [scale]
  simp only [T, A_center, B_center, UnitMinimumCenter.score]
  push_cast
  apply Finset.sum_congr rfl
  intro h _
  rw [div_div_div_cancel_right₀ hs]

theorem bit_abs_le_one (v i : ℕ) : |(bit v i : ℝ)| ≤ 1 := by
  have hlo : (0 : ℤ) ≤ bit v i := by unfold bit; positivity
  have hhi := UnitMinimumCenter.bit_le_one v i
  rw [abs_of_nonneg (by exact_mod_cast hlo)]
  exact_mod_cast hhi

theorem numeratorForm_norm (h : Fin 3) (v : ℕ) : ‖numeratorForm h v‖ ≤ 18 := by
  apply opNorm_le_bound _ (by norm_num)
  intro z
  rw [numeratorForm_apply, Real.norm_eq_abs]
  calc
    |∑ i : Fin 18, (bit v i.val : ℝ) * z (numeratorIndex i h)| ≤
        ∑ i : Fin 18, |(bit v i.val : ℝ) * z (numeratorIndex i h)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin 18, ‖z‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact (mul_le_mul (bit_abs_le_one v i.val)
        (by simpa using norm_le_pi_norm z (numeratorIndex i h)) (abs_nonneg _) zero_le_one).trans_eq
        (one_mul _)
    _ = 18 * ‖z‖ := by simp

theorem denominatorForm_norm (h : Fin 3) (v : ℕ) : ‖denominatorForm h v‖ ≤ 18 := by
  apply opNorm_le_bound _ (by norm_num)
  intro z
  rw [denominatorForm_apply, Real.norm_eq_abs]
  calc
    |∑ i : Fin 18, (bit v i.val : ℝ) * z (denominatorIndex i h)| ≤
        ∑ i : Fin 18, |(bit v i.val : ℝ) * z (denominatorIndex i h)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin 18, ‖z‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact (mul_le_mul (bit_abs_le_one v i.val)
        (by simpa using norm_le_pi_norm z (denominatorIndex i h)) (abs_nonneg _) zero_le_one).trans_eq
        (one_mul _)
    _ = 18 * ‖z‖ := by simp

noncomputable def scoreDerivative (v : ℕ) (z : Space) : Space →L[ℝ] ℝ :=
  ∑ h : Fin 3, ((B h v z)⁻¹ • numeratorForm h v -
    (A h v z / (B h v z)^2) • denominatorForm h v)

theorem hasFDerivAt_T (v : ℕ) (z : Space) (hb : ∀ h, B h v z ≠ 0) :
    HasFDerivAt (T v) (scoreDerivative v z) z := by
  unfold T scoreDerivative
  apply HasFDerivAt.fun_sum
  intro h _
  have hi := (hasDerivAt_inv (hb h)).comp_hasFDerivAt z
    ((denominatorForm h v).hasFDerivAt.const_add 1)
  have hd := (numeratorForm h v).hasFDerivAt.mul hi
  convert hd using 1
  · ext w
    simp [A, B, div_eq_mul_inv, Function.comp_def]
  · ext w
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, Function.comp_apply, A, B]
    ring

#print axioms T_center
#print axioms hasFDerivAt_T

end HeadComplexity.UnitMinimumAnalytic
