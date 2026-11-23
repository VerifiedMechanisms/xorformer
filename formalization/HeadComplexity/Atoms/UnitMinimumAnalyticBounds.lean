import HeadComplexity.Atoms.UnitMinimumAnalyticData

set_option linter.style.header false

namespace HeadComplexity.UnitMinimumAnalytic

open scoped BigOperators
open ContinuousLinearMap Metric Set
open UnitMinimumCenter (scale u b den)
open FiniteRatioCalculus

noncomputable def radius : ℝ := 1 / 10^40
noncomputable def beta : ℝ := 1 / 1000
def certBall : Set Space := closedBall center radius

theorem radius_nonneg : 0 ≤ radius := by norm_num [radius]
theorem beta_pos : 0 < beta := by norm_num [beta]

theorem coordinate_close (z : Space) (hz : z ∈ certBall) (i : Fin 108) :
    |z i - center i| ≤ radius := by
  have hh : ‖z - center‖ ≤ radius := by simpa [certBall, mem_closedBall, dist_eq_norm] using hz
  have hb : |z i - center i| ≤ ‖z - center‖ := by
    simpa using norm_le_pi_norm (z - center) i
  exact hb.trans hh

theorem center_numerator_bound (i : Fin 18) (h : Fin 3) :
    |center (numeratorIndex i h)| < 1 / 2 := by
  rw [center_numerator, abs_div, abs_of_pos (by norm_num [scale] : (0 : ℝ) < scale)]
  apply (div_lt_iff₀ (by norm_num [scale] : (0 : ℝ) < scale)).mpr
  have hh : 2 * |(u h i : ℝ)| < scale := by exact_mod_cast UnitMinimumCenter.numerator_bounds h i
  linarith

theorem center_slope_bound (i : Fin 18) (h : Fin 3) :
    center (denominatorIndex i h) < -1 / 1000 := by
  rw [center_denominator]
  apply (div_lt_iff₀ (by norm_num [scale] : (0 : ℝ) < scale)).mpr
  have hh : 1000 * (b h i : ℝ) < -scale := by
    exact_mod_cast (UnitMinimumCenter.slope_bounds h i).2
  linarith

theorem center_denominator_bound (h : Fin 3) (v : ℕ) : 1 / 100 < B h v center := by
  rw [B_center]
  apply (lt_div_iff₀ (by norm_num [scale] : (0 : ℝ) < scale)).mpr
  have hh : (scale : ℝ) < 100 * (den h 262143 : ℝ) := by
    exact_mod_cast UnitMinimumCenter.denominator_endpoint_bounds h
  have hm : (den h 262143 : ℝ) ≤ den h v := by
    exact_mod_cast UnitMinimumCenter.den_ge_endpoint h v
  linarith

theorem numerator_coordinate_bound (z : Space) (hz : z ∈ certBall)
    (i : Fin 18) (h : Fin 3) : |z (numeratorIndex i h)| ≤ 1 := by
  have hc := coordinate_close z hz (numeratorIndex i h)
  have hb := center_numerator_bound i h
  have ht := abs_add_le (z (numeratorIndex i h) - center (numeratorIndex i h))
    (center (numeratorIndex i h))
  rw [sub_add_cancel] at ht
  norm_num [radius] at hc
  linarith

theorem slope_negative (z : Space) (hz : z ∈ certBall) (i : Fin 18) (h : Fin 3) :
    z (denominatorIndex i h) < 0 := by
  have hc := (abs_le.mp (coordinate_close z hz (denominatorIndex i h))).2
  have hb := center_slope_bound i h
  norm_num [radius] at hc
  linarith

theorem A_bound (h : Fin 3) (v : ℕ) (z : Space) (hz : z ∈ certBall) : |A h v z| ≤ 18 := by
  rw [A, numeratorForm_apply]
  calc
    |∑ i : Fin 18, (IntegerBinaryFiber.bit v i.val : ℝ) * z (numeratorIndex i h)| ≤
        ∑ i : Fin 18, |(IntegerBinaryFiber.bit v i.val : ℝ) * z (numeratorIndex i h)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin 18, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact (mul_le_mul (bit_abs_le_one v i.val) (numerator_coordinate_bound z hz i h)
        (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = 18 := by norm_num

theorem A_difference (h : Fin 3) (v : ℕ) (z w : Space) :
    |A h v z - A h v w| ≤ 18 * ‖z - w‖ := by
  rw [A, A, ← map_sub, ← Real.norm_eq_abs]
  exact ((numeratorForm h v).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (numeratorForm_norm h v) (norm_nonneg _))

theorem B_difference (h : Fin 3) (v : ℕ) (z w : Space) :
    |B h v z - B h v w| ≤ 18 * ‖z - w‖ := by
  simp only [B, add_sub_add_left_eq_sub, ← map_sub, ← Real.norm_eq_abs]
  exact ((denominatorForm h v).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (denominatorForm_norm h v) (norm_nonneg _))

theorem B_bound (h : Fin 3) (v : ℕ) (z : Space) (hz : z ∈ certBall) : beta < B h v z := by
  have hc := center_denominator_bound h v
  have hd := (abs_le.mp (B_difference h v z center)).1
  have hn : ‖z - center‖ ≤ radius := by simpa [certBall, mem_closedBall, dist_eq_norm] using hz
  norm_num [radius, beta] at hn ⊢
  linarith

theorem score_difference (v : ℕ) (z w : Space) (hz : z ∈ certBall) (hw : w ∈ certBall) :
    |T v z - T v w| ≤ 10^10 * ‖z - w‖ := by
  have hterm (h : Fin 3) : |A h v z / B h v z - A h v w / B h v w| ≤
      (18 / beta + 18 * 18 / beta^2) * ‖z - w‖ := by
    have hh := ratio_difference_bound beta_pos (B_bound h v z hz).le (B_bound h v w hw).le
      (A_bound h v w hw) (A_difference h v z w) (B_difference h v z w)
    convert hh using 1
    ring
  rw [T, T, ← Finset.sum_sub_distrib]
  calc
    |∑ h : Fin 3, (A h v z / B h v z - A h v w / B h v w)| ≤
        ∑ h : Fin 3, |A h v z / B h v z - A h v w / B h v w| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin 3, (18 / beta + 18 * 18 / beta^2) * ‖z - w‖ :=
      Finset.sum_le_sum fun h _ ↦ hterm h
    _ ≤ 10^10 * ‖z - w‖ := by
      norm_num [beta]
      nlinarith [norm_nonneg (z - w)]

theorem derivative_difference (v : ℕ) (z w : Space) (hz : z ∈ certBall) (hw : w ∈ certBall) :
    ‖scoreDerivative v z - scoreDerivative v w‖ ≤ 10^15 * ‖z - w‖ := by
  have hinv (h : Fin 3) : |(B h v z)⁻¹ - (B h v w)⁻¹| ≤ 10^12 * ‖z - w‖ := by
    have hh := reciprocal_difference_bound beta_pos (B_bound h v z hz).le (B_bound h v w hw).le
      (B_difference h v z w)
    norm_num [beta] at hh
    nlinarith [norm_nonneg (z - w)]
  have hrat (h : Fin 3) : |A h v z / (B h v z)^2 - A h v w / (B h v w)^2| ≤
      10^12 * ‖z - w‖ := by
    have hh := ratio_square_difference_bound beta_pos (B_bound h v z hz).le
      (B_bound h v w hw).le (A_bound h v w hw) (A_difference h v z w) (B_difference h v z w)
    norm_num [beta] at hh
    nlinarith [norm_nonneg (z - w)]
  have hterm (h : Fin 3) :
      ‖((B h v z)⁻¹ • numeratorForm h v - (A h v z / (B h v z)^2) • denominatorForm h v) -
        ((B h v w)⁻¹ • numeratorForm h v - (A h v w / (B h v w)^2) • denominatorForm h v)‖ ≤
      36 * 10^12 * ‖z - w‖ := by
    have heq :
        ((B h v z)⁻¹ • numeratorForm h v - (A h v z / (B h v z)^2) • denominatorForm h v) -
          ((B h v w)⁻¹ • numeratorForm h v - (A h v w / (B h v w)^2) • denominatorForm h v) =
        ((B h v z)⁻¹ - (B h v w)⁻¹) • numeratorForm h v -
          (A h v z / (B h v z)^2 - A h v w / (B h v w)^2) • denominatorForm h v := by
      ext t
      simp only [sub_apply, smul_apply, smul_eq_mul]
      ring
    rw [heq]
    have hh := norm_sub_le
      (((B h v z)⁻¹ - (B h v w)⁻¹) • numeratorForm h v)
      ((A h v z / (B h v z)^2 - A h v w / (B h v w)^2) • denominatorForm h v)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at hh
    have h1 := mul_le_mul (hinv h) (numeratorForm_norm h v)
      (norm_nonneg _) (by positivity : 0 ≤ (10 : ℝ)^12 * ‖z - w‖)
    have h2 := mul_le_mul (hrat h) (denominatorForm_norm h v)
      (norm_nonneg _) (by positivity : 0 ≤ (10 : ℝ)^12 * ‖z - w‖)
    nlinarith
  rw [scoreDerivative, scoreDerivative, ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun h _ ↦ hterm h).trans <| by
    norm_num
    nlinarith [norm_nonneg (z - w)]

#print axioms B_bound
#print axioms score_difference
#print axioms derivative_difference

end HeadComplexity.UnitMinimumAnalytic
