import HeadComplexity.Polynomial.PureCubicOrientedBase

set_option linter.style.header false

/-! # Exact admissibility of the five rationally perturbed denominators -/

namespace HeadComplexity.PureCubicFiveDenominators

noncomputable section
open RoPETwoHead PureRoPEReplication PureRoPEReplicationStrict PureCubicOrientedBase

def weight₀ : Fin 5 → ℝ := ![0, 1, 2, 0, 1]
def weight₂ : Fin 5 → ℝ := ![0, 0, 0, 1, 1]

theorem weight_bounds (h : Fin 5) :
    0 ≤ weight₀ h ∧ weight₀ h ≤ 2 ∧ 0 ≤ weight₂ h ∧ weight₂ h ≤ 1 := by
  fin_cases h <;> norm_num [weight₀, weight₂]

def denominator {m : ℕ} (t : ℝ) (h : Fin 5) : Form (14 * m) :=
  baseForm.lin ((denominatorForm 0).lin (denominatorForm 2) (weight₀ h) (weight₂ h)) 1 t

theorem denominator_positive {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 ≤ t)
    (h : Fin 5) (x : Fin (14 * m) → Bool) : 0 < (denominator t h).eval x := by
  have hw := weight_bounds h
  have hp := baseForm_gt_eight hm x
  have h0 := PureRoPEReplication.denominator_positive hm x 0
  have h2 := PureRoPEReplication.denominator_positive hm x 2
  simp only [denominator, Form.lin_eval, one_mul, denominatorForm_eval]
  exact add_pos_of_pos_of_nonneg (lt_trans (by norm_num) hp)
    (mul_nonneg ht (add_nonneg (mul_nonneg hw.1 h0.le) (mul_nonneg hw.2.2.1 h2.le)))

theorem perturbation_margin (i : Fin 14) :
    baseSlope i + (1 / 65536 : ℝ) * (2 * |baseB 0 i| + |baseB 2 i|) < 0 := by
  fin_cases i <;> norm_num [baseSlope, baseB]

theorem perturbed_baseSlope {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 65536)
    (h : Fin 5) (i : Fin 14) :
    baseSlope i + t * (weight₀ h * baseB 0 i + weight₂ h * baseB 2 i) < 0 := by
  have hw := weight_bounds h
  have h0 : weight₀ h * baseB 0 i ≤ 2 * |baseB 0 i| :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hw.1).trans
      (mul_le_mul_of_nonneg_right hw.2.1 (abs_nonneg _))
  have h2 : weight₂ h * baseB 2 i ≤ |baseB 2 i| := by
    simpa using (mul_le_mul_of_nonneg_left (le_abs_self _) hw.2.2.1).trans
      (mul_le_mul_of_nonneg_right hw.2.2.2 (abs_nonneg _))
  have hh := mul_le_mul_of_nonneg_left (add_le_add h0 h2) ht
  have hh' := mul_le_mul_of_nonneg_right ht'
    (show 0 ≤ 2 * |baseB 0 i| + |baseB 2 i| by positivity)
  exact lt_of_le_of_lt (add_le_add le_rfl (hh.trans hh')) (perturbation_margin i)

theorem denominator_slopes {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 ≤ t)
    (ht' : t ≤ 1 / 65536) (h : Fin 5) (j : Fin (14 * m)) :
    (denominator t h).v j < 0 := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  let i := ((finProdFinEquiv (m := 14) (n := m)).symm j).1
  have he : (denominator t h).v j =
      2 * (baseSlope i + t * (weight₀ h * baseB 0 i + weight₂ h * baseB 2 i)) / m := by
    simp only [denominator, baseForm, Form.lin, denominatorForm, centeredForm,
      replicate, baseSlope, i]
    ring
  rw [he]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (by norm_num) (perturbed_baseSlope ht ht' h i)) hm'

def step (m : ℕ) : ℝ := epsilon m / 2 ^ 40

theorem step_positive {m : ℕ} (hm : 0 < m) : 0 < step m := by
  exact div_pos (epsilon_positive hm) (by norm_num)

theorem step_le {m : ℕ} (hm : 0 < m) : step m ≤ 1 / 65536 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : (1 : ℝ) ≤ (m : ℝ) ^ 3 := one_le_pow₀ hm'
  have hs : 1 ≤ scale m := by
    unfold scale W
    push_cast
    nlinarith
  have he : epsilon m ≤ 1 / 16 := by
    unfold epsilon
    apply (div_le_iff₀ (by positivity : 0 < 16 * scale m)).mpr
    nlinarith
  unfold step
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 40)).mpr
  linarith

/-- Every affine numerator is allowed over each of these exact rational
denominators. This is an architectural admissibility statement, independent
of the subsequent finite-difference sign estimate. -/
theorem fraction_admissible {m : ℕ} (hm : 0 < m) (N : Form (14 * m)) (h : Fin 5) :
    (fraction N (denominator (step m) h)).Admissible := by
  apply RoPETwoHead.fraction_admissible
  · exact denominator_positive hm (step_positive hm).le h
  · exact Or.inr (denominator_slopes hm (step_positive hm).le (step_le hm) h)

end
end HeadComplexity.PureCubicFiveDenominators
