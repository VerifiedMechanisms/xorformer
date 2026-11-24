import HeadComplexity.Research.BooleanProjectionMomentAliasing

set_option linter.style.header false

/-!
Positive commuting diagonal descriptor matrices need not act boundedly in the
norm determined by Boolean inverse vectors. An exact projection ghost is not
stable under multiplication by one coordinate matrix. A positive perturbation
makes the Boolean observations full rank while the operator ratio diverges.
-/
noncomputable section
namespace HeadComplexity.ObservableSpanInstability
open Finset
open scoped BigOperators

def first (ε : ℝ) : Fin 6 → ℝ := ![3 + ε, 2, 1, 1, 3, 2]
def second : Fin 6 → ℝ := ![2, 1, 3, 2, 1, 3]
def residue : Fin 6 → ℝ := ![1, 1, 1, -1, -1, -1]

def observation (ε : ℝ) (x : Fin 3 → Bool) (h : Fin 6) : ℝ :=
  1 / (1 + first ε h * boolToReal (x 0) + second h * boolToReal (x 1) +
    boolToReal (x 2))

def score (ε : ℝ) (x : Fin 3 → Bool) : ℝ :=
  ∑ h, residue h * observation ε x h

def multipliedScore (ε : ℝ) (x : Fin 3 → Bool) : ℝ :=
  ∑ h, residue h * first ε h * observation ε x h

def baseDen (x : Fin 3 → Bool) : ℝ :=
  1 + 3 * boolToReal (x 0) + 2 * boolToReal (x 1) + boolToReal (x 2)

/-- All six poles have positive constant and coordinate coefficients. -/
theorem coefficients_positive (ε : ℝ) (hε : 0 ≤ ε) (h : Fin 6) :
    0 < first ε h ∧ 0 < second h := by
  fin_cases h <;> norm_num [first, second] <;> linarith

theorem baseDen_ge_one (x : Fin 3 → Bool) : 1 ≤ baseDen x := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    norm_num [baseDen, boolToReal, h0, h1, h2]

/-- The unperturbed signed functional annihilates every Boolean inverse vector. -/
theorem score_zero (x : Fin 3 → Bool) : score 0 x = 0 := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    norm_num [score, observation, first, second, residue, Fin.sum_univ_succ,
      boolToReal, h0, h1, h2]

theorem score_eq_difference (ε : ℝ) (x : Fin 3 → Bool) :
    score ε x = 1 / (baseDen x + ε * boolToReal (x 0)) - 1 / baseDen x := by
  have hz := score_zero x
  have hd : 1 + (3 + ε) * boolToReal (x 0) + 2 * boolToReal (x 1) +
      boolToReal (x 2) = baseDen x + ε * boolToReal (x 0) := by
    unfold baseDen
    ring
  simp only [score, observation, first, second, residue, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons,
    Fin.isValue, one_mul, neg_mul, zero_add, add_zero] at hz ⊢
  rw [hd]
  dsimp [baseDen] at *
  linarith

lemma reciprocal_difference_abs_le (a ε : ℝ) (ha : 1 ≤ a) (hε : 0 ≤ ε) :
    |1 / (a + ε) - 1 / a| ≤ ε := by
  have hap : 0 < a := by linarith
  have haep : 0 < a + ε := by linarith
  have he : 1 / (a + ε) - 1 / a = -ε / (a * (a + ε)) := by
    field_simp
    ring
  rw [he, abs_div, abs_neg, abs_of_nonneg hε,
    abs_of_pos (mul_pos hap haep)]
  apply (div_le_iff₀ (mul_pos hap haep)).mpr
  have hd : 1 ≤ a * (a + ε) := by nlinarith
  nlinarith

/-- The perturbation is small on the entire cube. -/
theorem score_abs_le (ε : ℝ) (hε : 0 ≤ ε) (x : Fin 3 → Bool) :
    |score ε x| ≤ ε := by
  rw [score_eq_difference]
  cases h0 : x 0
  · simp [h0, boolToReal, hε]
  · simpa [h0, boolToReal] using
      reciprocal_difference_abs_le (baseDen x) ε (baseDen_ge_one x) hε

/-- Coordinate multiplication detects a direction invisible to all original
Boolean observations. -/
theorem multipliedScore_probe (ε : ℝ) :
    multipliedScore ε ![false, true, false] = ε / 3 - 1 / 12 := by
  norm_num [multipliedScore, observation, first, second, residue,
    Fin.sum_univ_succ, boolToReal]
  ring

theorem multipliedScore_abs_ge (ε : ℝ) (hε : ε ≤ 1 / 8) :
    1 / 24 ≤ |multipliedScore ε ![false, true, false]| := by
  rw [multipliedScore_probe]
  have hn : ε / 3 - 1 / 12 < 0 := by linarith
  rw [abs_of_neg hn]
  linarith

/-- No bound for coordinate multiplication can depend only on the size of all
Boolean observations, even at one fixed positive pole configuration. -/
theorem no_bound_at_zero (C : ℝ) :
    ¬ (|multipliedScore 0 ![false, true, false]| ≤
      C * ∑ x : Fin 3 → Bool, |score 0 x|) := by
  simp only [score_zero, abs_zero, Finset.sum_const_zero, mul_zero]
  rw [multipliedScore_probe]
  norm_num

def signedFunctional : (Fin 6 → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ h, residue h * v h
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum, mul_left_comm]

/-- The span of all Boolean inverse vectors is not invariant under the first
positive diagonal coordinate matrix. -/
theorem multipliedVector_not_mem_span :
    (fun h => first 0 h * observation 0 ![false, true, false] h) ∉
      Submodule.span ℝ (Set.range (observation 0)) := by
  have hspan : Submodule.span ℝ (Set.range (observation 0)) ≤
      LinearMap.ker signedFunctional := by
    apply Submodule.span_le.mpr
    rintro v ⟨x, rfl⟩
    change score 0 x = 0
    exact score_zero x
  intro hv
  have hz := hspan hv
  change (∑ h, residue h * (first 0 h *
    observation 0 ![false, true, false] h)) = 0 at hz
  have he : multipliedScore 0 ![false, true, false] = 0 := by
    simpa [multipliedScore, mul_assoc] using hz
  rw [multipliedScore_probe] at he
  norm_num at he

/-- For every positive perturbation the Boolean observations have no nonzero
annihilator. Thus the instability occurs along full-rank configurations. -/
theorem annihilator_eq_zero_of_pos (ε : ℝ) (hε : 0 < ε) (c : Fin 6 → ℝ)
    (h : ∀ x : Fin 3 → Bool, ∑ i, c i * observation ε x i = 0) :
    ∀ i, c i = 0 := by
  have h0 := h ![false, false, false]
  have h2 := h ![false, true, false]
  have h3 := h ![false, true, true]
  have h4 := h ![true, false, false]
  have h5 := h ![true, false, true]
  have h6 := h ![true, true, false]
  norm_num [observation, first, second, Fin.sum_univ_succ, boolToReal] at h0 h2 h3
  norm_num [observation, first, second, Fin.sum_univ_succ, boolToReal] at h4 h5 h6
  let K : ℝ := -11 / 31104000 - (1 / 288000) * (ε + 4)⁻¹ +
    (1 / 129600) * (ε + 5)⁻¹ - (1 / 518400) * (ε + 6)⁻¹
  have hK : K = -ε * (ε + 2) * (11 * ε + 71) /
      (31104000 * (ε + 4) * (ε + 5) * (ε + 6)) := by
    dsimp [K]
    field_simp
    ring
  have hKne : K ≠ 0 := by
    rw [hK]
    apply div_ne_zero
    · exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hε.ne') (by positivity))
        (by positivity)
    · positivity
  have hz : c 0 * K = 0 := by
    dsimp [K]
    linear_combination (-7 / 6220800 : ℝ) * h0 + (-1 / 288000 : ℝ) * h2 +
      (1 / 129600 : ℝ) * h3 + (-1 / 288000 : ℝ) * h4 +
      (1 / 129600 : ℝ) * h5 + (-1 / 518400 : ℝ) * h6
  have hc0 : c 0 = 0 := (mul_eq_zero.mp hz).resolve_right hKne
  rw [hc0] at h0 h2 h3 h4 h5 h6
  norm_num at h0 h2 h3 h4 h5 h6
  intro i
  fin_cases i
  · exact hc0
  · change c 1 = 0
    linarith
  · change c 2 = 0
    linarith
  · change c 3 = 0
    linarith
  · change c 4 = 0
    linarith
  · change c 5 = 0
    linarith

/-- Full-rank positive configurations have arbitrarily bad coordinate-observation
ratios. The coefficient bound does not depend on the desired ratio. -/
theorem arbitrarily_bad_full_rank_ratio (C : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 8 ∧
      (∀ x : Fin 3 → Bool, |score ε x| ≤ ε) ∧
      C * ε < |multipliedScore ε ![false, true, false]| ∧
      (∀ c : Fin 6 → ℝ,
        (∀ x : Fin 3 → Bool, ∑ i, c i * observation ε x i = 0) →
        ∀ i, c i = 0) := by
  let ε : ℝ := 1 / (48 * (|C| + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hden : 0 < 48 * (|C| + 1) := by positivity
  have hsmall : ε ≤ 1 / 8 := by
    dsimp [ε]
    apply (div_le_iff₀ hden).mpr
    nlinarith [abs_nonneg C]
  have hratio : C * ε < 1 / 24 := by
    dsimp [ε]
    rw [mul_one_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith [le_abs_self C, abs_nonneg C]
  exact ⟨ε, hε, hsmall, score_abs_le ε hε.le,
    lt_of_lt_of_le hratio (multipliedScore_abs_ge ε hsmall),
    fun c hc => annihilator_eq_zero_of_pos ε hε c hc⟩

end HeadComplexity.ObservableSpanInstability
