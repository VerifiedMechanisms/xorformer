import HeadComplexity.Results.JointFamilyScalarCapacity

set_option linter.style.header false

/-!
# Common zeros of compact moving-pole decoders

A scalar-address decoder with H distinct exterior poles and H query points
cannot have independent output rows while vanishing at every query: its
coefficient rows are proportional. This rules out the most direct compact
moving-pole codebook with exactly as many poles as query addresses. It does
not rule out extra poles, colliding-pole limits, or nonscalar addresses.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

private theorem zero_bias_degree {H : ℕ} (pole η : Fin H → ℝ) :
    (jointFamilyCauchyPolynomial Finset.univ pole η 0).natDegree ≤ H - 1 := by
  classical
  simp only [jointFamilyCauchyPolynomial, Polynomial.C_0, zero_mul, zero_add]
  apply (Polynomial.natDegree_sum_le _ _).trans
  apply Finset.sup_le
  intro i hi
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    (∑ j ∈ Finset.univ.erase i,
        (Polynomial.C (pole j) - Polynomial.X : Polynomial ℝ).natDegree) ≤
        ∑ _j ∈ Finset.univ.erase i, 1 := by
      apply Finset.sum_le_sum
      intro j _
      exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
    _ = H - 1 := by simp

/-- With no scalar bias, H distinct reciprocal kernels are independent
when evaluated at at least H distinct queries away from the poles. -/
theorem jointFamily_cauchy_zero_bias_injective {H M : ℕ}
    (pole : Fin H → ℝ) (query : Fin M → ℝ) (η : Fin H → ℝ)
    (hHM : H ≤ M) (hpole : Function.Injective pole)
    (hquery : Function.Injective query)
    (hden : ∀ h i, pole h - query i ≠ 0)
    (hzero : ∀ i, (∑ h, η h / (pole h - query i)) = 0) :
    ∀ h, η h = 0 := by
  classical
  intro h
  have hH : 0 < H := Nat.zero_lt_of_lt h.isLt
  let P := jointFamilyCauchyPolynomial Finset.univ pole η 0
  have hPdegree : P.natDegree < M := by
    have hd := zero_bias_degree pole η
    dsimp [P]
    omega
  have hPeval (i : Fin M) : P.eval (query i) = 0 := by
    rw [jointFamilyCauchyPolynomial_eval Finset.univ pole η 0 (query i)
      (fun h _ ↦ hden h i)]
    simp [hzero]
  have hPzero : P = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hquery hPeval
      (by simpa using hPdegree)
  have hpatpole : P.eval (pole h) =
      η h * ∏ j ∈ Finset.univ.erase h, (pole j - pole h) := by
    simp only [P, jointFamilyCauchyPolynomial, Polynomial.C_0, zero_mul,
      zero_add, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X]
    apply Finset.sum_eq_single h
    · intro j _ hj
      have hhmem : h ∈ Finset.univ.erase j := by simp [Ne.symm hj]
      rw [Finset.prod_eq_zero hhmem (sub_self (pole h)), mul_zero]
    · simp
  have hprod : (∏ j ∈ Finset.univ.erase h, (pole j - pole h)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (hpole.ne (Finset.mem_erase.mp hj).1)
  have he : η h * ∏ j ∈ Finset.univ.erase h, (pole j - pole h) = 0 := by
    rw [← hpatpole, hPzero, Polynomial.eval_zero]
  exact (mul_eq_zero.mp he).resolve_right hprod

/-- If two moving-pole output rows vanish at H query points at a common
configuration of H distinct poles, their fixed residues are proportional
with the same factors as their scalar biases. -/
theorem jointFamily_common_cauchy_zero_cross_multiply {H M : ℕ}
    (pole : Fin H → ℝ) (query : Fin M → ℝ)
    (η ξ : Fin H → ℝ) (c d : ℝ)
    (hHM : H ≤ M) (hpole : Function.Injective pole)
    (hquery : Function.Injective query)
    (hden : ∀ h i, pole h - query i ≠ 0)
    (hη : ∀ i, c + ∑ h, η h / (pole h - query i) = 0)
    (hξ : ∀ i, d + ∑ h, ξ h / (pole h - query i) = 0) :
    ∀ h, d * η h = c * ξ h := by
  have hz (i : Fin M) :
      (∑ h, (d * η h - c * ξ h) / (pole h - query i)) = 0 := by
    simp only [sub_div, mul_div_assoc, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    linear_combination d * hη i - c * hξ i
  have he := jointFamily_cauchy_zero_bias_injective pole query
    (fun h ↦ d * η h - c * ξ h) hHM hpole hquery hden hz
  intro h
  exact sub_eq_zero.mp (he h)

/-- The proportionality is an identity at every new pole configuration,
not merely at the configuration where the rows vanished. -/
theorem jointFamily_common_cauchy_zero_score_proportional {H M : ℕ}
    (pole : Fin H → ℝ) (query : Fin M → ℝ)
    (η ξ : Fin H → ℝ) (c d : ℝ)
    (hHM : H ≤ M) (hpole : Function.Injective pole)
    (hquery : Function.Injective query)
    (hden : ∀ h i, pole h - query i ≠ 0)
    (hη : ∀ i, c + ∑ h, η h / (pole h - query i) = 0)
    (hξ : ∀ i, d + ∑ h, ξ h / (pole h - query i) = 0)
    (newPole : Fin H → ℝ) (u : ℝ) :
    d * (c + ∑ h, η h / (newPole h - u)) =
      c * (d + ∑ h, ξ h / (newPole h - u)) := by
  have he := jointFamily_common_cauchy_zero_cross_multiply pole query η ξ c d
    hHM hpole hquery hden hη hξ
  simp only [mul_add, Finset.mul_sum, ← mul_div_assoc, he]
  ring

/-- Two independent strict output bits cannot be obtained by moving H poles
around a configuration at which both rows vanish on at least H queries.
Already the two words `(+,+)` and `(+,-)` are incompatible. -/
theorem jointFamily_common_cauchy_zero_no_two_words {H M : ℕ}
    (pole : Fin H → ℝ) (query : Fin M → ℝ)
    (η ξ : Fin H → ℝ) (c d : ℝ)
    (hHM : H ≤ M) (hpole : Function.Injective pole)
    (hquery : Function.Injective query)
    (hden : ∀ h i, pole h - query i ≠ 0)
    (hη : ∀ i, c + ∑ h, η h / (pole h - query i) = 0)
    (hξ : ∀ i, d + ∑ h, ξ h / (pole h - query i) = 0)
    (p₁ p₂ : Fin H → ℝ) (u₁ u₂ : ℝ)
    (h₁η : 0 < c + ∑ h, η h / (p₁ h - u₁))
    (h₁ξ : 0 < d + ∑ h, ξ h / (p₁ h - u₁))
    (h₂η : 0 < c + ∑ h, η h / (p₂ h - u₂))
    (h₂ξ : d + ∑ h, ξ h / (p₂ h - u₂) < 0) : False := by
  have hprop₁ := jointFamily_common_cauchy_zero_score_proportional pole query η ξ c d
    hHM hpole hquery hden hη hξ p₁ u₁
  have hprop₂ := jointFamily_common_cauchy_zero_score_proportional pole query η ξ c d
    hHM hpole hquery hden hη hξ p₂ u₂
  have hc : c ≠ 0 := by
    intro hc
    have he := jointFamily_cauchy_zero_bias_injective pole query η
      hHM hpole hquery hden (fun i ↦ by simpa [hc] using hη i)
    simp [hc, he] at h₁η
  rcases lt_or_gt_of_ne hc with hc | hc
  · have hd : d < 0 := by nlinarith
    have hl : d * (c + ∑ h, η h / (p₂ h - u₂)) < 0 :=
      mul_neg_of_neg_of_pos hd h₂η
    have hr : 0 < c * (d + ∑ h, ξ h / (p₂ h - u₂)) :=
      mul_pos_of_neg_of_neg hc h₂ξ
    linarith
  · have hd : 0 < d := by nlinarith
    have hl : 0 < d * (c + ∑ h, η h / (p₂ h - u₂)) :=
      mul_pos hd h₂η
    have hr : c * (d + ∑ h, ξ h / (p₂ h - u₂)) < 0 :=
      mul_neg_of_pos_of_neg hc h₂ξ
    linarith

end HeadComplexity.AxisZeroGluing
