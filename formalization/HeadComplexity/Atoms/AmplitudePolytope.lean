import HeadComplexity.Atoms.HeadEllipticEnergy

set_option linter.style.header false
set_option linter.style.whitespace false

/-! Algebraic ingredients for the bounded-head numerator polytope and
its harmonic vertex branches. The analytic maximum principle and the
table-image theorem are written proofs. No head-count claim is made. -/

namespace HeadComplexity.AmplitudePolytope

open scoped BigOperators

theorem clip_decomposition (a b : ℝ) (hb : 0 ≤ b) :
    a = min b (max (-b) a) + max (a-b) 0 - max (-a-b) 0 ∧
      |min b (max (-b) a)| ≤ b := by
  by_cases hhigh : b ≤ a
  · have hlow : -b ≤ a := by linarith
    simp only [max_eq_right hlow, min_eq_left hhigh,
      max_eq_left (sub_nonneg.mpr hhigh),
      max_eq_right (show -a-b ≤ 0 by linarith), sub_zero]
    exact ⟨by ring, by simpa [abs_of_nonneg hb]⟩
  · by_cases hlow : a ≤ -b
    · simp only [max_eq_left hlow,
        min_eq_right (show -b ≤ b by linarith),
        max_eq_right (show a-b ≤ 0 by linarith),
        max_eq_left (show 0 ≤ -a-b by linarith), add_zero]
      exact ⟨by ring, by simpa [abs_of_nonneg hb]⟩
    · have ha : -b ≤ a := le_of_lt (lt_of_not_ge hlow)
      have hab : a ≤ b := le_of_lt (lt_of_not_ge hhigh)
      simp only [max_eq_right ha, min_eq_right hab,
        max_eq_right (show a-b ≤ 0 by linarith),
        max_eq_right (show -a-b ≤ 0 by linarith), add_zero, sub_zero]
      exact ⟨trivial, abs_le.mpr ⟨ha,hab⟩⟩

theorem budget_weights {I : Type*} [Fintype I] (p m : I → ℝ) (a₀ : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hm : ∀ i, 0 ≤ m i)
    (hpSum : ∑ i, p i ≤ 1-a₀) (hmSum : ∑ i, m i ≤ 1+a₀) :
    0 ≤ (1+a₀-∑ i, m i)/2 ∧
    0 ≤ (1-a₀-∑ i, p i)/2 ∧
    (∀ i, 0 ≤ m i/2 ∧ 0 ≤ p i/2) ∧
    ((1+a₀-∑ i, m i)/2 + (1-a₀-∑ i, p i)/2 +
      ∑ i, (m i/2+p i/2)) = 1 ∧
    ((1+a₀-∑ i, m i)/2 - (1-a₀-∑ i, p i)/2 +
      ∑ i, (m i/2-p i/2)) = a₀ ∧
    (∀ i, 2*(p i/2)-2*(m i/2) = p i-m i) := by
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨div_nonneg (hm i) (by norm_num), div_nonneg (hp i) (by norm_num)⟩
  · rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
    ring
  · rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
    ring
  · intro i
    ring

theorem vertex_branch_amplitude {I : Type*} [Fintype I]
    (b x s : I → ℝ) (k : ℝ)
    (hb : ∀ i, 0 ≤ b i) (hx : ∀ i, 0 ≤ x i)
    (hs : ∀ i, |s i| ≤ 1) (hk : |k| ≤ 1) :
    |k+∑ i, s i*b i*x i| ≤ 1+∑ i, b i*x i := by
  calc
    _ ≤ |k|+|∑ i, s i*b i*x i| := abs_add_le _ _
    _ ≤ 1+∑ i, |s i*b i*x i| := add_le_add hk (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ _ := by
      apply add_le_add (le_refl _)
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_mul, abs_of_nonneg (hb i), abs_of_nonneg (hx i)]
      have := mul_le_mul_of_nonneg_right (hs i) (mul_nonneg (hb i) (hx i))
      nlinarith

/-- The extra product-rule terms for a choice probability cancel exactly. -/
theorem choice_product_cancellation (b r x : ℝ)
    (hx : x^2 = x) (hD : 1+r ≠ 0) :
    -2*x*(b*x+b*r)/(1+r)^2 + 2*b*x/(1+r) = 0 := by
  field_simp
  nlinarith [congrArg (fun t : ℝ ↦ 2*b*t) hx]

theorem metric_positive {I : Type*} [Fintype I] (b z : I → ℝ)
    (hb : ∀ i, 0 < b i) (hz : ∃ i, z i ≠ 0) :
    0 < HeadEllipticEnergy.energy b z := by
  obtain ⟨i,hi⟩ := hz
  have hs : 0 < ∑ j, b j*(z j)^2 := by
    apply Finset.sum_pos'
    · intro j hj
      exact mul_nonneg (hb j).le (sq_nonneg _)
    · exact ⟨i,Finset.mem_univ _,mul_pos (hb i) (sq_pos_of_ne_zero hi)⟩
  unfold HeadEllipticEnergy.energy
  exact add_pos_of_pos_of_nonneg hs (sq_nonneg _)

/-- Four harmonic polynomial inequalities can enclose a bounded chamber. -/
theorem harmonic_positive_chamber_bounded (u v : ℝ)
    (h₁ : 0 < 1+(u^2-v^2)) (h₂ : 0 < 1-(u^2-v^2))
    (h₃ : 0 < 1+2*u*v) (h₄ : 0 < 1-2*u*v) :
    (u^2+v^2)^2 < 2 := by
  have hA : (u^2-v^2)^2 < 1 := by nlinarith [mul_pos h₁ h₂]
  have hB : (2*u*v)^2 < 1 := by nlinarith [mul_pos h₃ h₄]
  have he : (u^2+v^2)^2 = (u^2-v^2)^2+(2*u*v)^2 := by ring
  rw [he]
  linarith

end HeadComplexity.AmplitudePolytope
