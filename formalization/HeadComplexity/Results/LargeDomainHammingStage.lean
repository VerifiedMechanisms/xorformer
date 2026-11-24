import HeadComplexity.Results.LargeDomainProducts

set_option linter.style.header false

namespace HeadComplexity.LargeDomain

open scoped BigOperators

/-- Below the queried stage both rails are present. At and above the stage
there is one rail, encoding `z`. -/
def hammingStageRails {d : ℕ} (k : Fin d) (z : Fin d → Bool)
    (i : Fin d) (b : Bool) : ℝ :=
  if i.val < k.val then 1 else if b = z i then 1 else 0

/-- A thermometer stage encoding also balances the Hamming weight. -/
def hammingStageThermometer {d : ℕ} (k : Fin d) (i : Fin d) : ℝ :=
  if i.val < k.val then 0 else 1

/-- This version uses only an affine thermometer correction, with no
stage one-hot coordinate and no product of input coordinates. -/
def hammingStageThermometerNumerator {d : ℕ} (e : Fin d → ℝ)
    (h : Fin d → Bool) (x : Fin d → Bool → ℝ) (u : Fin d → ℝ) : ℝ :=
  (∑ i : Fin d, e i * x i (!(h i))) - (∑ i : Fin d, e i) +
    ∑ i : Fin d, e i * u i

/-- A strictly reverse affine denominator when all `γ`, `κ`, and `t` are
positive. Its full-cube floor is `ε₀ - ∑ t`, independently of their scale. -/
def hammingStageDenominator {d s : ℕ} (ε₀ κ : ℝ)
    (γ : Fin d → ℝ) (t : Fin s → ℝ) (h : Fin d → Bool)
    (x : Fin d → Bool → ℝ) (y : Fin s → ℝ) : ℝ :=
  ε₀ + (∑ i : Fin d,
    (γ i * (1 - x i (h i)) + κ * ((1 - x i false) + (1 - x i true)))) -
      ∑ j : Fin s, t j * y j

/-- The coefficients `e` may depend on the head. The stage correction is
implemented by an affine coefficient on a stage one-hot coordinate. -/
def hammingStageNumerator {d : ℕ} (e : Fin d → ℝ) (h : Fin d → Bool)
    (x : Fin d → Bool → ℝ) (stage : Fin d → ℝ) : ℝ :=
  (∑ i : Fin d, e i * x i (!(h i))) -
    ∑ k : Fin d, stage k * ∑ i : Fin d, if i.val < k.val then e i else 0

lemma hammingStageDenominator_positive {d s : ℕ} {ε₀ κ : ℝ}
    {γ : Fin d → ℝ} {t : Fin s → ℝ} (h : Fin d → Bool)
    (x : Fin d → Bool → ℝ) (y : Fin s → ℝ)
    (hκ : 0 ≤ κ) (hγ : ∀ i, 0 ≤ γ i) (ht : ∀ j, 0 ≤ t j)
    (hx : ∀ i b, x i b ≤ 1) (hy : ∀ j, y j ≤ 1)
    (hfloor : ∑ j : Fin s, t j < ε₀) :
    0 < hammingStageDenominator ε₀ κ γ t h x y := by
  have hs : 0 ≤ ∑ i : Fin d,
      (γ i * (1 - x i (h i)) + κ * ((1 - x i false) + (1 - x i true))) := by
    apply Finset.sum_nonneg
    intro i _
    apply add_nonneg
    · exact mul_nonneg (hγ i) (sub_nonneg.mpr (hx i (h i)))
    · exact mul_nonneg hκ (add_nonneg
        (sub_nonneg.mpr (hx i false)) (sub_nonneg.mpr (hx i true)))
  have hc : (∑ j : Fin s, t j * y j) ≤ ∑ j : Fin s, t j := by
    apply Finset.sum_le_sum
    intro j _
    nlinarith [ht j, hy j]
  unfold hammingStageDenominator
  linarith

lemma hammingStage_unused_slope_neg {κ : ℝ} (hκ : 0 < κ) : -κ < 0 := by
  linarith

lemma hammingStage_match_slope_neg {κ γ : ℝ} (hκ : 0 < κ) (hγ : 0 ≤ γ) :
    -(γ + κ) < 0 := by linarith

lemma hammingStage_wrong_rail {d : ℕ} (k : Fin d) (z h : Fin d → Bool)
    (i : Fin d) :
    hammingStageRails k z i (!(h i)) =
      if i.val < k.val then 1 else if h i ≠ z i then 1 else 0 := by
  unfold hammingStageRails
  by_cases hi : i.val < k.val
  · simp [hi]
  · simp only [hi, ↓reduceIte]
    cases hh : h i <;> cases hz : z i <;> simp

/-- Exact cancellation of all lower-stage contributions. -/
theorem hammingStage_numerator_eval {d : ℕ} (k : Fin d)
    (z h : Fin d → Bool) (e : Fin d → ℝ) :
    hammingStageNumerator e h (hammingStageRails k z)
      (fun l ↦ if l = k then 1 else 0) =
      ∑ i : Fin d, if i.val < k.val then 0 else if h i ≠ z i then e i else 0 := by
  unfold hammingStageNumerator
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hammingStage_wrong_rail]
  by_cases hi : i.val < k.val <;> by_cases hm : h i = z i <;> simp [hi, hm]

/-- Reverse denominators retain a nonnegative guard on every rail. At a
stage row, lower double rails cancel their baseline exactly. -/
theorem hammingStage_denominator_eval {d s : ℕ} (k : Fin d)
    (z h : Fin d → Bool) (ε₀ κ : ℝ) (γ : Fin d → ℝ)
    (t : Fin s → ℝ) (y : Fin s → ℝ) :
    hammingStageDenominator ε₀ κ γ t h (hammingStageRails k z) y =
      ε₀ + (∑ i : Fin d, if i.val < k.val then 0 else
        ((if h i ≠ z i then γ i else 0) + κ)) - ∑ j : Fin s, t j * y j := by
  unfold hammingStageDenominator
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  unfold hammingStageRails
  by_cases hi : i.val < k.val
  · simp [hi]
  · cases hh : h i <;> cases hz : z i <;> simp [hi]

/-- For a matching higher prefix, the affine numerator selects exactly
those heads whose queried bit mismatches. No product with the stage
coordinate is used in the numerator. -/
theorem hammingStage_numerator_prefix {d : ℕ} (k : Fin d)
    (z h : Fin d → Bool) (e : Fin d → ℝ)
    (hprefix : ∀ i : Fin d, k.val < i.val → h i = z i) :
    hammingStageNumerator e h (hammingStageRails k z)
      (fun l ↦ if l = k then 1 else 0) =
      if h k ≠ z k then e k else 0 := by
  rw [hammingStage_numerator_eval]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hik
    by_cases hi : i.val < k.val
    · simp [hi]
    · have hki : k.val < i.val := by
        have hne : i.val ≠ k.val := fun he ↦ hik (Fin.ext he)
        omega
      simp [hi, hprefix i hki]
  · simp

/-- Source rails and the thermometer occupy one common shell, at every
stage and every address. A separate dual-rail query axis adds exactly `d`
more to this weight. -/
theorem hammingStage_shell_weight {d : ℕ} (k : Fin d) (z : Fin d → Bool) :
    (∑ i : Fin d, (hammingStageRails k z i false + hammingStageRails k z i true +
      hammingStageThermometer k i)) = 2 * (d : ℝ) := by
  have hi (i : Fin d) :
      hammingStageRails k z i false + hammingStageRails k z i true +
        hammingStageThermometer k i = 2 := by
    unfold hammingStageRails hammingStageThermometer
    by_cases h : i.val < k.val
    · norm_num [h]
    · cases hz : z i <;> norm_num [h]
  simp_rw [hi]
  simp [mul_comm]

theorem hammingStage_thermometer_numerator {d : ℕ} (k : Fin d)
    (z h : Fin d → Bool) (e : Fin d → ℝ) :
    hammingStageThermometerNumerator e h (hammingStageRails k z)
      (hammingStageThermometer k) =
      hammingStageNumerator e h (hammingStageRails k z)
        (fun l ↦ if l = k then 1 else 0) := by
  rw [hammingStage_numerator_eval]
  unfold hammingStageThermometerNumerator
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hammingStage_wrong_rail]
  unfold hammingStageThermometer
  by_cases hi : i.val < k.val <;> by_cases hm : h i = z i <;> simp [hi, hm]

end HeadComplexity.LargeDomain
