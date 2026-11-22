import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Results.PriorityRestriction

set_option linter.style.header false

/-! The two-ratio construction for the sign of a product of two affine forms.
This provides the head-model side of the priority-list obstruction. -/
namespace HeadComplexity
open scoped BigOperators

noncomputable def affineProductPredicate {n : ℕ} (c₁ c₂ : ℝ)
    (a₁ a₂ : Fin n → ℝ) : (Fin n → Bool) → Bool :=
  fun x ↦ decide (0 < affineValue c₁ a₁ x * affineValue c₂ a₂ x)

theorem computableWithHeadsN_affineProduct {n : ℕ} (c₁ c₂ : ℝ)
    (a₁ a₂ : Fin n → ℝ) :
    computableWithHeadsN n 2 (affineProductPredicate c₁ c₂ a₁ a₂) := by
  classical
  let d₀ : ℝ := 1 + |c₂|
  let d : Fin n → ℝ := fun i ↦ 1 + |a₂ i|
  have hd₀ : 0 < d₀ := by dsimp [d₀]; positivity
  have hd (i : Fin n) : 0 < d i := by dsimp [d]; positivity
  have he₀ : 0 < d₀ + c₂ := by
    have h := neg_abs_le c₂
    dsimp [d₀]
    linarith
  have he (i : Fin n) : 0 < d i + a₂ i := by
    have h := neg_abs_le (a₂ i)
    dsimp [d]
    linarith
  let num₀ : Fin 2 → ℝ := ![c₁, -c₁]
  let num : Fin 2 → Fin n → ℝ := ![a₁, fun i ↦ -a₁ i]
  let den₀ : Fin 2 → ℝ := ![d₀, d₀ + c₂]
  let den : Fin 2 → Fin n → ℝ := ![d, fun i ↦ d i + a₂ i]
  apply computableWithHeadsN_of_positiveAffineRatios num₀ num den₀ den
    (fun h ↦ by fin_cases h <;> simpa [den₀] using (by assumption))
    (fun h i ↦ by
      fin_cases h
      · exact hd i
      · exact he i) 0
  intro x
  have hD := affineValue_pos d₀ d hd₀ hd x
  have hB := affineValue_pos (d₀ + c₂) (fun i ↦ d i + a₂ i) he₀ he x
  have hBeq : affineValue (d₀ + c₂) (fun i ↦ d i + a₂ i) x =
      affineValue d₀ d x + affineValue c₂ a₂ x := affineValue_add _ _ _ _ _
  have hN : affineValue (-c₁) (fun i ↦ -a₁ i) x = -affineValue c₁ a₁ x := by
    simp [affineValue, Finset.sum_neg_distrib]
    ring
  have hid := PriorityRestriction.two_ratio_product_identity
    (affineValue c₁ a₁ x) (affineValue d₀ d x) (affineValue c₂ a₂ x) 1
    hD.ne' (by simpa [hBeq] using hB.ne')
  simp only [Fin.sum_univ_two, num₀, num, den₀, den, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_add]
  rw [hN, neg_div, ← sub_eq_add_neg, hBeq]
  simp only [one_mul] at hid
  rw [hid, div_pos_iff_of_pos_right (mul_pos hD (by simpa [hBeq] using hB))]
  simp [affineProductPredicate]

end HeadComplexity
