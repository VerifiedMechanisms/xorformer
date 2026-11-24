import HeadComplexity.Results.ReverseMaskedCauchy

set_option linter.style.header false

/-!
# Exact masked row biases with two axis-zero heads per mask

The query masks are fixed across rows. Their row coefficients are arbitrary.
This supplies the block biases in the Haar decoder investigation without
assuming that independent query biases are free. It is an implementation
lemma, not a shattering assertion or an asymptotic head-count improvement.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

/-- A sum of masked row coefficients has an exact axis-zero realization
using two strictly admissible reverse heads for each fixed Boolean mask. -/
theorem exists_reverseAxis_masked_row_sum {r s H : ℕ}
    (b : Fin H → Fin r → ℝ) (mask : Fin H → Fin s → Bool) :
    ∃ L : ReverseAxisData r s (H + H), ∀ i j,
      L.score (localGrid i j) = ∑ h, if mask h j then b h i else 0 := by
  classical
  let C : ℝ := 2 * (r : ℝ) + 2 * (s : ℝ) + 4
  let p : Fin H → Fin r → ℝ := fun _ _ ↦ 1
  let a : Fin H → Fin r → ℝ := fun h i ↦ (C - 3) * (C - 2) * b h i
  let u : Fin H → Fin s → ℝ := fun h j ↦ 1 + if mask h j then 1 else 0
  let v : Fin H → Fin s → ℝ := fun _ _ ↦ 1
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
  have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
  have hC : 3 < C := by dsimp [C]; linarith
  have hp : ∀ h i, 0 < p h i := by intros; norm_num [p]
  have hu : ∀ h j, 0 < u h j := by
    intro h j
    cases hm : mask h j <;> norm_num [u, hm]
  have hv : ∀ h j, 0 < v h j := by intros; norm_num [v]
  have hCu : ∀ h, (∑ i, p h i) + (∑ j, u h j) < C := by
    intro h
    have hub : (∑ j, u h j) ≤ 2 * (s : ℝ) := by
      calc
        _ ≤ ∑ _j : Fin s, (2 : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          cases hm : mask h j <;> norm_num [u, hm]
        _ = _ := by simp; ring
    simp only [p, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    dsimp [C]
    linarith
  have hCv : ∀ h, (∑ i, p h i) + (∑ j, v h j) < C := by
    intro h
    simp only [p, v, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    dsimp [C]
    linarith
  refine ⟨pairedRowsAxisData C p a u v hp hu hv hCu hCv, ?_⟩
  intro i j
  rw [pairedRowsAxisData_grid]
  apply Finset.sum_congr rfl
  intro h _
  dsimp [p, a, u, v]
  cases hm : mask h j
  · simp
  · simp only [↓reduceIte]
    have h2 : C - 2 ≠ 0 := by linarith
    have h3 : C - 3 ≠ 0 := by linarith
    rw [show C - 1 - (1 + 1) = C - 3 by ring,
      show C - 1 - 1 = C - 2 by ring]
    field_simp
    ring

end HeadComplexity.AxisZeroGluing
