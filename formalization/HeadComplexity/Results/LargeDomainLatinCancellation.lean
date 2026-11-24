import HeadComplexity.Results.LargeDomainGridSupport

set_option linter.style.header false

namespace HeadComplexity.LargeDomain

open scoped BigOperators

/-- A Latin assignment is a color table whose rows and columns are
permutations. Different columns of a larger decoding problem may choose
these tables independently. -/
structure LatinAssignment (q : ℕ) where
  color : Fin q → Fin q → Fin q
  row_bijective : ∀ i, Function.Bijective (color i)
  column_bijective : ∀ j, Function.Bijective (fun i ↦ color i j)

noncomputable def latinCauchyScore {q : ℕ} (T : LatinAssignment q)
    (b r c : Fin q → ℝ) : ℝ :=
  ∑ i, ∑ j, 1 / (b (T.color i j) + r i + c j)

theorem latin_cauchy_zero_left {q : ℕ} (T : LatinAssignment q)
    (b c : Fin q → ℝ) :
    latinCauchyScore T b (fun _ ↦ 0) c =
      ∑ j, ∑ k, 1 / (b k + c j) := by
  classical
  unfold latinCauchyScore
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [add_zero, Equiv.coe_ofBijective] using
    Equiv.sum_comp (Equiv.ofBijective (fun i ↦ T.color i j) (T.column_bijective j))
      (fun k ↦ 1 / (b k + c j))

theorem latin_cauchy_zero_right {q : ℕ} (T : LatinAssignment q)
    (b r : Fin q → ℝ) :
    latinCauchyScore T b r (fun _ ↦ 0) =
      ∑ i, ∑ k, 1 / (b k + r i) := by
  classical
  unfold latinCauchyScore
  apply Finset.sum_congr rfl
  intro i _
  simpa only [add_zero, Equiv.coe_ofBijective] using
    Equiv.sum_comp (Equiv.ofBijective (T.color i) (T.row_bijective i))
      (fun k ↦ 1 / (b k + r i))

/-- The cancellation keeps the full reciprocal dependence on arbitrary
color poles; it does not truncate a finite Taylor expansion. -/
theorem latin_cauchy_difference_zero_axes {q : ℕ}
    (T U : LatinAssignment q) (b r c : Fin q → ℝ) :
    (latinCauchyScore T b (fun _ ↦ 0) c -
      latinCauchyScore U b (fun _ ↦ 0) c = 0) ∧
    (latinCauchyScore T b r (fun _ ↦ 0) -
      latinCauchyScore U b r (fun _ ↦ 0) = 0) := by
  constructor
  · rw [latin_cauchy_zero_left, latin_cauchy_zero_left, sub_self]
  · rw [latin_cauchy_zero_right, latin_cauchy_zero_right, sub_self]

theorem latin_cauchy_denominator_pos {q : ℕ} (T : LatinAssignment q)
    (b r c : Fin q → ℝ) (hb : ∀ i, 0 < b i)
    (hr : ∀ i, 0 ≤ r i) (hc : ∀ j, 0 ≤ c j) (i j : Fin q) :
    0 < b (T.color i j) + r i + c j := by
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg (hb _) (hr i)) (hc j)

end HeadComplexity.LargeDomain
