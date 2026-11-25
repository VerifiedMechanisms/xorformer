import HeadComplexity.Results.PureGeneralReplicatedGrid

set_option linter.style.header false

/-!
# Coordinate monotonicity of the explicit pure rotary source

Every head score is increasing in every continuous input coordinate on the
closed cube. The proof uses a positive cross-multiplied numerator, without
differentiation or any change to the source or architecture.
-/

namespace HeadComplexity.PureGeneralReplicatedGrid

open scoped BigOperators

theorem u_ge_two {H : ℕ} (h : Fin H) (g : Fin (groupCount H)) :
    2 ≤ u h g := by
  simp only [u]
  split <;> norm_num

theorem abs_d_le_one {H : ℕ} (h : Fin H) (g : Fin (groupCount H)) :
    |d h g| ≤ 1 := by
  simp only [d]
  split <;> split <;> norm_num

theorem numerator_abs_le_mass {H : ℕ} (h : Fin H)
    (q : Fin (groupCount H) → ℝ) (hq : ∀ g, |q g| ≤ 1) :
    |numerator h q| ≤ mass H := by
  calc
    |numerator h q| ≤ ∑ g, |u h g * q g| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ g, u h g * |q g| := by
      simp only [abs_mul, abs_of_pos (u_pos h _)]
    _ ≤ ∑ g, u h g := by
      apply Finset.sum_le_sum
      intro g _
      simpa using mul_le_mul_of_nonneg_left (hq g) (u_pos h g).le
    _ = mass H := sum_u h

/-- The exact coefficient governing an increase in one coordinate is positive
throughout the closed cube, uniformly over the other coordinates. -/
theorem head_coordinate_cross_pos {H : ℕ} (h : Fin H)
    (q : Fin (groupCount H) → ℝ) (hq : ∀ g, |q g| ≤ 1)
    (g : Fin (groupCount H)) :
    0 < u h g * denominator h q - d h g * numerator h q := by
  have hden := denominator_pos h q hq
  have hdenbound := (denominator_bounds h q hq).1
  have hu : 2 * denominator h q ≤ u h g * denominator h q :=
    mul_le_mul_of_nonneg_right (u_ge_two h g) hden.le
  have hn : d h g * numerator h q ≤ mass H := by
    calc
      d h g * numerator h q ≤ |d h g * numerator h q| := le_abs_self _
      _ = |d h g| * |numerator h q| := abs_mul _ _
      _ ≤ |numerator h q| := by
        simpa using mul_le_mul_of_nonneg_right (abs_d_le_one h g)
          (abs_nonneg (numerator h q))
      _ ≤ mass H := numerator_abs_le_mass h q hq
  have hb : 0 < 2 * (base H - 2 * H) - mass H := by
    dsimp [base, mass]
    nlinarith [sq_nonneg ((H : ℝ) - 1 / 12)]
  nlinarith

theorem head_score_cross_difference {H : ℕ} (h : Fin H)
    (q q' : Fin (groupCount H) → ℝ) :
    numerator h q' * denominator h q - numerator h q * denominator h q' =
      ∑ g, (q' g - q g) *
        (u h g * denominator h q - d h g * numerator h q) := by
  have hn : numerator h q' - numerator h q = ∑ g, u h g * (q' g - q g) := by
    simp only [numerator, mul_sub, Finset.sum_sub_distrib]
  have hd : denominator h q' - denominator h q = ∑ g, d h g * (q' g - q g) := by
    simp only [denominator, mul_sub, Finset.sum_sub_distrib]
    ring
  calc
    numerator h q' * denominator h q - numerator h q * denominator h q' =
        (numerator h q' - numerator h q) * denominator h q -
          (denominator h q' - denominator h q) * numerator h q := by ring
    _ = _ := by
      rw [hn, hd, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro g _
      ring

theorem head_score_monotone_on_cube {H : ℕ} (h : Fin H)
    {q q' : Fin (groupCount H) → ℝ}
    (hq : ∀ g, |q g| ≤ 1) (hq' : ∀ g, |q' g| ≤ 1)
    (hle : ∀ g, q g ≤ q' g) :
    numerator h q / denominator h q ≤ numerator h q' / denominator h q' := by
  apply (div_le_div_iff₀ (denominator_pos h q hq) (denominator_pos h q' hq')).mpr
  have hc : 0 ≤ numerator h q' * denominator h q -
      numerator h q * denominator h q' := by
    rw [head_score_cross_difference]
    apply Finset.sum_nonneg
    intro g _
    exact mul_nonneg (sub_nonneg.mpr (hle g)) (head_coordinate_cross_pos h q hq g).le
  linarith

/-- The source score is monotone in the pointwise order on the closed cube. -/
theorem score_monotone_on_cube {H : ℕ} {q q' : Fin (groupCount H) → ℝ}
    (hq : ∀ g, |q g| ≤ 1) (hq' : ∀ g, |q' g| ≤ 1)
    (hle : ∀ g, q g ≤ q' g) : score q ≤ score q' := by
  apply Finset.sum_le_sum
  intro h _
  exact head_score_monotone_on_cube h hq hq' hle

/-- Increasing at least one coordinate strictly increases each head score. -/
theorem head_score_strict_on_cube {H : ℕ} (h : Fin H)
    {q q' : Fin (groupCount H) → ℝ}
    (hq : ∀ g, |q g| ≤ 1) (hq' : ∀ g, |q' g| ≤ 1)
    (hle : ∀ g, q g ≤ q' g) (hlt : ∃ g, q g < q' g) :
    numerator h q / denominator h q < numerator h q' / denominator h q' := by
  apply (div_lt_div_iff₀ (denominator_pos h q hq) (denominator_pos h q' hq')).mpr
  have hc : 0 < numerator h q' * denominator h q -
      numerator h q * denominator h q' := by
    rw [head_score_cross_difference]
    obtain ⟨g, hg⟩ := hlt
    apply lt_of_lt_of_le
      (mul_pos (sub_pos.mpr hg) (head_coordinate_cross_pos h q hq g))
    exact Finset.single_le_sum (fun i _ ↦
      mul_nonneg (sub_nonneg.mpr (hle i)) (head_coordinate_cross_pos h q hq i).le)
      (Finset.mem_univ g)
  linarith

/-- For a positive number of heads, the source score strictly increases
whenever a pointwise increase changes at least one coordinate. -/
theorem score_strict_on_cube {H : ℕ} (hH : 0 < H)
    {q q' : Fin (groupCount H) → ℝ}
    (hq : ∀ g, |q g| ≤ 1) (hq' : ∀ g, |q' g| ≤ 1)
    (hle : ∀ g, q g ≤ q' g) (hlt : ∃ g, q g < q' g) : score q < score q' := by
  apply Finset.sum_lt_sum
  · intro h _
    exact head_score_monotone_on_cube h hq hq' hle
  · exact ⟨⟨0, hH⟩, Finset.mem_univ _,
      head_score_strict_on_cube ⟨0, hH⟩ hq hq' hle hlt⟩

end HeadComplexity.PureGeneralReplicatedGrid
