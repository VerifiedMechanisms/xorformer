import HeadComplexity.Results.ReverseGridAxisRepair

set_option linter.style.header false

/-! Exact rank-factorized grid corrections with one head per factor and one
shared affine correction. Every output denominator is positive on the entire
Boolean cube. Strictification uses the checked weight-two gauge. -/

namespace HeadComplexity
namespace AxisZeroGluing

open scoped BigOperators

private theorem rank_grid_affine {r s : ℕ} (c : ℝ)
    (a : Fin r → ℝ) (b : Fin s → ℝ) (i : Fin r) (j : Fin s) :
    affineValue c (Fin.addCases a b) (localGrid i j) = c + a i + b j := by
  simp [affineValue, localGrid, Fin.sum_univ_add, boolToReal, add_assoc]

/-- A rank-one factor is exactly a single weak reverse head, up to a
column-only term. The constant in that term can be shared across factors. -/
theorem exists_weak_reverse_rank_factor {r s : ℕ}
    (f : Fin r → ℝ) (g : Fin s → ℝ) :
    ∃ T : ℝ, ∃ Q : WeakReverseRatio (r + s),
      ∀ i j, Q.value (localGrid i j) = (T + f i) * g j := by
  classical
  let C : ℝ := 1 + ∑ i, |f i|
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hf (i : Fin r) : |f i| < C := by
    have h := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) ↦ abs_nonneg (f k))
      (Finset.mem_univ i)
    dsimp [C]
    linarith
  let u : Fin r → ℝ := fun i ↦ f i + C
  have hu (i : Fin r) : 0 < u i := by
    have h := hf i
    have ha := neg_abs_le (f i)
    dsimp [u]
    linarith
  have huC (i : Fin r) : u i < 2 * C := by
    have h := hf i
    have ha := le_abs_self (f i)
    dsimp [u]
    linarith
  let M : ℝ := 4 * ((r : ℝ) + 1) * C
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hM : 0 < M := by dsimp [M]; positivity
  let t : ℝ := 1 / (2 * ((r : ℝ) + 1))
  have ht : 0 < t := by dsimp [t]; positivity
  have hsmall (i : Fin r) : u i / (M + u i) ≤ t := by
    have hden : 0 < M + u i := by linarith [hu i]
    apply (div_le_iff₀ hden).mpr
    have hteq : t * (2 * ((r : ℝ) + 1)) = 1 := by
      dsimp [t]
      exact div_mul_cancel₀ _ (by positivity)
    have htM : t * M = 2 * C := by
      dsimp [M]
      nlinarith [hteq]
    have htu : 0 < t * u i := mul_pos ht (hu i)
    rw [mul_add, htM]
    linarith [huC i]
  have hmargin : 0 < 1 - (r : ℝ) * t := by
    have hteq : t * (2 * ((r : ℝ) + 1)) = 1 := by
      dsimp [t]
      exact div_mul_cancel₀ _ (by positivity)
    nlinarith
  let Q : WeakReverseRatio (r + s) :=
    { a₀ := 0
      a := Fin.addCases (fun _ ↦ 0) (fun j ↦ M * g j)
      b₀ := 1
      b := Fin.addCases (fun i ↦ -(u i / (M + u i))) (fun _ ↦ 0)
      nonpositive := by
        intro k
        refine Fin.addCases ?_ ?_ k
        · intro i
          simp only [Fin.addCases_left]
          exact neg_nonpos.mpr (div_nonneg (hu i).le (by linarith [hu i]))
        · intro j
          simp
      positive := by
        intro bits
        have hlower : ∀ i : Fin r,
            -t ≤ -(u i / (M + u i)) * boolToReal (bits (Fin.castAdd s i)) := by
          intro i
          cases bits (Fin.castAdd s i) <;> simp [boolToReal] <;> linarith [hsmall i]
        have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hlower i)
        have hs' : -(r : ℝ) * t ≤
            ∑ i : Fin r, -(u i / (M + u i)) * boolToReal (bits (Fin.castAdd s i)) := by
          simpa using hs
        simp only [affineValue, Fin.sum_univ_add, Fin.addCases_left,
          Fin.addCases_right, zero_mul, Finset.sum_const_zero, add_zero]
        linarith }
  refine ⟨M + C, Q, ?_⟩
  intro i j
  change affineValue 0 (Fin.addCases (fun _ : Fin r ↦ 0) (fun j : Fin s ↦ M * g j))
      (localGrid i j) /
      affineValue 1 (Fin.addCases (fun i : Fin r ↦ -(u i / (M + u i)))
        (fun _ : Fin s ↦ 0)) (localGrid i j) = _
  rw [rank_grid_affine, rank_grid_affine]
  have hden : M + u i ≠ 0 := ne_of_gt (by linarith [hu i])
  have hmne : M ≠ 0 := ne_of_gt hM
  simp only [zero_add, add_zero]
  have heq : 1 + -(u i / (M + u i)) = M / (M + u i) := by
    field_simp [hden]
    ring
  rw [heq, div_div_eq_mul_div]
  field_simp [hmne]
  dsimp [u]
  ring

/-- Every rank-factorized matrix, with arbitrary row and column additions, has
an exact weak reverse grid representation with one head per factor and one
shared affine correction. There are no size restrictions on the matrix entries. -/
theorem exists_weak_reverse_rank_grid {r s L : ℕ}
    (f : Fin L → Fin r → ℝ) (g : Fin L → Fin s → ℝ)
    (row : Fin r → ℝ) (col : Fin s → ℝ) (bias : ℝ) :
    ∃ Q : WeakReverseGridData r s (L + 1), ∀ i j,
      Q.score (localGrid i j) =
        bias + row i + col j + ∑ h, f h i * g h j := by
  classical
  choose T Q hQ using fun h ↦ exists_weak_reverse_rank_factor (f h) (g h)
  let c : Fin s → ℝ := fun j ↦ col j - ∑ h, T h * g h j
  let R : WeakReverseRatio (r + s) :=
    { a₀ := 0
      a := Fin.addCases row c
      b₀ := 1
      b := fun _ ↦ 0
      positive := fun bits ↦ by simp [affineValue]
      nonpositive := fun _ ↦ le_refl 0 }
  have hR (i : Fin r) (j : Fin s) :
      R.value (localGrid i j) = row i + c j := by
    change affineValue 0 (Fin.addCases row c) (localGrid i j) /
      affineValue 1 (fun _ ↦ 0) (localGrid i j) = _
    rw [rank_grid_affine]
    simp [affineValue]
  let G : WeakReverseGridData r s (L + 1) :=
    { bias := bias, head := Fin.addCases Q (fun _ : Fin 1 ↦ R) }
  refine ⟨G, ?_⟩
  intro i j
  change bias + (∑ h : Fin (L + 1),
    ((Fin.addCases Q (fun _ : Fin 1 ↦ R) :
      Fin (L + 1) → WeakReverseRatio (r + s)) h).value (localGrid i j)) = _
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, hQ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, hR]
  dsimp [c]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

/-- Strict negative slopes are restored with no additional heads and no change
to the represented matrix. This is the exact rank correction used in the
regular-sheet construction. -/
theorem exists_strict_reverse_rank_grid {r s L : ℕ}
    (f : Fin L → Fin r → ℝ) (g : Fin L → Fin s → ℝ)
    (row : Fin r → ℝ) (col : Fin s → ℝ) (bias : ℝ) :
    ∃ Q : StrictReverseGridData r s (L + 1), ∀ i j,
      Q.score (localGrid i j) =
        bias + row i + col j + ∑ h, f h i * g h j := by
  obtain ⟨Q, hQ⟩ := exists_weak_reverse_rank_grid f g row col bias
  obtain ⟨R, hR⟩ := exists_strict_reverse_grid_of_weak Q
  exact ⟨R, fun i j ↦ (hR i j).trans (hQ i j)⟩

/-- The same rank correction may be made exactly zero on both Boolean axes,
with the fixed factor-three repair cost. -/
theorem exists_reverse_axis_rank_grid {r s L : ℕ}
    (f : Fin L → Fin r → ℝ) (g : Fin L → Fin s → ℝ)
    (row : Fin r → ℝ) (col : Fin s → ℝ) (bias : ℝ) :
    ∃ Q : ReverseAxisData r s (3 * (L + 1) + 3), ∀ i j,
      Q.score (localGrid i j) =
        bias + row i + col j + ∑ h, f h i * g h j := by
  obtain ⟨Q, hQ⟩ := exists_strict_reverse_rank_grid f g row col bias
  obtain ⟨R, hR⟩ := exists_reverse_axis_repair Q
  exact ⟨R, fun i j ↦ (hR i j).trans (hQ i j)⟩

end AxisZeroGluing
end HeadComplexity
