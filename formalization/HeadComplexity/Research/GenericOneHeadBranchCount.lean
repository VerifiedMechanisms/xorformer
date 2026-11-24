import HeadComplexity.Research.GenericOneHeadBasisNonuniqueness

set_option linter.style.header false
set_option linter.style.longLine false
set_option maxRecDepth 4096

noncomputable section
namespace HeadComplexity.GenericOneHeadBasisNonuniqueness
open scoped BigOperators

def exceptionalPoint : Fin 7 → Bool := ![false, false, true, false, false, false, true]

def positiveTable (a : Fin 8 → ℝ) : (Fin 7 → Bool) → Bool :=
  fun x => decide (0 < affine a x)

set_option maxHeartbeats 8000000 in
/-- In this particular basis example only one row has mixed coefficient signs.
This statement does not assume the full-cube unit-gap feasibility inequalities. -/
theorem sign_fixed_outside_exceptional (b : Fin 8 → ℝ) (hb : ∀ i, 0 < b i)
    (x : Fin 7 → Bool) (hx : x ≠ exceptionalPoint) :
    (0 < affine (transform b) x) ↔ 0 < affine (baseNumerator 0) x := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  have h4 := hb 4
  have h5 := hb 5
  have h6 := hb 6
  have h7 := hb 7
  have hvec : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    ext i
    fin_cases i <;> rfl
  rw [hvec] at hx ⊢
  generalize x 0 = b0, x 1 = b1, x 2 = b2, x 3 = b3, x 4 = b4,
    x 5 = b5, x 6 = b6 at hx ⊢
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases b4 <;> cases b5 <;> cases b6 <;>
    try { norm_num [exceptionalPoint] at hx }
  all_goals
    norm_num [affine, affineValue, transform, matrix,
      baseNumerator, Fin.sum_univ_succ, boolToReal] <;> linarith

theorem positiveTable_eq_one_of_two (b : Fin 8 → ℝ) (hb : ∀ i, 0 < b i) :
    positiveTable (transform b) = positiveTable (baseNumerator 0) ∨
    positiveTable (transform b) = positiveTable (baseNumerator 1) := by
  by_cases he : 0 < affine (transform b) exceptionalPoint
  · left
    funext x
    by_cases hx : x = exceptionalPoint
    · subst x
      have hbase : 0 < affine (baseNumerator 0) exceptionalPoint := by
        norm_num [exceptionalPoint, affine, affineValue, baseNumerator, Fin.sum_univ_succ, boolToReal]
      simp only [positiveTable, he, hbase]
    · simp only [positiveTable, sign_fixed_outside_exceptional b hb x hx]
  · right
    funext x
    by_cases hx : x = exceptionalPoint
    · subst x
      have hbase : ¬ 0 < affine (baseNumerator 1) exceptionalPoint := by
        norm_num [exceptionalPoint, affine, affineValue, baseNumerator, Fin.sum_univ_succ, boolToReal]
      simp only [positiveTable, he, hbase]
    · have h1 := sign_fixed_outside_exceptional (baseDenominator 1)
        (baseDenominator_pos 1) x hx
      rw [transform_base] at h1
      simp only [positiveTable, sign_fixed_outside_exceptional b hb x hx, h1]

def positiveBasisTables : Finset ((Fin 7 → Bool) → Bool) := by
  classical
  exact Finset.univ.filter fun f => ∃ b : Fin 8 → ℝ,
    (∀ i, 0 < b i) ∧ positiveTable (transform b) = f

theorem positiveBasisTables_eq_pair : positiveBasisTables =
    {positiveTable (baseNumerator 0), positiveTable (baseNumerator 1)} := by
  classical
  ext f
  simp only [positiveBasisTables, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact positiveTable_eq_one_of_two b hb
  · rintro (rfl | rfl)
    · exact ⟨baseDenominator 0, baseDenominator_pos 0, congrArg positiveTable (transform_base 0)⟩
    · exact ⟨baseDenominator 1, baseDenominator_pos 1, congrArg positiveTable (transform_base 1)⟩

theorem positiveBasisTables_card : positiveBasisTables.card = 2 := by
  rw [positiveBasisTables_eq_pair]
  have hn : positiveTable (baseNumerator 0) ≠ positiveTable (baseNumerator 1) := by
    intro h
    have he := congrFun h exceptionalPoint
    norm_num [positiveTable, exceptionalPoint, affine, affineValue,
      baseNumerator, Fin.sum_univ_succ, boolToReal] at he
  simp [hn]

/-- Every numerator with the prescribed actual unit sample values is the
specified linear transform, so the two-table conclusion applies to refits too. -/
theorem positiveTable_eq_one_of_two_of_basis_values
    (a b : Fin 8 → ℝ) (hb : ∀ i, 0 < b i)
    (h : ∀ j, affine a (basisPoint j) = basisValue j * affine b (basisPoint j)) :
    positiveTable a = positiveTable (baseNumerator 0) ∨
    positiveTable a = positiveTable (baseNumerator 1) := by
  have ha : a = transform b := basis_affine_injective a (transform b) fun j =>
    (h j).trans (basis_identity b j).symm
  rw [ha]
  exact positiveTable_eq_one_of_two b hb

end HeadComplexity.GenericOneHeadBasisNonuniqueness
