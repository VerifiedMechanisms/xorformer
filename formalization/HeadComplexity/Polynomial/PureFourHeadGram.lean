import HeadComplexity.Polynomial.FourHeadLocalQuadratic
import HeadComplexity.Polynomial.PositiveGramObstruction

set_option linter.style.header false

namespace HeadComplexity.PureFourHeadGram

noncomputable section

open Finset Matrix PureRoPEThreeHead FourHeadSelectorQuadratic FourHeadLocalPattern
open scoped BigOperators

def middle (c : ℝ) (d e n a k l : Fin 4 → ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  Fin.append
    (fun i ↦ Fin.append (fun _ ↦ 0) (fun j ↦ k i * mixed d e i j))
    (fun i ↦ Fin.append (fun j ↦ mixed d e i j * k j)
      (fun j ↦ (l i + l j) * mixed d e i j + pair c d e n a i j))

def row (s b : Fin 4 → ℝ) : Fin 8 → ℝ := Fin.append s b

def factor (c : ℝ) (d e n a k l s b : Fin 4 → ℝ) : Fin 4 → ℝ :=
  firstFactor c d e n a (fun h ↦ k h * s h + l h * b h) b

theorem mixed_symmetric (d e : Fin 4 → ℝ) (i j : Fin 4) :
    mixed d e i j = mixed d e j i := by
  fin_cases i <;> fin_cases j <;> simp [mixed]

theorem pair_symmetric (c : ℝ) (d e n a : Fin 4 → ℝ) (i j : Fin 4) :
    pair c d e n a i j = pair c d e n a j i := by
  simp only [pair, mixed_symmetric d e i j, mixed_symmetric d a i j,
    mixed_symmetric n e i j]

theorem middle_symmetric (c : ℝ) (d e n a k l : Fin 4 → ℝ) (i j : Fin 8) :
    middle c d e n a k l i j = middle c d e n a k l j i := by
  refine Fin.addCases (m := 4) (n := 4) (fun i ↦ ?_) (fun i ↦ ?_) i <;>
    refine Fin.addCases (m := 4) (n := 4) (fun j ↦ ?_) (fun j ↦ ?_) j <;>
    simp only [middle, Fin.append_left, Fin.append_right]
  all_goals
    rw [mixed_symmetric d e i j]
    try rw [pair_symmetric c d e n a i j]
    ring

set_option maxHeartbeats 2000000 in
-- Expand the fixed eight-dimensional bilinear identity over its four heads.
theorem middle_bilinear (c : ℝ) (d e n a k l s b s' b' : Fin 4 → ℝ) :
    dotProduct (row s b) ((middle c d e n a k l).mulVec (row s' b')) =
      ∑ h, (factor c d e n a k l s b h * b' h + b h * factor c d e n a k l s' b' h) := by
  simp [dotProduct, Matrix.mulVec, row, middle, factor, firstFactor, pair, mixed,
    Fin.sum_univ_succ, Fin.append, Fin.addCases]
  ring

def columns (S B : Fin 4 → Fin 16 → ℝ) (ix : Fin 8 → Fin 16) :
    Matrix (Fin 8) (Fin 8) ℝ := fun i ↦ row (fun h ↦ S h (ix i)) (fun h ↦ B h (ix i))

def factors (c : ℝ) (d e n a k l : Fin 4 → ℝ) (S B : Fin 4 → Fin 16 → ℝ) :
    Fin 4 → Fin 16 → ℝ := fun h i ↦ factor c d e n a k l (fun j ↦ S j i) (fun j ↦ B j i) h

theorem matrix_coefficient (c : ℝ) (d e n a k l : Fin 4 → ℝ)
    (S B : Fin 4 → Fin 16 → ℝ) (ix iy : Fin 8 → Fin 16) (i j : Fin 8) :
    (columns S B ix * middle c d e n a k l * (columns S B iy).transpose) i j =
      ∑ h, (factors c d e n a k l S B h (ix i) * B h (iy j) +
        B h (ix i) * factors c d e n a k l S B h (iy j)) := by
  have he := middle_bilinear c d e n a k l
    (fun h ↦ S h (ix i)) (fun h ↦ B h (ix i))
    (fun h ↦ S h (iy j)) (fun h ↦ B h (iy j))
  change _ = ∑ h, (factor c d e n a k l (fun h ↦ S h (ix i))
    (fun h ↦ B h (ix i)) h * B h (iy j) + B h (ix i) *
      factor c d e n a k l (fun h ↦ S h (iy j)) (fun h ↦ B h (iy j)) h)
  rw [← he]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, columns,
    dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

def unit : Fin 8 → ℝ := fun i ↦ if i = 0 then 1 else 0

theorem unit_ne_zero : unit ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [unit] at this

theorem middle_null (c : ℝ) (d e n a k l : Fin 4 → ℝ) :
    dotProduct unit ((middle c d e n a k l).mulVec unit) = 0 := by
  simp [unit, dotProduct, Matrix.mulVec, middle, Fin.append, Fin.addCases]

theorem columns_unit (S B : Fin 4 → Fin 16 → ℝ) (ix : Fin 8 → Fin 16) (i : Fin 8) :
    ((columns S B ix).mulVec unit) i = S 0 (ix i) := by
  simp [Matrix.mulVec, dotProduct, unit, columns, row, Fin.append, Fin.addCases]

/-- The full 404-label matching obstruction cannot be the selector projection
of four pure heads. This theorem uses only the shared positive mass column. -/
theorem quadratic_obstruction (q c : ℝ) (d e n a k l : Fin 4 → ℝ)
    (S B : Fin 4 → Fin 16 → ℝ) (hS : ∀ h i, 0 < S h i)
    (hz : productScore q (factors c d e n a k l S B) B zeroInput < 0)
    (hs : ∀ i, 0 < productScore q (factors c d e n a k l S B) B (singleInput i))
    (hc : ∀ i j : Fin 8, i ≠ j →
      productScore q (factors c d e n a k l S B) B (doubleInput (left i) (right j)) < 0)
    (hp : ∀ i j : Fin 8, i ≠ j →
      productScore q (factors c d e n a k l S B) B (doubleInput (right i) (right j)) < 0) :
    False := by
  let F := factors c d e n a k l S B
  apply PositiveGramObstruction.gram_obstruction_of_column_sums
    (columns S B left) (columns S B right) (middle c d e n a k l)
    (middle_symmetric c d e n a k l) unit unit_ne_zero (middle_null c d e n a k l)
  · intro i
    rw [columns_unit]
    exact hS 0 _
  · intro i
    rw [columns_unit]
    exact hS 0 _
  · intro i j hij
    rw [matrix_coefficient]
    have hidx : left i ≠ right j := by fin_cases i <;> fin_cases j <;> decide
    have he := product_face_difference q F B (left i) (right j) hidx
    have h1 := hs (left i)
    have h2 := hs (right j)
    have h3 := hc i j hij
    change 0 < productScore q F B (singleInput (left i)) at h1
    change 0 < productScore q F B (singleInput (right j)) at h2
    change productScore q F B (doubleInput (left i) (right j)) < 0 at h3
    change productScore q F B zeroInput < 0 at hz
    dsimp only [F] at he h1 h2 h3 hz
    linarith
  · intro j
    simp_rw [matrix_coefficient]
    change 0 < ∑ i, crossCoefficient F B i j
    have he := column_identity q F B j
    have hsum : 0 ≤ ∑ k' : Fin 8, if k' = j then 0 else
        productScore q F B (singleInput (right k')) -
          productScore q F B (doubleInput (right j) (right k')) := by
      apply Finset.sum_nonneg
      intro k' _
      split_ifs with h
      · exact le_refl 0
      · have h1 := hs (right k')
        have h2 := hp j k' (Ne.symm h)
        change 0 < productScore q F B (singleInput (right k')) at h1
        change productScore q F B (doubleInput (right j) (right k')) < 0 at h2
        linarith
    have h1 := hs (right j)
    change 0 < productScore q F B (singleInput (right j)) at h1
    change productScore q F B zeroInput < 0 at hz
    linarith
  · intro i j hij
    rw [matrix_coefficient]
    have hidx : right i ≠ right j := by
      intro h
      have hi : Function.Injective right := by
        intro i j h
        fin_cases i <;> fin_cases j <;> simp_all [right]
      exact hij (hi h)
    have he := product_face_difference q F B (right i) (right j) hidx
    have h1 := hs (right i)
    have h2 := hs (right j)
    have h3 := hp i j hij
    change 0 < productScore q F B (singleInput (right i)) at h1
    change 0 < productScore q F B (singleInput (right j)) at h2
    change productScore q F B (doubleInput (right i) (right j)) < 0 at h3
    change productScore q F B zeroInput < 0 at hz
    dsimp only [F] at he h1 h2 h3 hz
    linarith

end
end HeadComplexity.PureFourHeadGram
