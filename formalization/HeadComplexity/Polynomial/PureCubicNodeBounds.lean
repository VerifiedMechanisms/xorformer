import HeadComplexity.Polynomial.PureCubicRawKernel

set_option linter.style.header false

/-! # Exact size and rational denominator bounds for every finite zero-chart node -/

namespace HeadComplexity.PureCubicNodeBounds

noncomputable section

open MvPolynomial Matrix PureCubicChart PureCubicFiniteKernel PureCubicRawKernel
open PureCubicGraph
open scoped BigOperators

def smallRadius : ℝ := 1 / 2 ^ 40

theorem smallRadius_pos : 0 < smallRadius := by norm_num [smallRadius]

theorem smallRadius_lt_one : smallRadius < 1 := by norm_num [smallRadius]

theorem graphPoint_abs_bound (y : Fin 13 → ℝ)
    (hy : ∀ i, y i ∈ chartGrid) (i : Fin 14) :
    |graphPoint y i| < 4 * smallRadius := by
  have hn (j : Fin 13) : 0 ≤ y j := chartGrid_nonnegative (hy j)
  have hs (j : Fin 13) : y j < smallRadius := chartGrid_small (hy j)
  have hd₁ : 0 < 1 + y 3 := by linarith [hn 3]
  have hd₂ : 0 < 1 + y 4 := by linarith [hn 4]
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [graphPoint_first y hd₁.ne' hd₂.ne']
    have hp : 0 < 1 + y 2 := by linarith [hn 2]
    have ht (u v : Fin 13) : 0 ≤ y u * (1 + y 2) / (1 + y v) ∧
        y u * (1 + y 2) / (1 + y v) < 2 * smallRadius := by
      have hd : 0 < 1 + y v := by linarith [hn v]
      constructor
      · exact div_nonneg (mul_nonneg (hn u) hp.le) hd.le
      · apply (div_lt_iff₀ hd).mpr
        have hmul := mul_lt_mul_of_pos_right (hs u) hp
        have hsmall : 1 + y 2 < 2 := by linarith [hs 2, smallRadius_lt_one]
        have hmul₂ := mul_lt_mul_of_pos_left hsmall smallRadius_pos
        have hden : 2 * smallRadius ≤ 2 * smallRadius * (1 + y v) := by
          nlinarith [smallRadius_pos, hn v]
        nlinarith
    have h₁ := ht 0 3
    have h₂ := ht 1 4
    have he : graphFirst (y 0) (y 1) (y 2) (y 3) (y 4) =
        -(y 0 * (1 + y 2) / (1 + y 3) + y 1 * (1 + y 2) / (1 + y 4)) := by
      simp [graphFirst]
      ring
    rw [he, abs_neg, abs_of_nonneg (by linarith :
      0 ≤ y 0 * (1 + y 2) / (1 + y 3) + y 1 * (1 + y 2) / (1 + y 4))]
    linarith
  · rw [graphPoint_succ, abs_of_nonneg (hn j)]
    linarith [hs j, smallRadius_pos]

theorem rawNode_abs_bound (y : Fin 13 → ℝ)
    (hy : ∀ i, y i ∈ chartGrid) (i : Fin 14) : |rawNode y i| < 1 / 16 := by
  have hsum : |rawNode y i| ≤ (∑ j, |chartInverse i j|) * (4 * smallRadius) := by
    unfold rawNode Matrix.mulVec dotProduct
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (graphPoint_abs_bound y hy j).le (abs_nonneg _)
  have hrow := mul_lt_mul_of_pos_right (inverse_row_bound i)
    (show 0 < 4 * smallRadius by exact mul_pos (by norm_num) smallRadius_pos)
  have he : (2 : ℝ) ^ 34 * (4 * smallRadius) = 1 / 16 := by norm_num [smallRadius]
  rw [he] at hrow
  exact hsum.trans_lt hrow

def integerScale : ℕ := 10 * 2 ^ 40

theorem integerScale_cast : (integerScale : ℝ) = chartScale := by
  norm_num [integerScale, chartScale]

def indexedGrid (j : Fin 13 → Fin 10) (i : Fin 13) : ℝ := gridPoint (j i)

theorem indexedGrid_mem (j : Fin 13 → Fin 10) (i : Fin 13) :
    indexedGrid j i ∈ chartGrid := Finset.mem_image.mpr ⟨j i, Finset.mem_univ _, rfl⟩

def graphDenominator (j : Fin 13 → Fin 10) : ℕ :=
  integerScale * (integerScale + (j 3).val) * (integerScale + (j 4).val)

def graphInteger (j : Fin 13 → Fin 10) : Fin 14 → ℤ := Fin.cons
  (-((j 0).val : ℤ) * ((integerScale : ℤ) + (j 2).val) *
      ((integerScale : ℤ) + (j 4).val) -
    ((j 1).val : ℤ) * ((integerScale : ℤ) + (j 2).val) *
      ((integerScale : ℤ) + (j 3).val))
  (fun i ↦ ((j i).val : ℤ) * ((integerScale : ℤ) + (j 3).val) *
    ((integerScale : ℤ) + (j 4).val))

theorem graphDenominator_pos (j : Fin 13 → Fin 10) : 0 < graphDenominator j := by
  unfold graphDenominator integerScale
  positivity

theorem graphPoint_rational (j : Fin 13 → Fin 10) (i : Fin 14) :
    graphPoint (indexedGrid j) i = (graphInteger j i : ℝ) / graphDenominator j := by
  have hL : (integerScale : ℝ) ≠ 0 := by norm_num [integerScale]
  have h₁ : (integerScale : ℝ) + (j 3).val ≠ 0 := by
    have h : (0 : ℝ) ≤ (j 3).val := Nat.cast_nonneg _
    norm_num [integerScale] at *
    linarith
  have h₂ : (integerScale : ℝ) + (j 4).val ≠ 0 := by
    have h : (0 : ℝ) ≤ (j 4).val := Nat.cast_nonneg _
    norm_num [integerScale] at *
    linarith
  have hd₁ : 1 + indexedGrid j 3 ≠ 0 := by
    have h := chartGrid_nonnegative (indexedGrid_mem j 3)
    linarith
  have hd₂ : 1 + indexedGrid j 4 ≠ 0 := by
    have h := chartGrid_nonnegative (indexedGrid_mem j 4)
    linarith
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · rw [graphPoint_first _ hd₁ hd₂]
    simp only [graphFirst, indexedGrid, gridPoint, ← integerScale_cast, graphInteger,
      Fin.cons_zero, graphDenominator, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_add, Nat.cast_mul, Nat.cast_add]
    field_simp
  · simp only [graphPoint_succ, indexedGrid, gridPoint, ← integerScale_cast, graphInteger,
      Fin.cons_succ, graphDenominator, Int.cast_mul, Int.cast_natCast, Int.cast_add,
      Nat.cast_mul, Nat.cast_add]
    field_simp

def nodeDenominator (j : Fin 13 → Fin 10) : ℕ := 48 * graphDenominator j

def nodeInteger (j : Fin 13 → Fin 10) (i : Fin 14) : ℤ :=
  ∑ k, inverseNumerator i k * graphInteger j k

theorem rawNode_rational (j : Fin 13 → Fin 10) (i : Fin 14) :
    rawNode (indexedGrid j) i = (nodeInteger j i : ℝ) / nodeDenominator j := by
  simp only [rawNode, Matrix.mulVec, dotProduct, chartInverse, graphPoint_rational,
    nodeInteger, Int.cast_sum, Int.cast_mul, nodeDenominator, Nat.cast_mul, Nat.cast_ofNat]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem nodeDenominator_pos (j : Fin 13 → Fin 10) : 0 < nodeDenominator j :=
  Nat.mul_pos (by decide) (graphDenominator_pos j)

theorem nodeDenominator_bound (j : Fin 13 → Fin 10) : nodeDenominator j < 2 ^ 138 := by
  have h₁ : (j 3).val ≤ 9 := by omega
  have h₂ : (j 4).val ≤ 9 := by omega
  have hb : nodeDenominator j ≤ 48 * (integerScale * (integerScale + 9) *
      (integerScale + 9)) := by
    exact Nat.mul_le_mul_left 48 (Nat.mul_le_mul
      (Nat.mul_le_mul_left integerScale (Nat.add_le_add_left h₁ integerScale))
      (Nat.add_le_add_left h₂ integerScale))
  exact hb.trans_lt (by norm_num [integerScale])

theorem finite_node_denominator (y : Fin 13 → ℝ) (hy : ∀ i, y i ∈ chartGrid) :
    ∃ q : ℕ, 0 < q ∧ q < 2 ^ 138 ∧ ∀ i, ∃ a : ℤ, rawNode y i = (a : ℝ) / q := by
  choose j hj using fun i ↦ Finset.mem_image.mp (hy i)
  have he : y = indexedGrid j := by
    funext i
    exact (hj i).2.symm
  subst y
  exact ⟨nodeDenominator j, nodeDenominator_pos j, nodeDenominator_bound j,
    fun i ↦ ⟨nodeInteger j i, rawNode_rational j i⟩⟩

end
end HeadComplexity.PureCubicNodeBounds
