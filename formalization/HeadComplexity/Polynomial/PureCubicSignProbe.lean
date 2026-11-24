import HeadComplexity.Polynomial.MeanGridSignProbe
import HeadComplexity.Polynomial.PureCubicNodeBounds
import HeadComplexity.Polynomial.PureCubicCoefficientBounds

set_option linter.style.header false

/-! # Actual rational-chart sign probes for the explicit pure cubic -/

namespace HeadComplexity.PureCubicSignProbe
noncomputable section
open scoped BigOperators Matrix
open MvPolynomial PureCubicChart PureCubicFiniteKernel PureCubicRawKernel
open PureCubicIrreducible PureCubicGraph PureCubicNodeBounds MeanGridSignProbe

/-- Translate only the first numerator coordinate in the exact linear chart. -/
def probe (y : Fin 13 → ℝ) (t : ℝ) : Fin 14 → ℝ :=
  chartInverse *ᵥ (graphPoint y + Pi.single 0 t)

theorem probe_apply (y : Fin 13 → ℝ) (t : ℝ) (i : Fin 14) :
    probe y t i = rawNode y i + chartInverse i 0 * t := by
  simp [probe, rawNode, Matrix.mulVec, dotProduct,
    Pi.single_apply, mul_add, Finset.sum_add_distrib]

theorem eval_probe (y : Fin 13 → ℝ) (hy : ∀ i, y i ∈ chartGrid) (t : ℝ) :
    eval (probe y t) rawTarget = t * (1 + y 3) * (1 + y 4) := by
  rw [rawTarget, eval_substitution, probe, chart_apply_inverse]
  have hzero := eval_target_graphPoint y (grid_leading_positive y hy).ne'
  simp only [coordinatePolynomial, map_add, map_mul, map_one, eval_X] at hzero ⊢
  simp only [Pi.add_apply, Pi.single_apply]
  norm_num [Fin.ext_iff]
  have h4 : graphPoint y 4 = y 3 := rfl
  have h5 : graphPoint y 5 = y 4 := rfl
  simp only [h4, h5] at hzero ⊢
  nlinarith

theorem probe_displacement (y : Fin 13 → ℝ) (t : ℝ) (i : Fin 14) :
    |probe y t i - rawNode y i| ≤ (2 : ℝ) ^ 34 * |t| := by
  rw [probe_apply, add_sub_cancel_left, abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg t)
  exact (inverse_first_column_bound i).le.trans (by norm_num)

theorem scaled_probe_displacement (y : Fin 13 → ℝ) (m : ℕ) (hm : 0 < m)
    (i : Fin 14) :
    |probe y ((2 : ℝ) ^ 20 / m) i - rawNode y i| ≤ (2 : ℝ) ^ 54 / m ∧
    |probe y (-((2 : ℝ) ^ 20 / m)) i - rawNode y i| ≤ (2 : ℝ) ^ 54 / m := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have ht : (0 : ℝ) ≤ 2^20 / m := by positivity
  have hp := probe_displacement y ((2 : ℝ) ^ 20 / m) i
  have hn := probe_displacement y (-((2 : ℝ) ^ 20 / m)) i
  rw [abs_of_nonneg ht] at hp
  rw [abs_neg, abs_of_nonneg ht] at hn
  have heq : (2 : ℝ) ^ 34 * (2^20 / m) = (2 : ℝ) ^ 54 / m := by
    rw [← mul_div_assoc, ← pow_add]
  exact ⟨by simpa only [heq] using hp, by simpa only [heq] using hn⟩

theorem scaled_probes_in_cube (y : Fin 13 → ℝ) (hy : ∀ i, y i ∈ chartGrid)
    (m : ℕ) (hm : 0 < m) (hsize : (2 : ℝ) ^ 60 ≤ m) (i : Fin 14) :
    |probe y ((2 : ℝ) ^ 20 / m) i| ≤ 1 ∧
    |probe y (-((2 : ℝ) ^ 20 / m)) i| ≤ 1 := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hd : (2 : ℝ) ^ 54 / m ≤ 1 / 64 := by
    apply (div_le_iff₀ hmr).mpr
    nlinarith
  have ha := rawNode_abs_bound y hy i
  obtain ⟨hp, hn⟩ := scaled_probe_displacement y m hm i
  have htp := abs_sub_le (probe y ((2 : ℝ) ^ 20 / m) i) (rawNode y i) 0
  have htn := abs_sub_le (probe y (-((2 : ℝ) ^ 20 / m)) i) (rawNode y i) 0
  simp only [sub_zero] at htp htn
  constructor <;> linarith

theorem scaled_probe_signs (y : Fin 13 → ℝ) (hy : ∀ i, y i ∈ chartGrid)
    (m : ℕ) (hm : 0 < m) :
    (2 : ℝ) ^ 18 / m ≤ eval (probe y ((2 : ℝ) ^ 20 / m)) rawTarget ∧
    eval (probe y (-((2 : ℝ) ^ 20 / m))) rawTarget ≤ -((2 : ℝ) ^ 18 / m) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have ht : (0 : ℝ) ≤ 2^20 / m := by positivity
  have h3 := chartGrid_nonnegative (hy 3)
  have h4 := chartGrid_nonnegative (hy 4)
  have hprod : 1 ≤ (1 + y 3) * (1 + y 4) := by nlinarith
  have hlarge : (2 : ℝ) ^ 18 / m ≤ (2 : ℝ) ^ 20 / m :=
    (div_le_div_iff_of_pos_right hmr).mpr (by norm_num)
  rw [eval_probe y hy, eval_probe y hy]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hprod ht]

/-- The explicit finite zero-chart samples have uniformly small residual under
any normalized cubic with the correct signs on the mean grid. -/
theorem chart_residual_bound (Q : MvPolynomial (Fin 14) ℝ)
    (hQdeg : Q.totalDegree ≤ 3) (hQc : ∀ d, |Q.coeff d| ≤ 1)
    (hFc : ∀ d, |rawTarget.coeff d| ≤ 1)
    (m : ℕ) (hm : 0 < m) (hsize : (2 : ℝ) ^ 60 ≤ m)
    (hsign : ∀ k : Fin 14 → Fin (m + 1),
      (0 < eval (fun i ↦ gridValue m (k i)) rawTarget ↔
        0 < eval (fun i ↦ gridValue m (k i)) Q))
    (y : Fin 13 → ℝ) (hy : ∀ i, y i ∈ chartGrid) :
    |eval (rawNode y) Q| < (2 : ℝ) ^ 67 / m := by
  apply rounded_probe_bound rawTarget Q rawTarget_degree.le hQdeg hFc hQc m hm
    (rawNode y) (probe y ((2 : ℝ) ^ 20 / m)) (probe y (-((2 : ℝ) ^ 20 / m)))
    (fun i ↦ (rawNode_abs_bound y hy i).le.trans (by norm_num))
    (fun i ↦ (scaled_probes_in_cube y hy m hm hsize i).1)
    (fun i ↦ (scaled_probes_in_cube y hy m hm hsize i).2)
    (fun i ↦ (scaled_probe_displacement y m hm i).1)
    (fun i ↦ (scaled_probe_displacement y m hm i).2)
    (scaled_probe_signs y hy m hm).1 (scaled_probe_signs y hy m hm).2 hsign


theorem actual_chart_residual_bound (Q : MvPolynomial (Fin 14) ℝ)
    (hQdeg : Q.totalDegree ≤ 3) (hQc : ∀ d, |Q.coeff d| ≤ 1)
    (m : ℕ) (hm : 0 < m) (hsize : (2 : ℝ) ^ 60 ≤ m)
    (hsign : ∀ k : Fin 14 → Fin (m + 1),
      (0 < eval (fun i ↦ gridValue m (k i)) rawTarget ↔
        0 < eval (fun i ↦ gridValue m (k i)) Q))
    (y : Fin 13 → ℝ) (hy : ∀ i, y i ∈ chartGrid) :
    |eval (rawNode y) Q| < (2 : ℝ) ^ 67 / m :=
  chart_residual_bound Q hQdeg hQc PureCubicCoefficientBounds.rawTarget_coefficient_bound
    m hm hsize hsign y hy

theorem replicationCount_large :
    (2 : ℝ) ^ 60 ≤ PureRoPEReplication.replicationCount := by
  simp only [PureRoPEReplication.replicationCount, Nat.cast_pow, Nat.cast_ofNat]
  exact pow_le_pow_right₀ (by norm_num) (by decide)

end
end HeadComplexity.PureCubicSignProbe
