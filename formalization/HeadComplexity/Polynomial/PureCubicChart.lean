import HeadComplexity.Results.PureRoPEReplicationStrict
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option linter.style.header false

/-!
# Exact rational coordinate chart for the replicated pure cubic

These finite identities certify the coordinate inverse and its denominator and
row-norm bounds. They do not assert the quantitative Boolean lower bound.
-/

namespace HeadComplexity.PureCubicChart

noncomputable section

open PureRoPEReplication Matrix
open scoped BigOperators

/-- Coordinates are S0,S1,S2,B0,B1,B2,z7,...,z14. -/
def chart : Matrix (Fin 14) (Fin 14) ℝ :=
  ![baseS 0, baseS 1, baseS 2, baseB 0, baseB 1, baseB 2,
    fun i ↦ if i = 6 then 1 else 0,
    fun i ↦ if i = 7 then 1 else 0,
    fun i ↦ if i = 8 then 1 else 0,
    fun i ↦ if i = 9 then 1 else 0,
    fun i ↦ if i = 10 then 1 else 0,
    fun i ↦ if i = 11 then 1 else 0,
    fun i ↦ if i = 12 then 1 else 0,
    fun i ↦ if i = 13 then 1 else 0]

/-- Multiplying the inverse by 48 gives this integer matrix. -/
def inverseNumerator : Matrix (Fin 14) (Fin 14) ℤ :=
  ![![-100479375, -4176000, 2320000, -62000000000, 8000000000, -400000000, 48, 288,
      1008, 2688, 6048, 12096, 22176, 38016],
    ![421003125, 14040000, -9220000, 274000000000, -38000000000, 2000000000, -288, -1680,
      -5760, -15120, -33600, -66528, -120960, -205920],
    ![-703368750, -20320000, 14880000, -484000000000, 72000000000, -4000000000, 720, 4032,
      13440, 34560, 75600, 147840, 266112, 449280],
    ![596081250, 15840000, -12280000, 428000000000, -68000000000, 4000000000, -960, -5040,
      -16128, -40320, -86400, -166320, -295680, -494208],
    ![-260791875, -6480000, 5200000, -190000000000, 32000000000, -2000000000, 720, 3360, 10080,
      24192, 50400, 95040, 166320, 274560],
    ![48035625, 1096000, -900000, 34000000000, -6000000000, 400000000, -288, -1008, -2688,
      -6048, -12096, -22176, -38016, -61776],
    ![0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48]]

def chartInverse : Matrix (Fin 14) (Fin 14) ℝ :=
  fun i j ↦ (inverseNumerator i j : ℝ) / 48

set_option maxHeartbeats 8000000 in
-- The proof checks all 196 entries using exact rational arithmetic.
theorem chart_inverse_mul : chartInverse * chart = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, chartInverse,
      inverseNumerator, chart, baseS, baseB, Matrix.one_apply, Fin.ext_iff]

theorem chart_mul_inverse : chart * chartInverse = 1 := by
  exact mul_eq_one_comm.mp chart_inverse_mul

theorem inverse_denominator (i j : Fin 14) :
    ∃ k : ℤ, chartInverse i j = (k : ℝ) / 48 :=
  ⟨inverseNumerator i j, rfl⟩

theorem inverse_row_bound (i : Fin 14) :
    (∑ j, |chartInverse i j|) < (2 : ℝ) ^ 34 := by
  fin_cases i <;> norm_num [chartInverse, inverseNumerator, Fin.sum_univ_succ]

theorem inverse_first_column_bound (i : Fin 14) :
    |chartInverse i 0| < (2 : ℝ) ^ 24 := by
  fin_cases i <;> norm_num [chartInverse, inverseNumerator]

theorem inverse_apply (z : Fin 14 → ℝ) :
    chartInverse *ᵥ (chart *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, chart_inverse_mul, Matrix.one_mulVec]

theorem chart_apply_inverse (z : Fin 14 → ℝ) :
    chart *ᵥ (chartInverse *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, chart_mul_inverse, Matrix.one_mulVec]

end
end HeadComplexity.PureCubicChart
