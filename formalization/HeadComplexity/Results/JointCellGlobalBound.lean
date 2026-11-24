import HeadComplexity.Results.JointCellRankRepair
import HeadComplexity.Results.AffinePlaneSavingAsymptotics

set_option linter.style.header false

/-!
# Global consequence of joint local axis repair

The shared cancellation within each local table improves the explicit constant
in the inherited logarithmic upper bound. This does not establish a growing
saving across independent tables or a stronger asymptotic order.
-/

namespace HeadComplexity
namespace AxisZeroGluing

private theorem three_mul_le_four_pow {a : ℕ} (ha : 1 ≤ a) : 3 * a ≤ 4 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ a ha ih =>
      rw [pow_succ]
      nlinarith

/-- A tighter elementary scale estimate suffices for the improved constant. -/
theorem jointPlane_log_dimension_le_scale {n a : ℕ}
    (hn : 2 ≤ n) (ha : 1 ≤ a) (hcap : n / 2 ≤ a * 4 ^ a) :
    Real.log n ≤ 3 * a := by
  have hhalf : n ≤ 3 * (n / 2) := by omega
  have hpower := three_mul_le_four_pow ha
  have hnat : n ≤ 16 ^ a := by
    have heq : 4 ^ a * 4 ^ a = 16 ^ a := by rw [← mul_pow]; norm_num
    rw [← heq]
    nlinarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hreal : (n : ℝ) ≤ (16 : ℝ) ^ a := by exact_mod_cast hnat
  have hlog := Real.log_le_log hnpos hreal
  rw [Real.log_pow] at hlog
  have hlogtwo : Real.log 2 ≤ (3 / 4 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hlog16 : Real.log 16 ≤ 3 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog16 (show (0 : ℝ) ≤ a by positivity)
  nlinarith

/-- Complete local budget after sharing the axis cancellations within a table. -/
theorem jointPlane_axis_budget {n a : ℕ}
    (hn : 10 ≤ n) (ha : 2 ≤ a)
    (hcap : n / 2 ≤ a * 4 ^ a) (hsize : a * 4 ^ a ≤ 8 * (n / 2)) :
    ((3 * 4 ^ a + 4 : ℕ) : ℝ) ≤ 39 * n / Real.log n := by
  have hlogpos : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hpow : 16 ≤ 4 ^ a := by
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ (4 : ℕ)) ha
    norm_num at this
    exact this
  have hhead : 4 * (3 * 4 ^ a + 4) ≤ 13 * 4 ^ a := by omega
  have hbudgetnat : (3 * 4 ^ a + 4) * a ≤ 13 * n := by
    have hmul := Nat.mul_le_mul_right a hhead
    have hhalf : 2 * (n / 2) ≤ n := by omega
    nlinarith
  have hbudget : ((3 * 4 ^ a + 4 : ℕ) : ℝ) * a ≤ 13 * n := by
    exact_mod_cast hbudgetnat
  have hlog := jointPlane_log_dimension_le_scale (show 2 ≤ n by omega)
    (show 1 ≤ a by omega) hcap
  have hmul := mul_le_mul_of_nonneg_left hlog
    (show (0 : ℝ) ≤ ((3 * 4 ^ a + 4 : ℕ) : ℝ) by positivity)
  apply (le_div_iff₀ hlogpos).mpr
  nlinarith

end AxisZeroGluing

open AxisZeroGluing

/-- An unconditional constant improvement, including cover overlaps, exact axis
repair, all exceptional faces, and original-model admissibility. -/
theorem worstCaseHeadComplexity_real_le_joint_log_saving {n : ℕ} (hn : 32 ≤ n) :
    (worstCaseHeadComplexity n : ℝ) ≤
      151010 * (2 : ℝ) ^ n / ((n : ℝ) * Real.log n) := by
  obtain ⟨a, ha, hcap, hsize⟩ := exists_affinePlaneScale (n / 2) (by omega)
  have hcomp := hasReverseAxisCompiler_affinePlane_joint a (n / 2) (n - n / 2)
    (by omega) hcap
  have hbudget := jointPlane_axis_budget (show 10 ≤ n by omega) ha hcap hsize
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogle : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos hnpos
    linarith
  have h := worstCaseHeadComplexity_balanced_le hn (K := 39) (by norm_num)
    hlogpos hlogle hcomp hbudget
  norm_num at h ⊢
  exact h

end HeadComplexity
