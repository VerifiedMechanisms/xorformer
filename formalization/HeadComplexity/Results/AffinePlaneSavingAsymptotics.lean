import HeadComplexity.Results.AxisZeroAsymptotics
import HeadComplexity.Results.ReverseGridAxisRepair

set_option linter.style.header false

/-!
# Logarithmic saving from affine-plane grid compilers

This file contains the quantitative scale selection and the global asymptotic
transfer.  The finite compiler is an explicit argument until the construction
file supplies its checked theorem.
-/

namespace HeadComplexity
namespace AxisZeroGluing

open Filter Asymptotics
open scoped Topology

/-- The geometric sequence of affine-plane row capacities has bounded gaps. -/
theorem exists_affinePlaneScale (r : ℕ) (hr : 5 ≤ r) :
    ∃ a : ℕ, 2 ≤ a ∧ r ≤ a * 4 ^ a ∧ a * 4 ^ a ≤ 8 * r := by
  have hex : ∃ a : ℕ, r ≤ a * 4 ^ a := by
    refine ⟨r, ?_⟩
    have hp : 1 ≤ 4 ^ r := Nat.one_le_pow r 4 (by omega)
    nlinarith
  let a := Nat.find hex
  have hcap : r ≤ a * 4 ^ a := Nat.find_spec hex
  have ha : 2 ≤ a := by
    by_contra h
    have hsmall : a = 0 ∨ a = 1 := by omega
    rcases hsmall with h | h <;> simp [h] at hcap <;> omega
  have hpred : (a - 1) * 4 ^ (a - 1) < r := by
    have hnot := Nat.find_min hex (show a - 1 < a by omega)
    exact Nat.lt_of_not_ge hnot
  have hpow : 4 ^ a = 4 * 4 ^ (a - 1) := by
    calc
      4 ^ a = 4 ^ ((a - 1) + 1) := by congr 1; omega
      _ = 4 * 4 ^ (a - 1) := by rw [pow_succ, Nat.mul_comm]
  have ha2 : a ≤ 2 * (a - 1) := by omega
  have hmul := Nat.mul_le_mul_right (4 ^ (a - 1)) ha2
  refine ⟨a, ha, hcap, ?_⟩
  rw [hpow]
  nlinarith

/-- A capacity that covers half the dimension is at least a constant multiple
of its logarithm.  The loose constant keeps the finite proof elementary. -/
theorem log_dimension_le_affinePlaneScale {n a : ℕ}
    (hn : 2 ≤ n) (ha : 1 ≤ a) (hcap : n / 2 ≤ a * 4 ^ a) :
    Real.log n ≤ 5 * a := by
  have hhalf : n ≤ 3 * (n / 2) := by omega
  have haexp : a ≤ 2 ^ a := (Nat.lt_two_pow_self (n := a)).le
  have hfour : 3 ≤ 4 ^ a := by
    have h := Nat.pow_le_pow_right (by omega : 1 ≤ 4) ha
    norm_num at h ⊢
    omega
  have hnat : n ≤ 32 ^ a := by
    have hmul := Nat.mul_le_mul haexp hfour
    have hprod : 2 ^ a * 4 ^ a = 8 ^ a := by rw [← mul_pow]; norm_num
    rw [hprod] at hmul
    have hpow : 8 ^ a * 4 ^ a = 32 ^ a := by rw [← mul_pow]; norm_num
    rw [← hpow]
    nlinarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hreal : (n : ℝ) ≤ (32 : ℝ) ^ a := by exact_mod_cast hnat
  have hlog := Real.log_le_log hnpos hreal
  rw [Real.log_pow] at hlog
  have hlogtwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlog32 : Real.log 32 ≤ 5 := by
    have heq : (32 : ℝ) = 2 ^ (5 : ℕ) := by norm_num
    rw [heq, Real.log_pow]
    norm_num
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog32 (show (0 : ℝ) ≤ a by positivity)
  nlinarith

/-- The finite affine-plane budget, including exact axis repair, is logarithmic
in the number of available row coordinates. -/
theorem affinePlane_axis_budget {n a : ℕ}
    (hn : 10 ≤ n) (ha : 2 ≤ a)
    (hcap : n / 2 ≤ a * 4 ^ a) (hsize : a * 4 ^ a ≤ 8 * (n / 2)) :
    ((3 * (2 * 4 ^ a + 2 ^ a + 1) + 3 : ℕ) : ℝ) ≤
      600 * n / Real.log n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have htwo : 2 ^ a ≤ 4 ^ a := Nat.pow_le_pow_left (by norm_num) a
  have hone : 1 ≤ 4 ^ a := Nat.one_le_pow a 4 (by omega)
  have hhead : 3 * (2 * 4 ^ a + 2 ^ a + 1) + 3 ≤ 15 * 4 ^ a := by
    nlinarith
  have hbudgetnat : (3 * (2 * 4 ^ a + 2 ^ a + 1) + 3) * a ≤ 120 * n := by
    have hmul := Nat.mul_le_mul_right a hhead
    have hhalf : n / 2 ≤ n := Nat.div_le_self n 2
    nlinarith
  have hbudget :
      ((3 * (2 * 4 ^ a + 2 ^ a + 1) + 3 : ℕ) : ℝ) * a ≤ 120 * n := by
    exact_mod_cast hbudgetnat
  have hlog := log_dimension_le_affinePlaneScale (show 2 ≤ n by omega)
    (show 1 ≤ a by omega) hcap
  have hmul := mul_le_mul_of_nonneg_left hlog
    (show (0 : ℝ) ≤ ((3 * (2 * 4 ^ a + 2 ^ a + 1) + 3 : ℕ) : ℝ) by positivity)
  apply (le_div_iff₀ hlogpos).mpr
  nlinarith

/-- A compiler at affine-plane dimensions proves the full eventual logarithmic
saving against the original worst-case head complexity. -/
theorem worstCaseHeadComplexity_isBigO_log_of_affinePlaneCompiler
    (hcompiler : ∀ a r s : ℕ, 1 ≤ a → r ≤ a * 4 ^ a →
      HasStrictReverseGridCompiler r s (2 * 4 ^ a + 2 ^ a + 1)) :
    (fun n : ℕ ↦ (worstCaseHeadComplexity n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (2 : ℝ) ^ n / ((n : ℝ) * Real.log n)) := by
  apply worstCaseHeadComplexity_isBigO_of_compiler (K := 600) (by norm_num)
    (fun n ↦ Real.log n)
  filter_upwards [eventually_ge_atTop (10 : ℕ)] with n hn
  obtain ⟨a, ha, hcap, hsize⟩ := exists_affinePlaneScale (n / 2) (by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogle : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos hnpos
    linarith
  refine ⟨hlogpos, hlogle, 3 * (2 * 4 ^ a + 2 ^ a + 1) + 3, ?_, ?_⟩
  · exact hasReverseAxisCompiler_of_strictReverseGridCompiler
      (hcompiler a (n / 2) (n - n / 2) (by omega) hcap)
  · exact affinePlane_axis_budget hn ha hcap hsize

end AxisZeroGluing
end HeadComplexity
