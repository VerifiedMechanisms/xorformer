import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

set_option linter.style.header false

noncomputable section
namespace HeadComplexity.NegativeObservationBinomial
open Finset
open scoped BigOperators

/-- The binomial generating function evaluated at one half. -/
theorem binomial_half (n : ℕ) :
    (∑ r ∈ range (n+1), (n.choose r : ℝ) * (1/2 : ℝ)^r) = (3/2 : ℝ)^n := by
  have hh := (add_pow (1/2 : ℝ) 1 n).symm
  norm_num [mul_comm] at hh ⊢
  exact hh

/-- Exact algebra in the exceptional-set expectation. No probability
measure or independence premise is built into this declaration. -/
theorem weighted_binomial_half (n : ℕ) :
    (∑ r ∈ range (n+1), (n.choose r : ℝ) * (1+(r : ℝ)) * (1/2 : ℝ)^r) =
      (1+(n : ℝ)/3) * (3/2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hs := sum_choose_succ_mul
      (fun r _ : ℕ => (1+(r : ℝ)) * (1/2 : ℝ)^r) n
    have hterm (r : ℕ) :
        (n.choose r : ℝ) * ((1+((r+1 : ℕ) : ℝ)) * (1/2 : ℝ)^(r+1)) =
          (1/2 : ℝ) * ((n.choose r : ℝ) * (1+(r : ℝ)) * (1/2 : ℝ)^r) +
          (1/2 : ℝ) * ((n.choose r : ℝ) * (1/2 : ℝ)^r) := by
      push_cast
      rw [pow_succ]
      ring
    simp only [hterm, sum_add_distrib, ← mul_sum] at hs
    simp only [← mul_assoc] at hs
    change (∑ r ∈ range (n+2), ((n+1).choose r : ℝ) * (1+(r : ℝ)) * (1/2 : ℝ)^r) = _
    rw [hs, ih, binomial_half]
    push_cast
    rw [pow_succ]
    ring

/-- Reflection of a binomially weighted sum. -/
theorem binomial_reflection (n : ℕ) (f : ℕ → ℝ) :
    (∑ r ∈ range (n+1), (n.choose r : ℝ) * f (n-r)) =
      ∑ r ∈ range (n+1), (n.choose r : ℝ) * f r := by
  calc
    _ = ∑ r ∈ range (n+1), (n.choose (n-r) : ℝ) * f (n-r) := by
      apply sum_congr rfl
      intro r hr
      rw [Nat.choose_symm (Nat.lt_succ_iff.mp (mem_range.mp hr))]
    _ = _ := by simpa using sum_range_reflect (fun r => (n.choose r : ℝ) * f r) (n+1)

/-- The complete downward-plus-upward binomial sum, before using symmetry. -/
theorem full_independent_sum (n : ℕ) :
    (∑ r ∈ range (n+1), (n.choose r : ℝ) *
      ((1+(r : ℝ)) * (1/2 : ℝ)^r +
        (1+((n-r : ℕ) : ℝ)) * (1/2 : ℝ)^(n-r))) =
      2*(1+(n : ℝ)/3)*(3/2 : ℝ)^n := by
  simp only [mul_add, sum_add_distrib]
  rw [binomial_reflection n (fun r => (1+(r : ℝ)) * (1/2 : ℝ)^r)]
  simp only [← mul_assoc]
  rw [weighted_binomial_half]
  ring

/-- The symmetric union bound for independent half-observations. -/
theorem two_sided_independent_sum (n : ℕ) :
    2 * (∑ r ∈ range (n+1), (n.choose r : ℝ) * (1+(r : ℝ)) * (1/2 : ℝ)^r) =
      2*(1+(n : ℝ)/3)*(3/2 : ℝ)^n := by
  rw [weighted_binomial_half]
  ring

/-- The slightly looser exact algebra used for sampling an exactly
balanced half of the cube without replacement. -/
theorem balanced_binomial_half (n : ℕ) :
    (∑ r ∈ range (n+1), (n.choose r : ℝ) * (1+2*(r : ℝ)) * (1/2 : ℝ)^r) =
      (1+2*(n : ℝ)/3)*(3/2 : ℝ)^n := by
  have hterm (r : ℕ) :
      (n.choose r : ℝ) * (1+2*(r : ℝ)) * (1/2 : ℝ)^r =
        2*((n.choose r : ℝ) * (1+(r : ℝ)) * (1/2 : ℝ)^r) -
          (n.choose r : ℝ) * (1/2 : ℝ)^r := by ring
  simp_rw [hterm]
  rw [sum_sub_distrib, ← mul_sum, weighted_binomial_half, binomial_half]
  ring

end HeadComplexity.NegativeObservationBinomial
