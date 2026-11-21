import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exact inequalities for a dominant-power construction

These lemmas certify the numerical lifting step of the tropical search.
They do not assert that the required exponent inequalities can be solved
for every Boolean function at any particular head count.
-/

namespace HeadComplexity

open scoped BigOperators

variable {ι κ : Type*}

/-- A sum of positive powers is bounded by its largest power times the
number of summands. The exponent maximum is supplied explicitly. -/
theorem sum_zpow_bounds (s : Finset ι) (b : ι → ℤ) (T : ℝ)
    (hT : 1 ≤ T) (d : ℤ) (hd : ∀ i ∈ s, b i ≤ d)
    (hw : ∃ i ∈ s, b i = d) :
    T ^ d ≤ ∑ i ∈ s, T ^ b i ∧
      (∑ i ∈ s, T ^ b i) ≤ (s.card : ℝ) * T ^ d := by
  have hpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  constructor
  · obtain ⟨i, hi, hbi⟩ := hw
    rw [← hbi]
    exact Finset.single_le_sum (fun j _ ↦ (zpow_pos hpos _).le) hi
  · calc
      _ ≤ ∑ _i ∈ s, T ^ d :=
        Finset.sum_le_sum (fun i hi ↦ zpow_le_zpow_right₀ hT (hd i hi))
      _ = (s.card : ℝ) * T ^ d := by simp

/-- Bounds for one unsigned contribution to an affine fraction. -/
theorem zpow_div_bounds (T K B : ℝ) (a d : ℤ)
    (hT : 0 < T)
    (hBlo : T ^ d ≤ B) (hBhi : B ≤ K * T ^ d) :
    T ^ (a - d) / K ≤ T ^ a / B ∧ T ^ a / B ≤ T ^ (a - d) := by
  have hd : 0 < T ^ d := zpow_pos hT _
  have hB : 0 < B := hd.trans_le hBlo
  have ha : 0 < T ^ a := zpow_pos hT _
  rw [zpow_sub₀ hT.ne']
  constructor
  · calc
      T ^ a / T ^ d / K = T ^ a / (K * T ^ d) := by ring
      _ ≤ T ^ a / B := div_le_div_of_nonneg_left ha.le hB hBhi
  · exact div_le_div_of_nonneg_left ha.le hd hBlo

/-- One winning power dominates any specified finite number of terms
whose exponents are at least one smaller. -/
theorem zpow_winner_dominates_sum
    (s : Finset ι) (v : ι → ℝ) (T K : ℝ) (E : ℤ)
    (hT : 0 < T) (hK : 0 < K)
    (hv : ∀ i ∈ s, v i ≤ T ^ (E - 1))
    (hsize : K * (s.card : ℝ) < T) :
    (∑ i ∈ s, v i) < T ^ E / K := by
  have hp : 0 < T ^ (E - 1) := zpow_pos hT _
  have hpow : T ^ E = T * T ^ (E - 1) := by
    calc
      T ^ E = T ^ (1 + (E - 1)) := by congr 1; omega
      _ = T ^ (1 : ℤ) * T ^ (E - 1) := zpow_add₀ hT.ne' _ _
      _ = T * T ^ (E - 1) := by rw [zpow_one]
  calc
    _ ≤ ∑ _i ∈ s, T ^ (E - 1) := Finset.sum_le_sum hv
    _ = (s.card : ℝ) * T ^ (E - 1) := by simp
    _ < T ^ E / K := by
      apply (lt_div_iff₀ hK).mpr
      rw [hpow]
      nlinarith

/-- The abstract exact lift: a positive contribution at the winning
level exceeds the whole opposing sum. All additional positive terms
may be retained. -/
theorem positive_of_dominant_power
    (positiveTerms : Finset ι) (negativeTerms : Finset κ)
    (p : ι → ℝ) (m : κ → ℝ) (T K : ℝ) (E : ℤ)
    (hT : 0 < T) (hK : 0 < K)
    (hp : ∀ i ∈ positiveTerms, 0 ≤ p i)
    (hw : ∃ i ∈ positiveTerms, T ^ E / K ≤ p i)
    (hm : ∀ i ∈ negativeTerms, m i ≤ T ^ (E - 1))
    (hsize : K * (negativeTerms.card : ℝ) < T) :
    0 < (∑ i ∈ positiveTerms, p i) - ∑ i ∈ negativeTerms, m i := by
  obtain ⟨i, hi, hpi⟩ := hw
  have hsum : T ^ E / K ≤ ∑ j ∈ positiveTerms, p j :=
    hpi.trans (Finset.single_le_sum hp hi)
  have hneg := zpow_winner_dominates_sum negativeTerms m T K E hT hK hm hsize
  linarith

end HeadComplexity
