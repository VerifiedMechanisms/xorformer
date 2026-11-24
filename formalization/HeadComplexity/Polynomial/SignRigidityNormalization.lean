import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option linter.style.header false

/-!
# The scalar recovered from a normalized sign polynomial is positive

These finite coefficient estimates check the normalization step in the
quantitative Boolean sign-rigidity argument. The all-one evaluation is the
sum of ordinary monomial coefficients.
-/

namespace HeadComplexity.SignRigidityNormalization

open scoped BigOperators

theorem scalar_abs_lower {ι : Type*} (F Q : ι → ℝ) (c e : ℝ)
    (hF : ∀ i, |F i| ≤ 1) (hQ : ∃ i, |Q i| = 1)
    (herr : ∀ i, |Q i - c * F i| ≤ e) : 1 - e ≤ |c| := by
  obtain ⟨i, hi⟩ := hQ
  have htriangle : |Q i| ≤ |Q i - c * F i| + |c * F i| := by
    simpa using abs_add_le (Q i - c * F i) (c * F i)
  have hmul : |c * F i| ≤ |c| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left (hF i) (abs_nonneg c)
  have herror := herr i
  rw [hi] at htriangle
  linarith

theorem sum_error_bound {ι : Type*} [Fintype ι] (F Q : ι → ℝ) (c e : ℝ)
    (herr : ∀ i, |Q i - c * F i| ≤ e) :
    |(∑ i, Q i) - c * ∑ i, F i| ≤ (Fintype.card ι : ℝ) * e := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |Q i - c * F i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, e := Finset.sum_le_sum (fun i _ ↦ herr i)
    _ = _ := by simp

theorem positive_scalar {ι : Type*} [Fintype ι] (F Q : ι → ℝ) (c e : ℝ)
    (he : 0 ≤ e) (hehalf : e ≤ 1 / 2)
    (hF : ∀ i, |F i| ≤ 1) (hQ : ∃ i, |Q i| = 1)
    (herr : ∀ i, |Q i - c * F i| ≤ e)
    (hgap : (Fintype.card ι : ℝ) * e < (∑ i, F i) / 2)
    (hpositive : 0 < ∑ i, Q i) : 1 / 2 ≤ c := by
  have habs := scalar_abs_lower F Q c e hF hQ herr
  have hsum := (abs_le.mp (sum_error_bound F Q c e herr)).2
  have hFsum : 0 < ∑ i, F i := by
    have hn : 0 ≤ (Fintype.card ι : ℝ) * e := mul_nonneg (Nat.cast_nonneg _) he
    linarith
  by_cases hc : 0 ≤ c
  · rw [abs_of_nonneg hc] at habs
    linarith
  · have hc' : c < 0 := lt_of_not_ge hc
    rw [abs_of_neg hc'] at habs
    have hcsmall : c ≤ -(1 / 2) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcsmall hFsum.le
    nlinarith

theorem division_error {ι : Type*} (F Q : ι → ℝ) (c e : ℝ)
    (hc : 1 / 2 ≤ c) (he : 0 ≤ e) (herr : ∀ i, |Q i - c * F i| ≤ e) (i : ι) :
    |Q i / c - F i| ≤ 2 * e := by
  have hcpos : 0 < c := by linarith
  have heq : Q i / c - F i = (Q i - c * F i) / c := by
    field_simp
  rw [heq, abs_div, abs_of_pos hcpos]
  apply (div_le_iff₀ hcpos).mpr
  have hm : (2 * e) * (1 / 2) ≤ (2 * e) * c :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  nlinarith [herr i]

end HeadComplexity.SignRigidityNormalization
