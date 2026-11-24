import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option linter.style.header false

/-!
An all-orders three-for-one projection-equivalent lift for affine directions
depending on one Boolean coordinate. This is a statement about signed direction
measures, not a relative-margin theorem for arbitrary head sums.
-/

noncomputable section
namespace HeadComplexity.OneCoordinateMomentLift
open Finset
open scoped BigOperators

variable {J : Type*} [Fintype J]

/-- Each original direction `(a,b)` is replaced by the axis-supported signed
triple `(a,0) + (0,a+b) - (0,a)`. -/
theorem scalar_kernel_identity (F : ℝ → ℝ) (a b : ℝ) (x : Bool) :
    F (a + b * (if x then 1 else 0)) =
      F a + F ((a+b) * (if x then 1 else 0)) -
        F (a * (if x then 1 else 0)) := by
  cases x <;> simp

theorem finite_kernel_identity (F : ℝ → ℝ) (c a b : J → ℝ) (x : Bool) :
    (∑ j, c j * F (a j + b j * (if x then 1 else 0))) =
      ∑ j, c j * (F (a j) + F ((a j+b j) * (if x then 1 else 0)) -
        F (a j * (if x then 1 else 0))) := by
  apply sum_congr rfl
  intro j _
  rw [scalar_kernel_identity F (a j) (b j) x]

/-- The two Boolean projection moment conditions imply every ordinary monomial
moment condition on the lifted support, at the same arbitrary order. -/
theorem ordinary_moment_zero (c a b : J → ℝ) (q : ℕ)
    (ha : ∀ k ≤ q, ∑ j, c j * (a j) ^ k = 0)
    (hab : ∀ k ≤ q, ∑ j, c j * (a j + b j) ^ k = 0)
    (r s : ℕ) (hrs : r + s ≤ q) :
    (∑ j, c j * ((a j)^r * (0:ℝ)^s +
      (0:ℝ)^r * (a j+b j)^s - (0:ℝ)^r * (a j)^s)) = 0 := by
  by_cases hs : s = 0
  · subst s
    simpa using ha r (by omega)
  by_cases hr : r = 0
  · subst r
    have h0 : ∑ j, c j = 0 := by simpa using ha 0 (by omega)
    simp only [pow_zero, one_mul, zero_pow hs, mul_zero,
      zero_add, mul_sub, sum_sub_distrib]
    rw [hab s (by omega), ha s (by omega)]
    ring
  · simp [zero_pow hs, zero_pow hr]

/-- Strictly positive replacement directions can be placed on two translated
axes, while preserving every scalar kernel. -/
theorem positive_axis_kernel_identity (F : ℝ → ℝ) (a b t : ℝ) (x : Bool) :
    F (a + b * (if x then 1 else 0)) =
      F (a + t * (if x then 1 else 0)) +
        F (t + (a+b-t) * (if x then 1 else 0)) -
        F (t + a * (if x then 1 else 0)) := by
  cases x
  · simp
  · simp only [ite_true, mul_one]
    have h1 : t + (a + b - t) = a + b := by ring
    rw [h1, add_comm t a]
    ring

/-- Choosing a baseline below the original intercepts preserves strict
positivity of all coordinates in the translated-axis construction. -/
theorem positive_axis_coordinates (a b t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (hta : t < a) :
    0 < a ∧ 0 < t ∧ 0 < a+b-t ∧ 0 < a := by
  exact ⟨ha, ht, by linarith, ha⟩

end HeadComplexity.OneCoordinateMomentLift
