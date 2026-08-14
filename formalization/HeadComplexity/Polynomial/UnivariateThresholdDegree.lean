import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# Threshold degree through a real-valued statistic

`UnivariateThresholdDegLE t f K` records that a Boolean function `f` on an
arbitrary domain is strictly sign-represented by a real univariate polynomial
of degree at most `K` after applying the statistic `t`.

This is the polynomial-side interface used by weighted-atom upper bounds.  It
does not mention the Boolean cube, attention heads, or any particular choice of
statistic.
-/

namespace HeadComplexity

open Polynomial

universe u

/-- A degree-at-most-`K` univariate polynomial sign certificate for `f` through
the statistic `t`. -/
def UnivariateThresholdDegLE {α : Type u} (t : α → ℝ) (f : α → Bool) (K : ℕ) : Prop :=
  ∃ P : ℝ[X], P.natDegree ≤ K ∧ ∀ x, (0 < P.eval (t x) ↔ f x = true)

namespace UnivariateThresholdDegLE

variable {α : Type u} {t : α → ℝ} {f : α → Bool} {K L : ℕ}

/-- A univariate threshold-degree certificate remains valid at every larger
degree bound. -/
theorem mono (h : UnivariateThresholdDegLE t f K) (hKL : K ≤ L) :
    UnivariateThresholdDegLE t f L := by
  obtain ⟨P, hdeg, hsign⟩ := h
  exact ⟨P, hdeg.trans hKL, hsign⟩

end UnivariateThresholdDegLE

end HeadComplexity
