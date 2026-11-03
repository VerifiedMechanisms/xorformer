import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Instances.Rat

set_option linter.style.header false

/-! # Rational witnesses for finite strict polynomial systems -/

namespace HeadComplexity

open MvPolynomial

/-- A feasible finite system of strict polynomial inequalities has a rational
parameter witness. Polynomial coefficients may even be arbitrary reals. -/
theorem exists_rational_strict_polynomial_witness {I K : Type*} [Finite I]
    (P : I → MvPolynomial K ℝ) (point : K → ℝ)
    (hpoint : ∀ i, 0 < eval point (P i)) :
    ∃ rational : K → ℚ, ∀ i, 0 < eval (fun k ↦ (rational k : ℝ)) (P i) := by
  have hopen : IsOpen {x : K → ℝ | ∀ i, 0 < eval x (P i)} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (P i).continuous_eval
  have hdense : DenseRange (fun rational : K → ℚ ↦ fun k ↦ (rational k : ℝ)) :=
    DenseRange.piMap fun _ ↦ Rat.denseRange_cast
  obtain ⟨_, ⟨rational, rfl⟩, h⟩ := Dense.exists_mem_open hdense hopen ⟨point, hpoint⟩
  exact ⟨rational, h⟩

end HeadComplexity
