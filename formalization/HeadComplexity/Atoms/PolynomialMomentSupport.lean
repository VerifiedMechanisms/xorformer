import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Polynomial moments and finite support

These lemmas audit the moment-annihilation step in the written homogeneous
polynomial rigidity argument. The analytic Laplace representation and the
complete factorization theorem are not formalized in this file.
-/

namespace HeadComplexity.PolynomialMomentSupport

open Polynomial MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Equality on all power moments extends to every real polynomial, even
when the comparison nodes are complex. -/
theorem polynomial_of_power_moments
    (L : ℝ[X] →ₗ[ℝ] ℂ) (z : ι → ℂ)
    (hMom : ∀ k : ℕ, L (X ^ k) = ∑ i, z i ^ k) (p : ℝ[X]) :
    L p = ∑ i, p.eval₂ Complex.ofRealHom (z i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, hp, hq, eval₂_add, Finset.sum_add_distrib]
  | monomial k a =>
      rw [← smul_X_eq_monomial, map_smul, hMom]
      simp only [smul_X_eq_monomial, eval₂_monomial, Complex.ofRealHom_eq_coe,
        Complex.real_smul, Finset.mul_sum]

/-- A polynomial vanishing at every comparison node annihilates its own
square under the moment functional. -/
theorem square_annihilation
    (L : ℝ[X] →ₗ[ℝ] ℂ) (z : ι → ℂ)
    (hMom : ∀ k : ℕ, L (X ^ k) = ∑ i, z i ^ k)
    (q : ℝ[X]) (hRoots : ∀ i, q.eval₂ Complex.ofRealHom (z i) = 0) :
    L (q ^ 2) = 0 := by
  rw [polynomial_of_power_moments L z hMom]
  simp [eval₂_pow, hRoots]

/-- A nonnegative square with zero integral vanishes on the measure support. -/
theorem support_subset_zero_set
    (μ : Measure ℝ) (q : ℝ[X])
    (hInt : Integrable (fun x : ℝ => (q.eval x) ^ 2) μ)
    (hZero : ∫ x : ℝ, (q.eval x) ^ 2 ∂μ = 0) :
    μ.support ⊆ {x : ℝ | q.eval x = 0} := by
  have hs : (fun x : ℝ => (q.eval x) ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hInt).mp hZero
  have hz : ∀ᵐ x ∂μ, q.eval x = 0 := by
    filter_upwards [hs] with x hx
    exact sq_eq_zero_iff.mp hx
  exact μ.support_subset_of_isClosed
    (isClosed_eq q.continuous continuous_const) hz

/-- The degree bounds every finite subset of that support. -/
theorem support_card_le_degree
    (μ : Measure ℝ) (q : ℝ[X]) (hq : q ≠ 0)
    (hInt : Integrable (fun x : ℝ => (q.eval x) ^ 2) μ)
    (hZero : ∫ x : ℝ, (q.eval x) ^ 2 ∂μ = 0)
    (s : Finset ℝ) (hs : (s : Set ℝ) ⊆ μ.support) :
    s.card ≤ q.natDegree := by
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  exact (Polynomial.mem_roots hq).mpr
    (support_subset_zero_set μ q hInt hZero (hs hx))

end HeadComplexity.PolynomialMomentSupport
