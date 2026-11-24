import HeadComplexity.Results.JointFamilyScalarCapacity

set_option linter.style.header false

/-!
# Polynomial reduction for a common affine denominator statistic

If all reciprocal heads use the same scalar statistic, clearing their
positive denominators leaves a linear combination of fixed input features
times univariate polynomials of degree at most the number of heads.

The companion written note applies an external multidegree sign-count
theorem. That counting theorem and its asymptotic consequence are not
formalized here.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

/-- Clearing common-statistic denominators preserves linearity in all
numerator features. The statistic and the features can be arbitrary. -/
theorem jointFamily_common_statistic_clearing
    (pole : I → ℝ) (residue : I → J → ℝ) (bias feature : J → ℝ)
    (t : ℝ) (hden : ∀ h, pole h - t ≠ 0) :
    (∑ j, feature j *
      (jointFamilyCauchyPolynomial Finset.univ pole (fun h ↦ residue h j) (bias j)).eval t) =
      (∏ h, (pole h - t)) *
        ((∑ j, feature j * bias j) +
          ∑ h, (∑ j, feature j * residue h j) / (pole h - t)) := by
  classical
  simp_rw [jointFamilyCauchyPolynomial_eval Finset.univ pole _ _ t
    (fun h _ ↦ hden h)]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_div, mul_div_assoc]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro j _
    ring

omit [Fintype J] in
/-- The preceding polynomials have degree at most the number of heads,
independently of pole positions and numerator feature values. -/
theorem jointFamily_common_statistic_polynomial_degree
    (pole : I → ℝ) (residue : I → J → ℝ) (bias : J → ℝ) (j : J) :
    (jointFamilyCauchyPolynomial Finset.univ pole
      (fun h ↦ residue h j) (bias j)).natDegree ≤ Fintype.card I := by
  simpa using jointFamilyCauchyPolynomial_degree Finset.univ pole
    (fun h ↦ residue h j) (bias j)

/-- Positivity is charged at every input where this reduction is used:
the cleared polynomial expression has exactly the same strict sign. -/
theorem jointFamily_common_statistic_strict_sign
    (pole : I → ℝ) (residue : I → J → ℝ) (bias feature : J → ℝ)
    (t σ : ℝ) (hden : ∀ h, 0 < pole h - t) :
    (0 < σ * (∑ j, feature j *
      (jointFamilyCauchyPolynomial Finset.univ pole (fun h ↦ residue h j) (bias j)).eval t)) ↔
    0 < σ * ((∑ j, feature j * bias j) +
      ∑ h, (∑ j, feature j * residue h j) / (pole h - t)) := by
  rw [jointFamily_common_statistic_clearing pole residue bias feature t
    (fun h ↦ ne_of_gt (hden h))]
  have hp : 0 < ∏ h, (pole h - t) := Finset.prod_pos (fun h _ ↦ hden h)
  rw [mul_left_comm σ]
  exact mul_pos_iff_of_pos_left hp

end HeadComplexity.AxisZeroGluing
