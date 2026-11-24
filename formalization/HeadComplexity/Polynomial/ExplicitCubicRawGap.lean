import HeadComplexity.Polynomial.CubicCoefficientHessian
import HeadComplexity.Polynomial.ExplicitCubicHessianGap

set_option linter.style.header false

/-!
# A uniform ordinary-coefficient gap for every oriented three-head cubic

This is the complete raw-coefficient component of the quantitative obstruction.
The subsequent recovery from squarefree coefficients and the finite Boolean
interpolation argument are separate steps.
-/

namespace HeadComplexity.ExplicitCubicRawGap
noncomputable section
open scoped BigOperators
open MvPolynomial GenericCubicHessianPullback PureRoPEReplication
open ExplicitCubicHessianGap

theorem linearPolynomial_homogeneous {n : ℕ} (a : Fin n → ℝ) :
    (linearPolynomial a).IsHomogeneous 1 := by
  apply IsHomogeneous.sum Finset.univ _ 1
  intro i _
  simpa using
    (isHomogeneous_C (Fin n) (a i) : (C (a i) : MvPolynomial (Fin n) ℝ).IsHomogeneous 0).mul
    (isHomogeneous_X ℝ i)

theorem cubic_homogeneous {n : ℕ} (S B : Fin 3 → Fin n → ℝ) :
    (cubic S B).IsHomogeneous 3 := by
  exact (((linearPolynomial_homogeneous (S 0)).mul
    (linearPolynomial_homogeneous (B 1))).mul (linearPolynomial_homogeneous (B 2))).add
    (((linearPolynomial_homogeneous (S 1)).mul
    (linearPolynomial_homogeneous (B 0))).mul (linearPolynomial_homogeneous (B 2))) |>.add
    (((linearPolynomial_homogeneous (S 2)).mul
    (linearPolynomial_homogeneous (B 0))).mul (linearPolynomial_homogeneous (B 1)))

/-- Some ordinary raw cubic coefficient is separated by the explicit uniform
radius, independently of all competing numerator and denominator magnitudes. -/
theorem raw_coefficient_gap (N E : Fin 3 → Fin 14 → ℝ)
    (hE : ∀ h, (∀ i, 0 < E h i) ∨ (∀ i, E h i < 0) ∨ E h = 0) :
    ∃ d : Fin 14 →₀ ℕ, rawGapScale / 2352 <
      |coeff d (cubic baseS baseB) - coeff d (cubic N E)| := by
  by_contra hn
  push Not at hn
  obtain ⟨w, hw, i, j, hij⟩ := oriented_cubic_hessian_gap_at_raw_scale N E hE
  have he : 0 ≤ rawGapScale / 2352 := div_nonneg rawGapScale_pos.le (by norm_num)
  have hb := CubicCoefficientHessian.hessian_difference_le
    (cubic baseS baseB) (cubic N E) (cubic_homogeneous _ _) (cubic_homogeneous _ _)
    (rawGapScale / 2352) he hn w hw i j
  have hid : 168 * (rawGapScale / 2352) = rawGapScale / 14 := by ring
  rw [hid] at hb
  exact (not_lt_of_ge hb) hij

/-- Absorbing an arbitrary readout preserves the same uniform gap. -/
theorem raw_coefficient_gap_with_readout (N E : Fin 3 → Fin 14 → ℝ) (c : ℝ)
    (hE : ∀ h, (∀ i, 0 < E h i) ∨ (∀ i, E h i < 0) ∨ E h = 0) :
    ∃ d : Fin 14 →₀ ℕ, rawGapScale / 2352 <
      |coeff d (cubic baseS baseB) - coeff d (cubic N E +
        C c * linearPolynomial (E 0) * linearPolynomial (E 1) * linearPolynomial (E 2))| := by
  rw [cubic_add_readout]
  exact raw_coefficient_gap _ E hE

end
end HeadComplexity.ExplicitCubicRawGap
