import HeadComplexity.Polynomial.PureCubicIrreducible
import HeadComplexity.Polynomial.PrimitiveGraphDivision

set_option linter.style.header false

/-!
# The exact rational-graph kernel of the separation cubic

Splitting off the first numerator coordinate makes the chart cubic primitive
linear over the remaining thirteen-variable polynomial ring. Restriction to
its rational graph therefore has kernel exactly the principal ideal generated
by the cubic. In total degree at most three, this kernel is its scalar span.
-/

namespace HeadComplexity.PureCubicGraphKernel

noncomputable section

open MvPolynomial PureCubicIrreducible

abbrev CoefficientRing := MvPolynomial (Fin 13) ℝ
abbrev RationalFunctions := FractionRing CoefficientRing

def leading : CoefficientRing := (1 + X 3) * (1 + X 4)

def trailing : CoefficientRing :=
  X 0 * (1 + X 2) * (1 + X 4) + X 1 * (1 + X 2) * (1 + X 3)

def split : MvPolynomial (Fin 14) ℝ ≃ₐ[ℝ] Polynomial CoefficientRing :=
  finSuccEquiv ℝ 13

theorem split_target : split coordinatePolynomial =
    Polynomial.C leading * Polynomial.X + Polynomial.C trailing := by
  have h₁ : split (X 1) = Polynomial.C (X 0) := finSuccEquiv_X_succ (R := ℝ) (n := 13) (j := 0)
  have h₂ : split (X 2) = Polynomial.C (X 1) := finSuccEquiv_X_succ (R := ℝ) (n := 13) (j := 1)
  have h₃ : split (X 3) = Polynomial.C (X 2) := finSuccEquiv_X_succ (R := ℝ) (n := 13) (j := 2)
  have h₄ : split (X 4) = Polynomial.C (X 3) := finSuccEquiv_X_succ (R := ℝ) (n := 13) (j := 3)
  have h₅ : split (X 5) = Polynomial.C (X 4) := finSuccEquiv_X_succ (R := ℝ) (n := 13) (j := 4)
  have h₀ : split (X 0) = Polynomial.X := finSuccEquiv_X_zero (R := ℝ) (n := 13)
  simp only [coordinatePolynomial, map_add, map_mul, map_one, h₀, h₁, h₂, h₃, h₄, h₅,
    leading, trailing]
  ring

theorem leading_ne_zero : leading ≠ 0 := by
  intro h
  have hh := congrArg (eval (fun _ : Fin 13 ↦ (0 : ℝ))) h
  norm_num [leading] at hh

theorem target_primitive :
    (Polynomial.C leading * Polynomial.X + Polynomial.C trailing).IsPrimitive := by
  have hirr := coordinatePolynomial_irreducible.map split
  rw [split_target] at hirr
  apply hirr.isPrimitive
  intro hdeg
  have hc := Polynomial.coeff_eq_zero_of_natDegree_lt (show
    (Polynomial.C leading * Polynomial.X + Polynomial.C trailing).natDegree < 1 by omega)
  apply leading_ne_zero
  simpa using hc

def graphRoot : RationalFunctions :=
  -(algebraMap CoefficientRing RationalFunctions trailing) /
    algebraMap CoefficientRing RationalFunctions leading

def restriction : MvPolynomial (Fin 14) ℝ →+* RationalFunctions :=
  (Polynomial.evalRingHom graphRoot).comp
    ((Polynomial.mapRingHom (algebraMap CoefficientRing RationalFunctions)).comp split.toRingHom)

theorem restriction_apply (Q : MvPolynomial (Fin 14) ℝ) : restriction Q =
    ((split Q).map (algebraMap CoefficientRing RationalFunctions)).eval graphRoot := rfl

theorem restriction_target : restriction coordinatePolynomial = 0 := by
  rw [restriction_apply, split_target]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have hA : algebraMap CoefficientRing RationalFunctions leading ≠ 0 := by
    intro h
    apply leading_ne_zero
    exact (IsFractionRing.injective CoefficientRing RationalFunctions) (by simpa using h)
  dsimp [graphRoot]
  field_simp
  ring

/-- Rational graph vanishing is exactly divisibility by the actual coordinate cubic. -/
theorem restriction_zero_iff_dvd (Q : MvPolynomial (Fin 14) ℝ) :
    restriction Q = 0 ↔ coordinatePolynomial ∣ Q := by
  constructor
  · intro h
    have hd := PrimitiveGraphDivision.primitive_linear_dvd_of_graph_zero
      (K := RationalFunctions) leading_ne_zero target_primitive (split Q) h
    rw [← split_target] at hd
    exact (map_dvd_iff split).mp hd
  · rintro ⟨T, rfl⟩
    rw [map_mul, restriction_target, zero_mul]

/-- The degree-at-most-three rational-graph kernel is the one-dimensional scalar span. -/
theorem degree_three_kernel (Q : MvPolynomial (Fin 14) ℝ) (hQ : Q.totalDegree ≤ 3) :
    restriction Q = 0 ↔ ∃ c : ℝ, Q = C c * coordinatePolynomial := by
  constructor
  · intro h
    exact eq_scalar_mul_of_dvd Q hQ ((restriction_zero_iff_dvd Q).mp h)
  · rintro ⟨c, rfl⟩
    rw [map_mul, restriction_target, mul_zero]

end

end HeadComplexity.PureCubicGraphKernel
