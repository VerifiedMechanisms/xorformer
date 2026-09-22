import HeadComplexity.Atoms.ClearedFeatureMatrix
import HeadComplexity.Polynomial.ModelToPolynomial
import HeadComplexity.Results.LowComplexity

set_option linter.style.header false

/-!
# Integral cleared-score certificates

This module is the analytic boundary for finite exact certificate checkers.
All certificate data live over the integers.  A denominator may have either
strictly positive slopes, or strictly negative slopes with a positive cube
margin.  Both orientations compile to one fractional atom.

The finite checker only has to establish integer inequalities and identities.
No floating-point or externally verified conclusion crosses this boundary.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n H : ℕ}

/-- An integral affine denominator in one of the two orientations realizable
by a fractional atom. -/
structure IntegralOrientedDenominator (n : ℕ) where
  constant : ℤ
  coefficient : Fin n → ℤ
  orientation :
    (0 < constant ∧ ∀ i, 0 < coefficient i) ∨
      (0 < constant ∧ (∀ i, coefficient i < 0) ∧
        ∑ i, -coefficient i < constant)

namespace IntegralOrientedDenominator

/-- The exact integer value of a denominator on a cube point. -/
def value (D : IntegralOrientedDenominator n)
    (bits : Fin n → Bool) : ℤ :=
  semiringAffineValue D.constant D.coefficient bits

/-- The corresponding real affine value. -/
noncomputable def realValue (D : IntegralOrientedDenominator n)
    (bits : Fin n → Bool) : ℝ :=
  affineValue (D.constant : ℝ) (fun i ↦ (D.coefficient i : ℝ)) bits

@[simp] theorem cast_value (D : IntegralOrientedDenominator n)
    (bits : Fin n → Bool) :
    (D.value bits : ℝ) = D.realValue bits := by
  rw [value, realValue, ← semiringAffineValue_real]
  exact map_semiringAffineValue (Int.castRingHom ℝ)
    D.constant D.coefficient bits

/-- The positive-slope alternative of denominator orientation. -/
def IsPositive (D : IntegralOrientedDenominator n) : Prop :=
  0 < D.constant ∧ ∀ i, 0 < D.coefficient i

/-- The negative-slope alternative of denominator orientation. -/
def IsNegative (D : IntegralOrientedDenominator n) : Prop :=
  0 < D.constant ∧ (∀ i, D.coefficient i < 0) ∧
    ∑ i, -D.coefficient i < D.constant

/-- The atom realizing an arbitrary affine numerator divided by this
denominator. -/
noncomputable def atom (D : IntegralOrientedDenominator n)
    (numConstant : ℤ) (numCoefficient : Fin n → ℤ) : FracAtom n := by
  classical
  by_cases hpos : D.IsPositive
  · exact FracAtom.ofPositiveAffineRatio (numConstant : ℝ)
      (fun i ↦ (numCoefficient i : ℝ)) (D.constant : ℝ)
      (fun i ↦ (D.coefficient i : ℝ))
      (by exact_mod_cast hpos.1) (fun i ↦ by exact_mod_cast hpos.2 i)
  · have hor : D.IsPositive ∨ D.IsNegative := D.orientation
    have hneg : D.IsNegative := hor.resolve_left hpos
    exact FracAtom.ofNegativeAffineRatio (numConstant : ℝ)
      (fun i ↦ (numCoefficient i : ℝ)) (D.constant : ℝ)
      (fun i ↦ (D.coefficient i : ℝ))
      (by exact_mod_cast hneg.1) (fun i ↦ by exact_mod_cast hneg.2.1 i)
      (by exact_mod_cast hneg.2.2)

/-- Evaluation of the compiled atom is exactly the prescribed affine ratio. -/
theorem atom_eval (D : IntegralOrientedDenominator n)
    (numConstant : ℤ) (numCoefficient : Fin n → ℤ)
    (bits : Fin n → Bool) :
    (D.atom numConstant numCoefficient).eval bits =
      affineValue (numConstant : ℝ) (fun i ↦ (numCoefficient i : ℝ)) bits /
        D.realValue bits := by
  classical
  unfold atom
  by_cases hpos : D.IsPositive
  · simp only [hpos, ↓reduceDIte]
    exact FracAtom.ofPositiveAffineRatio_eval _ _ _ _ _ _ bits
  · simp only [hpos, ↓reduceDIte]
    exact FracAtom.ofNegativeAffineRatio_eval _ _ _ _ _ _ _ bits

/-- Every oriented denominator is strictly positive on the Boolean cube. -/
theorem realValue_pos (D : IntegralOrientedDenominator n)
    (bits : Fin n → Bool) : 0 < D.realValue bits := by
  rcases D.orientation with hpos | hneg
  · exact affineValue_pos _ _ (by exact_mod_cast hpos.1)
      (fun i ↦ by exact_mod_cast hpos.2 i) bits
  · let phi := FracAtom.ofNegativeAffineRatio (0 : ℝ) (fun _ ↦ 0)
      (D.constant : ℝ) (fun i ↦ (D.coefficient i : ℝ))
      (by exact_mod_cast hneg.1)
      (fun i ↦ by exact_mod_cast hneg.2.1 i)
      (by exact_mod_cast hneg.2.2)
    have hphi := phi.denom_pos bits
    rw [FracAtom.ofNegativeAffineRatio_denom] at hphi
    exact hphi

end IntegralOrientedDenominator

/-- Integer evaluation of a denominator-cleared score.  The coefficient order
is a bias followed by one affine numerator for each denominator. -/
def integralClearedScore
    (denominator : Fin H → IntegralOrientedDenominator n)
    (bias : ℤ) (numConstant : Fin H → ℤ)
    (numCoefficient : Fin H → Fin n → ℤ)
    (bits : Fin n → Bool) : ℤ :=
  bias * ∏ h, (denominator h).value bits +
    ∑ h, semiringAffineValue (numConstant h) (numCoefficient h) bits *
      ∏ g ∈ Finset.univ.erase h, (denominator g).value bits

/-- A fully exact cleared-score sign certificate. -/
structure IntegralClearedScoreCertificate
    (n H : ℕ) (f : (Fin n → Bool) → Bool) where
  denominator : Fin H → IntegralOrientedDenominator n
  bias : ℤ
  numConstant : Fin H → ℤ
  numCoefficient : Fin H → Fin n → ℤ
  represents : ∀ bits,
    (0 < integralClearedScore denominator bias numConstant numCoefficient bits ↔
      f bits = true) ∧
    integralClearedScore denominator bias numConstant numCoefficient bits ≠ 0

namespace IntegralClearedScoreCertificate

private theorem cast_score
    (C : IntegralClearedScoreCertificate n H f)
    (bits : Fin n → Bool) :
    (integralClearedScore C.denominator C.bias C.numConstant
        C.numCoefficient bits : ℝ) =
      (C.bias : ℝ) * ∏ h, (C.denominator h).realValue bits +
        ∑ h,
          affineValue (C.numConstant h) (fun i ↦ (C.numCoefficient h i : ℝ)) bits *
            ∏ g ∈ Finset.univ.erase h,
              (C.denominator g).realValue bits := by
  rw [integralClearedScore, Int.cast_add, Int.cast_mul, Int.cast_prod]
  simp_rw [IntegralOrientedDenominator.cast_value]
  rw [Int.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [Int.cast_mul, Int.cast_prod, ← semiringAffineValue_real]
  simp_rw [IntegralOrientedDenominator.cast_value]
  congr 1
  exact map_semiringAffineValue (Int.castRingHom ℝ)
    (C.numConstant h) (C.numCoefficient h) bits

/-- An integral cleared-score certificate compiles to exactly one head per
denominator. -/
theorem computable (C : IntegralClearedScoreCertificate n H f) :
    computableWithHeadsN n H f := by
  classical
  let phi : Fin H → FracAtom n := fun h ↦
    (C.denominator h).atom (C.numConstant h) (C.numCoefficient h)
  apply computable_of_fracComputable
  refine ⟨phi, C.bias, fun bits ↦ ?_⟩
  let D : Fin H → ℝ := fun h ↦ (C.denominator h).realValue bits
  let N : Fin H → ℝ := fun h ↦
    affineValue (C.numConstant h) (fun i ↦ (C.numCoefficient h i : ℝ)) bits
  have hDpos : ∀ h, 0 < D h := fun h ↦
    (C.denominator h).realValue_pos bits
  have hDne : ∀ h, D h ≠ 0 := fun h ↦ (hDpos h).ne'
  have hprodpos : 0 < ∏ h, D h := Finset.prod_pos fun h _ ↦ hDpos h
  have hfactor : ∀ h, (∏ g, D g) = D h * ∏ g ∈ Finset.univ.erase h, D g :=
    fun h ↦ (Finset.mul_prod_erase Finset.univ D (Finset.mem_univ h)).symm
  have hclear :
      ((C.bias : ℝ) + ∑ h, N h / D h) * ∏ h, D h =
        (C.bias : ℝ) * ∏ h, D h +
          ∑ h, N h * ∏ g ∈ Finset.univ.erase h, D g := by
    rw [add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    rw [hfactor h]
    field_simp [hDne h]
  let score : ℤ := integralClearedScore C.denominator C.bias
    C.numConstant C.numCoefficient bits
  have hscore :
      (C.bias : ℝ) + ∑ h, N h / D h = (score : ℝ) / ∏ h, D h := by
    apply (eq_div_iff hprodpos.ne').2
    rw [hclear]
    exact (C.cast_score bits).symm
  have hphi : ∀ h, (phi h).eval bits = N h / D h := by
    intro h
    exact (C.denominator h).atom_eval
      (C.numConstant h) (C.numCoefficient h) bits
  simp_rw [hphi]
  rw [hscore, div_pos_iff_of_pos_right hprodpos]
  exact_mod_cast (C.represents bits).1

/-- The certificate directly gives the corresponding head-complexity upper
bound. -/
theorem HStar_le (C : IntegralClearedScoreCertificate n H f) :
    HStar n f ≤ H :=
  HStar_le_of_computableWithHeadsN C.computable

/-- The same certificate supplies a degree-at-most-`H` sign polynomial through
the general head-to-polynomial compiler. -/
theorem thresholdDegLE (C : IntegralClearedScoreCertificate n H f) :
    ThresholdDegLE f H :=
  signReprDegLe_of_computableWithHeadsN C.computable

end IntegralClearedScoreCertificate

end HeadComplexity
