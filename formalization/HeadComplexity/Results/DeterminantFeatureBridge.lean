import HeadComplexity.Atoms.ClearedFeatureMatrix
import HeadComplexity.Results.DeterminantSpan

set_option linter.style.header false

/-!
# Determinant feature matrices imply universal cleared spans

A square selection of cleared affine-denominator features is a universal basis
when its value matrix has nonzero determinant.  This module turns that finite
matrix premise into the existing `ClearedSpanCertificate` interface and hence
into a universal head-complexity bound.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n H : ℕ}

/-- Positive affine denominators, a square feature selection, and a checked
nonzero real determinant. -/
structure ClearedFeatureDeterminantCertificate (n H : ℕ) where
  denConst : Fin H → ℝ
  denCoeff : Fin H → Fin n → ℝ
  denConst_pos : ∀ h, 0 < denConst h
  denCoeff_pos : ∀ h i, 0 < denCoeff h i
  selected : BooleanCubeIndex n → ClearedFeatureIndex n H
  det_ne_zero :
    (clearedFeatureMatrix denConst denCoeff selected).det ≠ 0

namespace ClearedFeatureDeterminantCertificate

/-- The square matrix carried by a determinant certificate. -/
noncomputable abbrev matrix (C : ClearedFeatureDeterminantCertificate n H) :=
  clearedFeatureMatrix C.denConst C.denCoeff C.selected

private theorem selected_spans
    (C : ClearedFeatureDeterminantCertificate n H)
    (target : (Fin n → Bool) → ℝ) :
    ∃ coefficient : ClearedFeatureIndex n H → ℝ,
      ∀ bits,
        target bits = ∑ feature, coefficient feature *
          clearedFeatureValue C.denConst C.denCoeff feature bits := by
  classical
  have hunitDet : IsUnit C.matrix.det :=
    isUnit_iff_ne_zero.mpr C.det_ne_zero
  have hunit : IsUnit C.matrix :=
    (Matrix.isUnit_iff_isUnit_det C.matrix).mpr hunitDet
  have hsurjective : Function.Surjective C.matrix.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hunit
  obtain ⟨selectedCoefficient, hselectedCoefficient⟩ :=
    hsurjective (fun row ↦ target ((booleanCubeEquivFin n).symm row))
  let coefficient : ClearedFeatureIndex n H → ℝ := fun feature ↦
    ∑ column, if C.selected column = feature then selectedCoefficient column else 0
  refine ⟨coefficient, fun bits ↦ ?_⟩
  have hselected :
      target bits = ∑ column, selectedCoefficient column *
        clearedFeatureValue C.denConst C.denCoeff (C.selected column) bits := by
    have hrow := congrFun hselectedCoefficient ((booleanCubeEquivFin n) bits)
    rw [Matrix.mulVec] at hrow
    simpa [matrix, clearedFeatureMatrix, dotProduct, mul_comm] using hrow.symm
  rw [hselected]
  symm
  unfold coefficient
  rw [show
      (∑ feature, (∑ column,
          if C.selected column = feature then selectedCoefficient column else 0) *
          clearedFeatureValue C.denConst C.denCoeff feature bits) =
        ∑ column, selectedCoefficient column *
          clearedFeatureValue C.denConst C.denCoeff (C.selected column) bits by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro column _
    simp]

/-- A nonsingular selected feature matrix supplies the existing universal
cleared-span certificate. -/
noncomputable def toClearedSpanCertificate
    (C : ClearedFeatureDeterminantCertificate n H) :
    ClearedSpanCertificate n H where
  denConst := C.denConst
  denCoeff := C.denCoeff
  denConst_pos := C.denConst_pos
  denCoeff_pos := C.denCoeff_pos
  spans := by
    intro target
    obtain ⟨coefficient, hcoefficient⟩ := C.selected_spans target
    refine ⟨coefficient none,
      fun h ↦ coefficient (some (h, none)),
      fun h i ↦ coefficient (some (h, some i)), fun bits ↦ ?_⟩
    rw [hcoefficient bits,
      sum_clearedFeatureValue C.denConst C.denCoeff coefficient bits]
    simp only [semiringAffineValue_real]

/-- Every Boolean function is computable with the certified head count. -/
theorem computable (C : ClearedFeatureDeterminantCertificate n H)
    (f : (Fin n → Bool) → Bool) :
    computableWithHeadsN n H f :=
  C.toClearedSpanCertificate.computable f

/-- **Selected determinant universal bound.** -/
theorem HStar_le (C : ClearedFeatureDeterminantCertificate n H)
    (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ H :=
  C.toClearedSpanCertificate.HStar_le f

/-- Integer positive denominators and a nonzero modular determinant produce a
real determinant certificate. -/
noncomputable def ofIntegerMod
    (modulus : ℕ)
    (denConst : Fin H → ℤ) (denCoeff : Fin H → Fin n → ℤ)
    (hdenConst : ∀ h, 0 < denConst h)
    (hdenCoeff : ∀ h i, 0 < denCoeff h i)
    (selected : BooleanCubeIndex n → ClearedFeatureIndex n H)
    (hmod :
      (clearedFeatureMatrix
        (fun h ↦ (denConst h : ZMod modulus))
        (fun h i ↦ (denCoeff h i : ZMod modulus)) selected).det ≠ 0) :
    ClearedFeatureDeterminantCertificate n H where
  denConst := fun h ↦ (denConst h : ℝ)
  denCoeff := fun h i ↦ (denCoeff h i : ℝ)
  denConst_pos := fun h ↦ by exact_mod_cast hdenConst h
  denCoeff_pos := fun h i ↦ by exact_mod_cast hdenCoeff h i
  selected := selected
  det_ne_zero := real_clearedFeatureMatrix_det_ne_zero_of_zmod
    modulus denConst denCoeff selected hmod

/-- A checked modular feature determinant yields the universal head bound,
without trusting an external determinant computation. -/
theorem HStar_le_of_integer_zmod_feature_det
    (modulus : ℕ)
    (denConst : Fin H → ℤ) (denCoeff : Fin H → Fin n → ℤ)
    (hdenConst : ∀ h, 0 < denConst h)
    (hdenCoeff : ∀ h i, 0 < denCoeff h i)
    (selected : BooleanCubeIndex n → ClearedFeatureIndex n H)
    (hmod :
      (clearedFeatureMatrix
        (fun h ↦ (denConst h : ZMod modulus))
        (fun h i ↦ (denCoeff h i : ZMod modulus)) selected).det ≠ 0)
    (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ H :=
  ClearedFeatureDeterminantCertificate.HStar_le
    (ofIntegerMod modulus denConst denCoeff hdenConst hdenCoeff selected hmod) f

/-- A generated modular right inverse can discharge the determinant premise
without expanding a determinant in Lean. -/
theorem HStar_le_of_integer_zmod_feature_rightInverse
    (modulus : ℕ) [Fact (1 < modulus)]
    (denConst : Fin H → ℤ) (denCoeff : Fin H → Fin n → ℤ)
    (hdenConst : ∀ h, 0 < denConst h)
    (hdenCoeff : ∀ h i, 0 < denCoeff h i)
    (selected : BooleanCubeIndex n → ClearedFeatureIndex n H)
    (rightInverse : MatrixRightInverseCertificate
      (clearedFeatureMatrix
        (fun h ↦ (denConst h : ZMod modulus))
        (fun h i ↦ (denCoeff h i : ZMod modulus)) selected))
    (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ H :=
  HStar_le_of_integer_zmod_feature_det modulus denConst denCoeff
    hdenConst hdenCoeff selected rightInverse.det_ne_zero f

end ClearedFeatureDeterminantCertificate

end HeadComplexity
