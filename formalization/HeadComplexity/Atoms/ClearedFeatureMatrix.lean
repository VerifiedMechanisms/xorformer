import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option linter.style.header false

/-!
# Cleared affine-denominator feature matrices

This module packages the finite feature family used by determinant-span
certificates.  The construction is defined over an arbitrary commutative
semiring, so the same matrix can be evaluated over the integers, a finite
quotient ring, and the reals.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

variable {n H : ℕ}

/-- Full cleared-feature labels. `none` is the product of all denominators.
The other labels select a head and either its constant numerator or one raw
coordinate numerator. -/
abbrev ClearedFeatureIndex (n H : ℕ) : Type :=
  Option (Fin H × Option (Fin n))

/-- Canonical finite index type for Boolean cube inputs. -/
abbrev BooleanCubeIndex (n : ℕ) : Type :=
  Fin (Fintype.card (Fin n → Bool))

/-- Canonical enumeration of Boolean cube inputs. -/
noncomputable def booleanCubeEquivFin (n : ℕ) :
    (Fin n → Bool) ≃ BooleanCubeIndex n :=
  Fintype.equivFin _

/-- A Boolean bit interpreted in a semiring. -/
def semiringBitValue {R : Type*} [Semiring R] (bit : Bool) : R :=
  if bit then 1 else 0

/-- Evaluation of an affine form on a Boolean cube over a semiring. -/
def semiringAffineValue {R : Type*} [Semiring R]
    (constant : R) (coefficient : Fin n → R)
    (bits : Fin n → Bool) : R :=
  constant + ∑ i, coefficient i * semiringBitValue (bits i)

/-- Evaluation of a full denominator-cleared feature. -/
def clearedFeatureValue {R : Type*} [CommSemiring R]
    (denConst : Fin H → R) (denCoeff : Fin H → Fin n → R)
    (feature : ClearedFeatureIndex n H) (bits : Fin n → Bool) : R :=
  match feature with
  | none => ∏ h, semiringAffineValue (denConst h) (denCoeff h) bits
  | some (h, none) =>
      ∏ g ∈ Finset.univ.erase h,
        semiringAffineValue (denConst g) (denCoeff g) bits
  | some (h, some i) =>
      semiringBitValue (bits i) *
        ∏ g ∈ Finset.univ.erase h,
          semiringAffineValue (denConst g) (denCoeff g) bits

/-- The square value matrix attached to a selection of as many cleared
features as cube inputs. -/
noncomputable def clearedFeatureMatrix {R : Type*} [CommSemiring R]
    (denConst : Fin H → R) (denCoeff : Fin H → Fin n → R)
    (selected : BooleanCubeIndex n → ClearedFeatureIndex n H) :
    Matrix (BooleanCubeIndex n) (BooleanCubeIndex n) R :=
  fun row column ↦
    clearedFeatureValue denConst denCoeff (selected column)
      ((booleanCubeEquivFin n).symm row)

@[simp] theorem semiringBitValue_real (bit : Bool) :
    semiringBitValue (R := ℝ) bit = boolToReal bit := by
  cases bit <;> rfl

theorem semiringAffineValue_real
    (constant : ℝ) (coefficient : Fin n → ℝ)
    (bits : Fin n → Bool) :
    semiringAffineValue constant coefficient bits =
      affineValue constant coefficient bits := by
  simp only [semiringAffineValue, semiringBitValue_real]
  rfl

/-- A full coefficient vector expands to the corresponding cleared affine
numerator score. -/
theorem sum_clearedFeatureValue
    {R : Type*} [CommSemiring R]
    (denConst : Fin H → R) (denCoeff : Fin H → Fin n → R)
    (coefficient : ClearedFeatureIndex n H → R)
    (bits : Fin n → Bool) :
    (∑ feature, coefficient feature *
        clearedFeatureValue denConst denCoeff feature bits) =
      coefficient none *
          ∏ h, semiringAffineValue (denConst h) (denCoeff h) bits +
        ∑ h,
          semiringAffineValue (coefficient (some (h, none)))
              (fun i ↦ coefficient (some (h, some i))) bits *
            ∏ g ∈ Finset.univ.erase h,
              semiringAffineValue (denConst g) (denCoeff g) bits := by
  classical
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_option]
  simp only [clearedFeatureValue, semiringAffineValue, add_mul,
    Finset.sum_mul, Finset.sum_add_distrib, mul_assoc]

@[simp] theorem map_semiringBitValue
    {R S : Type*} [Semiring R] [Semiring S] (hom : R →+* S)
    (bit : Bool) :
    hom (semiringBitValue (R := R) bit) =
      semiringBitValue (R := S) bit := by
  cases bit <;> simp [semiringBitValue]

@[simp] theorem map_semiringAffineValue
    {R S : Type*} [Semiring R] [Semiring S] (hom : R →+* S)
    (constant : R) (coefficient : Fin n → R)
    (bits : Fin n → Bool) :
    hom (semiringAffineValue constant coefficient bits) =
      semiringAffineValue (hom constant) (fun i ↦ hom (coefficient i)) bits := by
  simp [semiringAffineValue]

/-- Cleared feature evaluation commutes with a commutative-semiring map. -/
theorem map_clearedFeatureValue
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (hom : R →+* S)
    (denConst : Fin H → R) (denCoeff : Fin H → Fin n → R)
    (feature : ClearedFeatureIndex n H) (bits : Fin n → Bool) :
    hom (clearedFeatureValue denConst denCoeff feature bits) =
      clearedFeatureValue (fun h ↦ hom (denConst h))
        (fun h i ↦ hom (denCoeff h i)) feature bits := by
  classical
  rcases feature with _ | ⟨h, _ | i⟩ <;>
    simp [clearedFeatureValue]

/-- The whole feature matrix commutes with coefficient base change. -/
theorem map_clearedFeatureMatrix
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (hom : R →+* S)
    (denConst : Fin H → R) (denCoeff : Fin H → Fin n → R)
    (selected : BooleanCubeIndex n → ClearedFeatureIndex n H) :
    (clearedFeatureMatrix denConst denCoeff selected).map hom =
      clearedFeatureMatrix (fun h ↦ hom (denConst h))
        (fun h i ↦ hom (denCoeff h i)) selected := by
  ext row column
  exact map_clearedFeatureValue hom denConst denCoeff
    (selected column) ((booleanCubeEquivFin n).symm row)

/-- A nonzero determinant after reduction modulo `modulus` certifies that the
integer determinant was nonzero. -/
theorem integer_det_ne_zero_of_zmod_det_ne_zero
    {m : Type*} [Fintype m] [DecidableEq m]
    (modulus : ℕ) (A : Matrix m m ℤ)
    (hmod : (A.map (Int.castRingHom (ZMod modulus))).det ≠ 0) :
    A.det ≠ 0 := by
  intro hzero
  apply hmod
  calc
    (A.map (Int.castRingHom (ZMod modulus))).det =
        ((A.det : ℤ) : ZMod modulus) := (Int.cast_det A).symm
    _ = 0 := by rw [hzero]; norm_num

/-- A nonzero modular determinant of an integer cleared-feature matrix also
certifies nonvanishing of the corresponding real feature matrix. -/
theorem real_clearedFeatureMatrix_det_ne_zero_of_zmod
    (modulus : ℕ)
    (denConst : Fin H → ℤ) (denCoeff : Fin H → Fin n → ℤ)
    (selected : BooleanCubeIndex n → ClearedFeatureIndex n H)
    (hmod :
      (clearedFeatureMatrix
        (fun h ↦ (denConst h : ZMod modulus))
        (fun h i ↦ (denCoeff h i : ZMod modulus)) selected).det ≠ 0) :
    (clearedFeatureMatrix
      (fun h ↦ (denConst h : ℝ))
      (fun h i ↦ (denCoeff h i : ℝ)) selected).det ≠ 0 := by
  classical
  let A : Matrix (BooleanCubeIndex n) (BooleanCubeIndex n) ℤ :=
    clearedFeatureMatrix denConst denCoeff selected
  have hAmod :
      (A.map (Int.castRingHom (ZMod modulus))).det ≠ 0 := by
    dsimp [A]
    change ((clearedFeatureMatrix denConst denCoeff selected).map
      (Int.castRingHom (ZMod modulus))).det ≠ 0
    rw [map_clearedFeatureMatrix]
    exact hmod
  have hA : A.det ≠ 0 :=
    integer_det_ne_zero_of_zmod_det_ne_zero modulus A hAmod
  have hcast : ((A.det : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hA
  rw [Int.cast_det] at hcast
  dsimp [A] at hcast
  change ((clearedFeatureMatrix denConst denCoeff selected).map
    (Int.castRingHom ℝ)).det ≠ 0 at hcast
  rw [map_clearedFeatureMatrix] at hcast
  exact hcast

/-- A checked right inverse is a compact, determinant-free way to certify
nonsingularity over a nontrivial commutative ring. -/
structure MatrixRightInverseCertificate
    {R : Type*} [CommRing R] {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m R) where
  inverse : Matrix m m R
  rightInverse : A * inverse = 1

namespace MatrixRightInverseCertificate

theorem det_ne_zero
    {R : Type*} [CommRing R] [Nontrivial R]
    {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m R} (C : MatrixRightInverseCertificate A) :
    A.det ≠ 0 :=
  Matrix.det_ne_zero_of_right_inverse C.rightInverse

end MatrixRightInverseCertificate

end HeadComplexity
