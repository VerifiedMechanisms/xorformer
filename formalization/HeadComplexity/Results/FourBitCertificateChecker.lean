import HeadComplexity.BooleanCube.FourBitEncoding
import HeadComplexity.Polynomial.PositiveCircuit
import HeadComplexity.Results.IntegralClearedCertificate

set_option linter.style.header false

/-!
# Kernel-checkable four-bit classification certificates

This is a compact, executable certificate interface for the exhaustive
four-bit classification.  A data set is a total table indexed by all 32768
complement-pair representatives.  Its validity is a decidable proposition
containing only finite integer arithmetic.  The soundness theorem turns a
successful check into the analytic cleared-score and positive-circuit
certificates used by the main theory.

The large archived payload is deliberately not included in this module.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

/-- Raw integral affine data on four variables. -/
structure IntegralAffine4 where
  constant : ℤ
  coefficient : Fin 4 → ℤ
deriving DecidableEq

namespace IntegralAffine4

/-- The two denominator orientations supported by the atom compiler. -/
def IsOriented (A : IntegralAffine4) : Prop :=
  (0 < A.constant ∧ ∀ i, 0 < A.coefficient i) ∨
    (0 < A.constant ∧ (∀ i, A.coefficient i < 0) ∧
      ∑ i, -A.coefficient i < A.constant)

instance (A : IntegralAffine4) : Decidable A.IsOriented := by
  unfold IsOriented
  infer_instance

/-- Exact value at a conventionally enumerated four-cube vertex. -/
def value (A : IntegralAffine4) (x : Fin 16) : ℤ :=
  semiringAffineValue A.constant A.coefficient (fourBitCube x)

/-- Pass checked raw affine data through the analytic orientation boundary. -/
def toOrientedDenominator (A : IntegralAffine4) (hA : A.IsOriented) :
    IntegralOrientedDenominator 4 where
  constant := A.constant
  coefficient := A.coefficient
  orientation := hA

end IntegralAffine4

/-- A denominator-cleared score row with `H` affine numerators. -/
structure RawClearedScore4 (H : ℕ) where
  bias : ℤ
  numerator : Fin H → IntegralAffine4
deriving DecidableEq

namespace RawClearedScore4

/-- Direct exact-integer evaluation of a raw cleared score. -/
def score (C : RawClearedScore4 H)
    (denominator : Fin H → IntegralAffine4) (x : Fin 16) : ℤ :=
  C.bias * ∏ h, (denominator h).value x +
    ∑ h, (C.numerator h).value x *
      ∏ g ∈ Finset.univ.erase h, (denominator g).value x

/-- The finite sign check for one truth-table mask. -/
def StrictlyRepresentsMask (C : RawClearedScore4 H)
    (denominator : Fin H → IntegralAffine4) (mask : Fin 32768) : Prop :=
  ∀ x : Fin 16,
    (0 < C.score denominator x ↔ mask.val.testBit x.val = true) ∧
      C.score denominator x ≠ 0

instance (C : RawClearedScore4 H) (denominator : Fin H → IntegralAffine4)
    (mask : Fin 32768) : Decidable (C.StrictlyRepresentsMask denominator mask) :=
  by
    unfold StrictlyRepresentsMask
    infer_instance

/-- A checked raw row becomes a faithful analytic cleared-score certificate. -/
noncomputable def toCertificate (C : RawClearedScore4 H)
    (denominator : Fin H → IntegralAffine4)
    (horiented : ∀ h, (denominator h).IsOriented)
    (mask : Fin 32768) (hrep : C.StrictlyRepresentsMask denominator mask) :
    IntegralClearedScoreCertificate 4 H
      (fourBitRepresentativeFunction mask) where
  denominator := fun h ↦ (denominator h).toOrientedDenominator (horiented h)
  bias := C.bias
  numConstant := fun h ↦ (C.numerator h).constant
  numCoefficient := fun h ↦ (C.numerator h).coefficient
  represents := by
    intro bits
    simpa [score, integralClearedScore, IntegralAffine4.value,
      IntegralAffine4.toOrientedDenominator,
      IntegralOrientedDenominator.value, fourBitRepresentativeFunction] using
      hrep (fourBitCubeEquiv.symm bits)

end RawClearedScore4

/-- A raw nonnegative integer circuit on the enumerated four-cube. -/
structure RawDegreeTwoCircuit4 where
  weight : Fin 16 → ℕ
deriving DecidableEq

namespace RawDegreeTwoCircuit4

/-- Exact finite circuit check against every squarefree monomial through
degree two. -/
def IsCircuitForMask (C : RawDegreeTwoCircuit4)
    (mask : Fin 32768) : Prop :=
  (∃ x, 0 < C.weight x) ∧
    ∀ S : Finset (Fin 4), S.card ≤ 2 →
      ∑ x, (C.weight x : ℤ) *
        integralLabelSign (mask.val.testBit x.val) *
        integralSquarefreeMonomial S (fourBitCube x) = 0

instance (C : RawDegreeTwoCircuit4) (mask : Fin 32768) :
    Decidable (C.IsCircuitForMask mask) := by
  unfold IsCircuitForMask
  infer_instance

/-- Soundness of the executable circuit convention. -/
noncomputable def toPositiveCircuit (C : RawDegreeTwoCircuit4)
    (mask : Fin 32768) (hC : C.IsCircuitForMask mask) :
    IntegralPositiveCircuit (fourBitRepresentativeFunction mask) 2 where
  weight := fun bits ↦ C.weight (fourBitCubeEquiv.symm bits)
  nonzero := by
    obtain ⟨x, hx⟩ := hC.1
    exact ⟨fourBitCubeEquiv x, by simpa using hx⟩
  moment := by
    intro S hS
    rw [← fourBitCubeEquiv.sum_comp]
    simpa using hC.2 S hS

end RawDegreeTwoCircuit4

/-- One row of the total complement-representative table. -/
inductive FourBitClassificationRow where
  | degreeAtMostTwo
      (dictionary : Fin 17) (score : RawClearedScore4 2)
  | degreeAtLeastThree
      (circuit : RawDegreeTwoCircuit4)
      (degreeThree : Option (Fin 5 × RawClearedScore4 3))
deriving DecidableEq

/-- All raw data needed by the finite checker.  Total function fields make
coverage of every representative structural rather than a separate parsing
claim. -/
structure FourBitClassificationData where
  h2Denominator : Fin 17 → Fin 2 → IntegralAffine4
  h3Denominator : Fin 5 → Fin 3 → IntegralAffine4
  row : Fin 32768 → FourBitClassificationRow

namespace FourBitClassificationData

/-- Validity of the row at one representative mask. -/
def RowValid (D : FourBitClassificationData) (mask : Fin 32768) : Prop :=
  match D.row mask with
  | .degreeAtMostTwo dictionary score =>
      score.StrictlyRepresentsMask (D.h2Denominator dictionary) mask
  | .degreeAtLeastThree circuit degreeThree =>
      circuit.IsCircuitForMask mask ∧
        match degreeThree with
        | none => mask = fourBitParityMask
        | some (dictionary, score) =>
            mask ≠ fourBitParityMask ∧
              score.StrictlyRepresentsMask
                (D.h3Denominator dictionary) mask

instance (D : FourBitClassificationData) (mask : Fin 32768) :
    Decidable (D.RowValid mask) := by
  cases hrow : D.row mask with
  | degreeAtMostTwo =>
      rw [RowValid, hrow]
      infer_instance
  | degreeAtLeastThree =>
      rename_i circuit degreeThree
      cases hthree : degreeThree with
      | none =>
          simp only [RowValid, hrow, hthree]
          infer_instance
      | some entry =>
          obtain ⟨dictionary, score⟩ := entry
          simp only [RowValid, hrow, hthree]
          infer_instance

/-- The exact finite validity proposition checked by the kernel. -/
def IsValid (D : FourBitClassificationData) : Prop :=
  (∀ dictionary h, (D.h2Denominator dictionary h).IsOriented) ∧
  (∀ dictionary h, (D.h3Denominator dictionary h).IsOriented) ∧
  ∀ mask, D.RowValid mask

instance (D : FourBitClassificationData) : Decidable D.IsValid := by
  unfold IsValid
  infer_instance

/-- Boolean entry point intended for ordinary `by decide` proof reflection. -/
def check (D : FourBitClassificationData) : Bool :=
  decide D.IsValid

/-- A successful Boolean check yields the full finite validity proposition. -/
theorem valid_of_check_eq_true (D : FourBitClassificationData)
    (hcheck : D.check = true) : D.IsValid :=
  of_decide_eq_true hcheck

end FourBitClassificationData

/-- The three analytically distinct outcomes for one complement-pair
representative. -/
inductive FourBitExactWitness (mask : Fin 32768) where
  | degreeAtMostTwo
      (certificate : IntegralClearedScoreCertificate 4 2
        (fourBitRepresentativeFunction mask))
  | parity
      (isParity : mask = fourBitParityMask)
      (circuit : IntegralPositiveCircuit
        (fourBitRepresentativeFunction mask) 2)
  | degreeThree
      (circuit : IntegralPositiveCircuit
        (fourBitRepresentativeFunction mask) 2)
      (certificate : IntegralClearedScoreCertificate 4 3
        (fourBitRepresentativeFunction mask))

/-- The analytic payload needed for the exhaustive four-bit theorem. -/
structure FourBitExactCertificate where
  witness : ∀ mask : Fin 32768, FourBitExactWitness mask

namespace FourBitClassificationData

private theorem existsExactWitness (D : FourBitClassificationData)
    (hD : D.IsValid) (mask : Fin 32768) :
    Nonempty (FourBitExactWitness mask) := by
  have hrow := hD.2.2 mask
  cases hr : D.row mask with
  | degreeAtMostTwo dictionary score =>
      apply Nonempty.intro
      apply FourBitExactWitness.degreeAtMostTwo
      apply score.toCertificate (D.h2Denominator dictionary)
        (fun h ↦ hD.1 dictionary h) mask
      simpa [RowValid, hr] using hrow
  | degreeAtLeastThree circuit degreeThree =>
      cases hthree : degreeThree with
      | none =>
          have hhigh : circuit.IsCircuitForMask mask ∧
              mask = fourBitParityMask := by
            rw [RowValid, hr, hthree] at hrow
            exact hrow
          exact ⟨FourBitExactWitness.parity hhigh.2
            (circuit.toPositiveCircuit mask hhigh.1)⟩
      | some entry =>
          obtain ⟨dictionary, score⟩ := entry
          have hhigh : circuit.IsCircuitForMask mask ∧
              (mask ≠ fourBitParityMask ∧
                score.StrictlyRepresentsMask
                  (D.h3Denominator dictionary) mask) := by
            rw [RowValid, hr, hthree] at hrow
            exact hrow
          exact ⟨FourBitExactWitness.degreeThree
            (circuit.toPositiveCircuit mask hhigh.1)
            (score.toCertificate (D.h3Denominator dictionary)
              (fun h ↦ hD.2.1 dictionary h) mask hhigh.2.2)⟩

/-- Main checker soundness theorem.  No conclusion of an external verifier is
trusted: only the finite proposition obtained from `check = true` is used. -/
noncomputable def toExactCertificate (D : FourBitClassificationData)
    (hD : D.IsValid) : FourBitExactCertificate where
  witness := fun mask ↦ Classical.choice (D.existsExactWitness hD mask)

/-- Boolean-check form of the soundness theorem. -/
noncomputable def exactCertificate_of_check_eq_true
    (D : FourBitClassificationData) (hcheck : D.check = true) :
    FourBitExactCertificate :=
  D.toExactCertificate (D.valid_of_check_eq_true hcheck)

end FourBitClassificationData

end HeadComplexity
