import HeadComplexity.Results.DummyVariables
import HeadComplexity.Results.ExactFamilies
import HeadComplexity.Results.FourBitCertificateChecker
import HeadComplexity.Results.OneBitGateThresholdDegree
import HeadComplexity.Results.StructuralInvariances

set_option linter.style.header false

/-!
# Analytic conclusion of the four-bit exact certificate

This module proves the complete quantified theorem from a checked
`FourBitExactCertificate`.  It also packages repeated fresh dummy variables so
the four-bit theorem descends to every smaller dimension.
-/

namespace HeadComplexity

variable {n : ℕ}

/-- Add `r` ignored coordinates at the front of a Boolean function. -/
def prependDummies (f : (Fin n → Bool) → Bool) :
    (r : ℕ) → (Fin (n + r) → Bool) → Bool
  | 0 => f
  | r + 1 => fun bits ↦ prependDummies f r (tailBits bits)

@[simp] theorem prependDummies_zero (f : (Fin n → Bool) → Bool) :
    prependDummies f 0 = f := rfl

@[simp] theorem prependDummies_succ (f : (Fin n → Bool) → Bool) (r : ℕ) :
    prependDummies f (r + 1) =
      fun bits ↦ prependDummies f r (tailBits bits) := rfl

/-- Repeated ignored fresh coordinates preserve head complexity. -/
theorem HStar_prependDummies (f : (Fin n → Bool) → Bool) (r : ℕ) :
    HStar (n + r) (prependDummies f r) = HStar n f := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [prependDummies_succ]
      change HStar ((n + r) + 1)
        (fun bits ↦ prependDummies f r
          (pullBitsAlong (Fin.succEmb (n + r)) bits)) =
          HStar n f
      rw [HStar_dummyVariablesAlong, ih]

/-- Repeated ignored fresh coordinates preserve threshold degree. -/
theorem thresholdDeg_prependDummies
    (f : (Fin n → Bool) → Bool) (r : ℕ) :
    thresholdDeg (prependDummies f r) = thresholdDeg f := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [prependDummies_succ]
      change thresholdDeg
        (fun bits : Fin ((n + r) + 1) → Bool ↦
          prependDummies f r (tailBits bits)) = thresholdDeg f
      rw [thresholdDeg_ignoreFresh, ih]

/-- Below two heads, the general threshold-degree lower bound and the exact
zero-head and one-head characterizations force equality. -/
theorem HStar_eq_thresholdDeg_of_HStar_le_two
    (f : (Fin n → Bool) → Bool) (hupper : HStar n f ≤ 2) :
    HStar n f = thresholdDeg f := by
  have hlower := thresholdDeg_le_HStar f
  by_cases hzero : thresholdDeg f = 0
  · have hconstant : ∀ x y, f x = f y :=
      constant_of_ThresholdDegLE_zero (hzero ▸ thresholdDeg_spec f)
    have hheadzero : HStar n f = 0 := (HStar_eq_zero_iff f).2 hconstant
    omega
  · by_cases hone : thresholdDeg f = 1
    · have hltf : isLTF f := (ThresholdDegLE_one_iff_isLTF f).1
          (hone ▸ thresholdDeg_spec f)
      have hheadone : HStar n f ≤ 1 :=
        HStar_le_of_computableWithHeadsN (computable_one_of_isLTF f hltf)
      omega
    · omega

namespace FourBitExactCertificate

/-- Every archived complement-pair representative has exact equality. -/
theorem representative_exact (C : FourBitExactCertificate)
    (mask : Fin 32768) :
    HStar 4 (fourBitRepresentativeFunction mask) =
      thresholdDeg (fourBitRepresentativeFunction mask) := by
  cases C.witness mask with
  | degreeAtMostTwo certificate =>
      exact HStar_eq_thresholdDeg_of_HStar_le_two _ certificate.HStar_le
  | parity isParity circuit =>
      subst mask
      rw [fourBitRepresentativeFunction_parity, HStar_parity,
        thresholdDeg_parity]
  | degreeThree circuit certificate =>
      have hlower := circuit.lt_thresholdDeg
      have hdegreeHead := thresholdDeg_le_HStar
        (fourBitRepresentativeFunction mask)
      have hupper := certificate.HStar_le
      omega

/-- Equality for every four-bit Boolean function, using output-complement
invariance to pass from the representative half of the truth tables to all
truth tables. -/
theorem fourBit_exact (C : FourBitExactCertificate)
    (f : (Fin 4 → Bool) → Bool) :
    HStar 4 f = thresholdDeg f := by
  obtain ⟨mask, hrep | hcomp⟩ := exists_representative_or_complement f
  · rw [hrep]
    exact C.representative_exact mask
  · rw [hcomp, HStar_complement]
    change HStar 4 (fourBitRepresentativeFunction mask) =
      thresholdDeg (complementFn (fourBitRepresentativeFunction mask))
    rw [thresholdDeg_complement]
    exact C.representative_exact mask

/-- **Exact classification through four bits.** A checked four-bit certificate
and the analytic invariances imply `HStar = thresholdDeg` for every Boolean
function on at most four inputs. -/
theorem exact_of_dimension_le_four (C : FourBitExactCertificate)
    (f : (Fin n → Bool) → Bool) (hn : n ≤ 4) :
    HStar n f = thresholdDeg f := by
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · have h := C.fourBit_exact (prependDummies f 4)
    rw [HStar_prependDummies f 4, thresholdDeg_prependDummies f 4] at h
    exact h
  · have h := C.fourBit_exact (prependDummies f 3)
    rw [HStar_prependDummies f 3, thresholdDeg_prependDummies f 3] at h
    exact h
  · have h := C.fourBit_exact (prependDummies f 2)
    rw [HStar_prependDummies f 2, thresholdDeg_prependDummies f 2] at h
    exact h
  · have h := C.fourBit_exact (prependDummies f 1)
    rw [HStar_prependDummies f 1, thresholdDeg_prependDummies f 1] at h
    exact h
  · have h := C.fourBit_exact (prependDummies f 0)
    rw [HStar_prependDummies f 0, thresholdDeg_prependDummies f 0] at h
    exact h

end FourBitExactCertificate

/-- Direct end-to-end theorem from a successful ordinary kernel check. -/
theorem smallDimension_exact_of_check_eq_true
    (D : FourBitClassificationData) (hcheck : D.check = true)
    (f : (Fin n → Bool) → Bool) (hn : n ≤ 4) :
    HStar n f = thresholdDeg f :=
  (D.exactCertificate_of_check_eq_true hcheck).exact_of_dimension_le_four f hn

end HeadComplexity
