import HeadComplexity.Atoms.PositiveWeightedSignDegree
import HeadComplexity.Atoms.AffineHead
import HeadComplexity.Atoms.SignPolynomial
import HeadComplexity.Results.SymmetricComplexity
import HeadComplexity.Results.ThresholdDegree

set_option linter.style.header false

/-!
# Polynomial presentation of positive-projection exactness

Positive weighted sign degree is the Lean polynomial-certificate presentation
of the positive-projection sign-change invariant in the existing theorem 69
writeup. Together with the general threshold-degree lower bound, it sandwiches
`HStar` between two polynomial quantities. Whenever the endpoints coincide,
this determines `HStar` exactly without a symmetry hypothesis.
-/

namespace HeadComplexity

variable {n : ℕ}

/-- Head complexity is at most positive weighted sign degree. -/
theorem HStar_le_positiveWeightedSignDeg (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ positiveWeightedSignDeg f :=
  HStar_le_of_computableWithHeadsN (positiveWeightedSignDeg_computable f)

/-- Ordinary threshold degree is at most positive weighted sign degree. -/
theorem thresholdDeg_le_positiveWeightedSignDeg
    (f : (Fin n → Bool) → Bool) :
    thresholdDeg f ≤ positiveWeightedSignDeg f :=
  (thresholdDeg_le_HStar f).trans (HStar_le_positiveWeightedSignDeg f)

/-- Unit weights recover the real-valued Hamming weight. -/
theorem wT_one_eq_hammingWeight (bits : Fin n → Bool) :
    wT (fun _ : Fin n ↦ (1 : ℝ)) bits = (hammingWeight bits : ℝ) := by
  rw [hammingWeight_eq_sum]
  simp [wT, boolToReal]

/-- The sign-change polynomial supplies a positive weighted sign-degree
certificate for every symmetric Boolean function. -/
theorem symmetricFn_positiveWeightedSignDegLE (F : ℕ → Bool) (n : ℕ) :
    PositiveWeightedSignDegLE (symmetricFn F : (Fin n → Bool) → Bool)
      (signChanges n F) := by
  obtain ⟨P, hPdeg, hPsign⟩ := exists_sign_poly F n
  refine ⟨(fun _ ↦ 1), (fun _ ↦ by norm_num), P, hPdeg, ?_⟩
  intro bits
  rw [wT_one_eq_hammingWeight]
  simpa [symmetricFn] using hPsign (hammingWeight bits) (hammingWeight_le n bits)

/-- On symmetric functions, positive weighted sign degree is exactly the
number of sign changes of the Hamming-weight profile. -/
theorem positiveWeightedSignDeg_symmetricFn (F : ℕ → Bool) (n : ℕ) :
    positiveWeightedSignDeg (symmetricFn F : (Fin n → Bool) → Bool) =
      signChanges n F := by
  apply Nat.le_antisymm
  · exact positiveWeightedSignDeg_le (symmetricFn_positiveWeightedSignDegLE F n)
  · have hupper := HStar_le_positiveWeightedSignDeg
      (symmetricFn F : (Fin n → Bool) → Bool)
    rwa [HStar_symmetricFn] at hupper

/-- On symmetric functions, ordinary threshold degree is also exactly the
number of sign changes of the Hamming-weight profile. -/
theorem thresholdDeg_symmetricFn (F : ℕ → Bool) (n : ℕ) :
    thresholdDeg (symmetricFn F : (Fin n → Bool) → Bool) = signChanges n F := by
  apply Nat.le_antisymm
  · have h := thresholdDeg_le_HStar
      (symmetricFn F : (Fin n → Bool) → Bool)
    rwa [HStar_symmetricFn] at h
  · exact signChanges_le_of_ThresholdDegLE
      (thresholdDeg_spec (symmetricFn F : (Fin n → Bool) → Bool))

/-- Threshold degree, head complexity, and positive weighted sign degree form
a general lower-and-upper-bound sandwich. -/
theorem thresholdDeg_le_HStar_le_positiveWeightedSignDeg
    (f : (Fin n → Bool) → Bool) :
    thresholdDeg f ≤ HStar n f ∧ HStar n f ≤ positiveWeightedSignDeg f :=
  ⟨thresholdDeg_le_HStar f, HStar_le_positiveWeightedSignDeg f⟩

/-- If threshold degree equals positive weighted sign degree, both bounds meet
and determine head complexity exactly.  No symmetry assumption is required. -/
theorem HStar_eq_thresholdDeg_of_eq_positiveWeightedSignDeg
    (f : (Fin n → Bool) → Bool)
    (h : thresholdDeg f = positiveWeightedSignDeg f) :
    HStar n f = thresholdDeg f := by
  apply le_antisymm
  · rw [h]
    exact HStar_le_positiveWeightedSignDeg f
  · exact thresholdDeg_le_HStar f

/-- Polynomial-certificate form of the low-alternation case in the
positive-projection exactness theorem. If the positive weighted sign degree is
at most two, every nonconstant non-LTF has head complexity exactly two. -/
theorem HStar_eq_two_of_positiveWeightedSignDeg_le_two
    (f : (Fin n → Bool) → Bool)
    (hdeg : positiveWeightedSignDeg f ≤ 2)
    (hnconst : ¬ (∀ x y, f x = f y)) (hnLTF : ¬ isLTF f) :
    HStar n f = 2 := by
  have hle : HStar n f ≤ 2 :=
    (HStar_le_positiveWeightedSignDeg f).trans hdeg
  have hne0 : HStar n f ≠ 0 :=
    fun h0 => hnconst ((HStar_eq_zero_iff f).mp h0)
  have hne1 : HStar n f ≠ 1 :=
    fun h1 => hnLTF ((HStar_eq_one_iff f).mp h1).2
  omega

end HeadComplexity
