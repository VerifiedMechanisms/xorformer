module

public import HeadComplexity.Attention.Complexity.Basic
public import HeadComplexity.Attention.ThresholdDegree
public import HeadComplexity.BooleanFunction.ThresholdDegree.Symmetric

/-!
# Head complexity of symmetric Boolean functions

A symmetric function needs one head for each change in its Hamming-weight profile.
The sign polynomial for the profile is compiled by the positive weighted-sum construction.
-/

@[expose] public section

namespace HeadComplexity

open BooleanFunction

variable {n : ℕ}

/-- A function of Hamming weight can be computed with one head per change in its Boolean
profile. -/
theorem computableWithHeads_symmetricFn (F : Fin (n + 1) → Bool) :
    ComputableWithHeads (symmetricFn F) (signChanges F) := by
  obtain ⟨p, hp, hs⟩ := exists_polynomial_natDegree_le_signChanges F
  refine computableWithHeads_of_sign_eval_weightedSum (fun _ ↦ 1) (fun _ ↦ zero_lt_one) hp
    (fun x ↦ ?_)
  simpa [symmetricFn] using hs ⟨Bool.hammingWeight x,
    Nat.lt_succ_of_le (by simpa using Bool.hammingWeight_le_card x)⟩

/-- The exact head count of a symmetric Boolean function is the number of changes between
consecutive Hamming weights. -/
theorem headComplexity_symmetricFn (F : Fin (n + 1) → Bool) :
    headComplexity (symmetricFn F) = signChanges F :=
  le_antisymm (computableWithHeads_symmetricFn F).headComplexity_le
    (signChanges_le_of_thresholdDegreeLE (computableWithHeads_headComplexity _).thresholdDegreeLE)

/-- A Hamming-weight threshold that is nonconstant on the cube needs exactly one head. -/
theorem headComplexity_threshold {t : ℕ} (ht : 0 < t) (htn : t ≤ n) :
    headComplexity (threshold n t) = 1 :=
  (headComplexity_symmetricFn _).trans (signChanges_thresholdProfile ht htn)

/-- Testing for an exact count strictly between zero and the input length needs exactly two
heads. -/
theorem headComplexity_exactCount {t : ℕ} (ht : 0 < t) (htn : t < n) :
    headComplexity (exactCount n t) = 2 :=
  (headComplexity_symmetricFn _).trans (signChanges_exactCountProfile ht htn)

/-- Parity needs exactly as many heads as there are input bits. -/
@[simp] theorem headComplexity_parity (n : ℕ) : headComplexity (parity n) = n :=
  (headComplexity_symmetricFn _).trans (signChanges_parityProfile n)

end HeadComplexity
