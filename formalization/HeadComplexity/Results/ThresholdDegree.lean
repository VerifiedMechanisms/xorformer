import HeadComplexity.Polynomial.ModelToPolynomial
import HeadComplexity.Polynomial.ParityThresholdDegree
import HeadComplexity.Results.LowComplexity

set_option linter.style.header false

/-!
# Result-facing threshold-degree bounds.

The polynomial modules define threshold degree and prove polynomial facts. This
module exposes the parts of that machinery that are headline results for head
complexity: heads imply low threshold degree, and parity has threshold degree `n`.
-/

namespace HeadComplexity

/-- **Theorem 6.** `H` heads give a degree-`≤ H` sign representation. -/
alias degree_le_of_computableWithHeadsN := signReprDegLe_of_computableWithHeadsN

/-- Every threshold-degree certificate upper-bounds the minimum threshold
degree. -/
theorem thresholdDeg_le_of_ThresholdDegLE {f : (Fin n → Bool) → Bool} {d : ℕ}
    (h : ThresholdDegLE f d) : thresholdDeg f ≤ d := by
  classical
  have hex : ∃ e, ThresholdDegLE f e := ⟨d, h⟩
  unfold thresholdDeg
  rw [dif_pos hex]
  exact Nat.find_min' hex h

/-- The minimum threshold degree is attained. -/
theorem thresholdDeg_spec (f : (Fin n → Bool) → Bool) :
    ThresholdDegLE f (thresholdDeg f) := by
  classical
  have hdeg : ThresholdDegLE f (HStar n f) :=
    signReprDegLe_of_computableWithHeadsN (HStar_computable f)
  have hex : ∃ d, ThresholdDegLE f d := ⟨HStar n f, hdeg⟩
  unfold thresholdDeg
  rw [dif_pos hex]
  exact Nat.find_spec hex

/-- **Theorem 6 (minimum form).** Threshold degree is at most head
complexity. -/
theorem thresholdDeg_le_HStar (f : (Fin n → Bool) → Bool) :
    thresholdDeg f ≤ HStar n f :=
  thresholdDeg_le_of_ThresholdDegLE
    (signReprDegLe_of_computableWithHeadsN (HStar_computable f))

/-- **Theorem 7.** Parity has threshold degree exactly `n`. -/
alias parity_thresholdDeg := thresholdDeg_parity

end HeadComplexity
