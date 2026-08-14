import HeadComplexity.Results.LowComplexity

set_option linter.style.header false

/-!
# Result-facing weighted upper bounds.

The atom module contains the construction. This module is the public result layer
for the weighted-sum and universal upper bounds on `H*`.
-/

namespace HeadComplexity

/-- **Theorem 9.** Weighted-sum upper bound `H* ≤ M - 1`. -/
theorem HStar_le_weighted_sum (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    (f : (Fin n → Bool) → Bool) (G : ℝ → Bool)
    (hf : ∀ bits, f bits = G (wT lam bits)) :
    HStar n f ≤ (Finset.univ.image (wT lam)).card - 1 :=
  HStar_le_of_computableWithHeadsN (weighted_computable lam hlam f G hf)

/-- **Theorem 9.** Universal upper bound `H* ≤ 2^n - 1`. -/
theorem HStar_le_universal_boolean (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ 2 ^ n - 1 :=
  HStar_le_of_computableWithHeadsN (universal_computable f)

end HeadComplexity
