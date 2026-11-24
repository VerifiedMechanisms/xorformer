import HeadComplexity.Model.Head
import HeadComplexity.Polynomial.ThresholdDegree

/-!
# Challenge: threshold degree two needs at most `⌊n/2⌋` heads for `n ≥ 6`

A trusted statement for the Lean comparator, using only definitions that were in xorformer at
commit f4781ed (`computableWithHeadsN`, `ThresholdDegLE`). The proof is left open. A run proves it
under the same name in `HeadComplexity/Solutions/QuadraticFloor.lean`.
-/

namespace HeadComplexity.Challenge

/-- Every function of threshold degree at most two on `n ≥ 6` bits is computable with
`⌊n/2⌋` heads. -/
theorem quadratic_floor_computable {n : ℕ} (hn : 6 ≤ n)
    {f : (Fin n → Bool) → Bool} (hd : ThresholdDegLE f 2) :
    computableWithHeadsN n (n / 2) f := sorry

end HeadComplexity.Challenge
