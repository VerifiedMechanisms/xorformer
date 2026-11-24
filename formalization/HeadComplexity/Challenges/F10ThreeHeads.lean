import HeadComplexity.Model.Head
import HeadComplexity.Results.StrictSeparation

/-!
# Challenge: the ten-bit degree-two function `f10` needs exactly three heads

A trusted statement for the Lean comparator, using only definitions that were in xorformer at
commit f4781ed (`HStar`, `f10`). The proof is left open. A run proves it under the same name in
`HeadComplexity/Solutions/F10ThreeHeads.lean`.
-/

namespace HeadComplexity

/-- The repository's ten-bit degree-two function needs exactly three heads. -/
theorem HStar_f10_eq_three : HStar 10 f10 = 3 := sorry

end HeadComplexity
