import HeadComplexity.Atoms.ClearedNormalForm

set_option linter.style.header false

/-!
# Result-facing cleared polynomial normal forms

This module exposes the arbitrary-head structured polynomial bridge. The exact
normal form retains actual fractional atoms, while the affine-factor relaxation
provides a reusable target for rank and factorization lower bounds.
-/

namespace HeadComplexity

/-- Attention computation with `H` heads is exactly sign representation by the
cleared polynomial of `H` fractional atoms. -/
alias cleared_polynomial_normal_form := computableWithHeadsN_iff_clearedAtomRep

/-- Failure of every positive affine-factor certificate rules out computation
with `H` heads. -/
alias cleared_affine_obstruction := not_computableWithHeadsN_of_no_clearedAffineRep

/-- Forgetting the affine factorization recovers a threshold-degree witness. -/
alias cleared_affine_to_threshold_degree := thresholdDegLE_of_clearedAffineRep

end HeadComplexity
