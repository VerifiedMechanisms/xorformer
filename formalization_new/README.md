# Head complexity of Boolean functions

Lean 4 formalization of one-layer softmax attention with shared embeddings.
The library proves the thirteen results in the [theorem writeups](../theorems/).

Use `import HeadComplexity` for the library, or import a subject module directly.
`ComputableWithHeads f H` is feasibility at budget `H`. The number
`headComplexity f` is its least feasible budget, and `HasHeadScore s H`
asserts exact realization of a scalar score.

```lean
import HeadComplexity.Attention.Complexity.Symmetric

open HeadComplexity

example (n : ℕ) : headComplexity (BooleanFunction.parity n) = n :=
  headComplexity_parity n
```

## Results by subject

| # | Result | Lean declaration | Subject module |
|---|---|---|---|
| 1 | Additive split on a two-coordinate face | `Attention.Model.numerator_additive_split` and `denominator_additive_split` | [Face](HeadComplexity/Attention/Face.lean) |
| 2 | Antipode identities and intersecting diagonal segments | `Attention.Model.restricted_numerator_antipode`, `restricted_denominator_antipode`, `openSegment_headOutput_inter_nonempty` | [Face](HeadComplexity/Attention/Face.lean) |
| 3 | A checkerboard needs at least two heads | `two_le_headComplexity_of_checkerboard` | [OneHead](HeadComplexity/Attention/Complexity/OneHead.lean) |
| 4 | Nonconstant symmetric thresholds need one head | `headComplexity_threshold` | [Symmetric heads](HeadComplexity/Attention/Complexity/Symmetric.lean) |
| 5 | Internal exact-count functions need two heads | `headComplexity_exactCount` | [Symmetric heads](HeadComplexity/Attention/Complexity/Symmetric.lean) |
| 6 | A head budget bounds threshold degree | `ComputableWithHeads.thresholdDegreeLE` | [Clearing denominators](HeadComplexity/Attention/ThresholdDegree.lean) |
| 7 | Parity has threshold degree equal to the number of bits | `BooleanFunction.thresholdDegree_parity` | [Symmetric degree](HeadComplexity/BooleanFunction/ThresholdDegree/Symmetric.lean) |
| 8 | Parity needs one head per bit | `headComplexity_parity` | [Symmetric heads](HeadComplexity/Attention/Complexity/Symmetric.lean) |
| 9 | A weighted sum with M image points gives budget M−1, with universal budget 2ⁿ−1 | `headComplexity_le_of_factorsThrough_weightedSum` and `headComplexity_le_two_pow_sub_one` | [Weighted construction](HeadComplexity/Attention/WeightedSum.lean) and [minimum API](HeadComplexity/Attention/Complexity/Basic.lean) |
| 10 | Exact coefficient image, exact scores, and minimum ratio count | `Attention.AffineFraction.realizable_iff`, `hasHeadScore_iff_exists_affineFractions`, `isLeast_headComplexity_affineFractions` | [Affine fractions](HeadComplexity/Attention/AffineFraction.lean) and [minimum API](HeadComplexity/Attention/Complexity/Basic.lean) |
| 11 | The zero- and one-head levels | `headComplexity_eq_zero_iff` and `headComplexity_eq_one_iff` | [OneHead](HeadComplexity/Attention/Complexity/OneHead.lean) |
| 12 | The symmetric head count equals the number of sign changes | `headComplexity_symmetricFn` | [Symmetric heads](HeadComplexity/Attention/Complexity/Symmetric.lean) |
| 13 | A ten-bit function has threshold degree two and needs at least three heads | `Counterexamples.thresholdDegree_f10_lt_headComplexity` | [Threshold degree gap](HeadComplexity/Counterexamples/ThresholdDegreeGap.lean) |

The worked [Boolean gates](HeadComplexity/Examples/BooleanGates.lean) and
[affine ratios](HeadComplexity/Examples/AffineRatios.lean) are library clients.

## Build

The project uses Lean and Mathlib `v4.31.0`. Run the following from this directory.

```bash
lake exe cache get   # first time only
lake build
```

After adding a module, run `lake exe mk_all --lib HeadComplexity` to update
`HeadComplexity.lean`.
