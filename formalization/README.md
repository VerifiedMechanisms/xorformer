# head-complexity

Lean 4 formalization of the head-complexity results for one-layer attention. The
definitions and theorems mirror the informal proofs in the top-level `theorems/` writeups.

## Status: vanilla results and rotary scalar comparisons

Every theorem in `theorems/01_foundations_and_normal_form/` (L1–L12) is machine-checked
for **general `n`**, with no `sorry`/`admit`, depending only on the three standard
Lean axioms `[propext, Classical.choice, Quot.sound]` (the full build runs a
`#print axioms` gate). `H*` is `HStar` (the least number of heads realizing `f`).
The explicit counterexample in `theorems/02_separations_and_counterexamples/` is
machine-checked as Theorem 13. Theorem 10 characterizes exact scores as a free
constant plus a sum of admissible affine ratios, one per head, including the
exact coefficient conditions and their constructive converse.

`AffineFraction.Admissible` follows the statement directly: the denominator is
positive throughout the Boolean cube, its slopes have `UniformSign`, and a
constant denominator requires numerator slopes with `UniformSign` as well.
Here `UniformSign` means all strictly positive, all strictly negative, or all zero.
The numerator constant is unrestricted.

Theorem 14 adds `PureRoPEAtom` and `RetainedRoPEAtom`, their minimum counts,
the scalar comparison with vanilla, and exact symmetric-family results.
The scalar statements and an exact-score separation are machine-checked.
The finite-frequency interpolation connecting these atoms to literal rotary
attention is a handwritten proof in the
[RoPE writeup](../theorems/03_rotary_attention/014_rope_head_complexity.md).
[Theorem 22](../theorems/03_rotary_attention/022_explicit_pure_rope_separation.md)
now gives an explicit Boolean pure/vanilla separation. Its quantitative vanilla
lower bound is handwritten with exact rational certificates, not Lean-formalized.
The actual unshifted formula's pure scalar upper construction, integer-cubic
identity, rational tie removal, strict full-cube margin, and non-complement
invariance are Lean-checked in `Results/PureRoPEReplicationStrict.lean`.
The seven-head vanilla upper compiler is also Lean-checked.
Supporting Lean modules now also check the raw cubic obstruction, the bounded
pole point and its target Hessian minor, exact squarefree recovery, the rational
coordinate inverse, finite product-grid interpolation, and untied averaging
with preservation of the distinct-group cubic coefficients. These components
do not yet constitute a complete Lean proof of the quantitative Boolean lower
bound.

| # | Theorem | Headline Lean result | File |
|---|-------|----------------------|------|
| 1 | 2-coordinate numerator additive split | `restricted_numerator_additive_split` | `Results/RestrictionLowerBounds.lean` |
| 2 | restricted numerator antipode identity | `restricted_numerator_antipode` | `Results/RestrictionLowerBounds.lean` |
| 3 | checkerboard obstruction `H*≥2` | `checkerboard_restriction_HStar_ge_two` | `Results/RestrictionLowerBounds.lean` |
| 4 | symmetric thresholds `H*=1` | `HStar_threshold` | `Results/ExactFamilies.lean` |
| 5 | family exact values | `HStar_parity`, `HStar_exact` | `Results/ExactFamilies.lean` |
| 6 | `deg±(f) ≤ H*(f)` | `degree_le_of_computableWithHeadsN` | `Results/ThresholdDegree.lean` |
| 7 | `deg±(parity) = n` | `parity_thresholdDeg` | `Results/ThresholdDegree.lean` |
| 8 | `H*(XOR_n) = n` | `HStar_parity` | `Results/ExactFamilies.lean` |
| 9 | weighted-sum `H* ≤ M−1`; universal `≤ 2ⁿ−1` | `HStar_le_weighted_sum`, `HStar_le_universal_boolean` | `Results/WeightedUpperBound.lean` |
| 10 | exact coefficients and score normal form; `H*=L_frac=L_aff` | `AffineFraction.realizable_iff`, `shared_score_iff_affineFraction`, `SharedHStar_eq_LaffineFrac` | `Atoms/AffineFraction.lean`, `Results/AffineFractionNormalForm.lean` (builds on `Results/FractionalNormalForm.lean`) |
| 11 | levels 0/1: const / nonconstant LTF | `HStar_eq_zero_iff`, `HStar_eq_one_iff` | `Results/LowComplexity.lean` |
| 12 | symmetric `H*=C(F)` (sign changes) | `HStar_symmetricFn` | `Results/SymmetricComplexity.lean` |
| 13 | explicit strict separation `deg±<H*` | `f10_strict_separation` | `Results/StrictSeparation.lean` |
| 14 | rotary scalar comparison and symmetric equality | `pureRoPEHStar_le_vanilla`, `retainedRoPEHStar_le_pure`, `thresholdDeg_le_retainedRoPEHStar`, `ropeHStar_symmetric` | `Atoms/RoPE.lean`, `Results/RoPEComparison.lean` |
| 16 | universal two-head pure/vanilla Boolean equality | `pureRoPEComputable_two_iff_vanilla`, `pureRoPEHStar_eq_vanilla_of_le_two` | `Results/PureRoPETwoHeads.lean` |
| 17 | twelve-bit quadratic needs exactly four pure and vanilla heads | `PureRoPEThreeHead.TwelvePair.exact_complexities` | `Results/PureRoPETwelvePairExact.lean` |
| 18 | four vanilla heads for three nonnegative affine zero sets | `ThreeFaceFourHeads.computable_four` | `Results/ThreeFaceFourHeads.lean` |
| 19 | all-vanilla four-head local obstruction and explicit cubic target | `FourHeadCrossOnlyExample.certified_target` | `Results/FourHeadCrossOnlyExample.lean` |
| 19 | original local pattern also excludes four pure heads | `PureFourHeadLocalPattern.pureRoPEHStar_ge_five` | `Results/PureFourHeadLocalPattern.lean` |
| 20 | cubic parity faces exclude all vanilla three-head models | `ThreeHeadTripartitePattern.HStar_ge_four`, `ThreeHeadEmbeddedPattern.HStar_ge_four` | `Results/ThreeHeadTripartitePattern.lean`, `Results/ThreeHeadEmbeddedPattern.lean` |
| 21 | quartic parity faces exclude all vanilla four-head models | `FourHeadQuarticPattern.HStar_ge_five` | `Results/FourHeadQuarticPattern.lean` |
| 22, upper component | exact replicated pure atoms and their cleared classifier | `PureRoPEReplication.explicitFunction_pure_three`, `PureRoPEReplication.explicitFunction_full_cube_sign` | `Results/PureRoPEReplication.lean` |
| 22, averaging component | exact distinct-group cubic coefficient identity | `ThreeHeadReplication.coefficient_sum_three_groups`, `ThreeHeadReplication.uniform_group_sum` | `Polynomial/ThreeHeadReplication.lean` |
| 22, full-cube component | exact unshifted formula, rational tie removal, strict margin, asymmetry | `PureRoPEReplicationStrict.explicitUnshiftedFunction_pure_three`, `PureRoPEReplicationStrict.explicitUnshiftedFunction_margin`, `PureRoPEReplicationStrict.explicitUnshiftedFunction_not_complement_invariant` | `Results/PureRoPEReplicationStrict.lean` |
| 22, vanilla upper component | every three-pure-head classifier admits seven vanilla heads | `vanilla_seven_of_pureRoPE_three` | `Results/ThreeFractionsSevenHeads.lean` |
| 22, explicit vanilla upper | the actual explicit function has at most seven shared vanilla heads | `PureRoPEReplicationBounds.explicit_sharedHStar_le_seven` | `Results/PureRoPEReplicationBounds.lean` |
| 22, untied averaging | actual mean polynomial preserves signs and squarefree cubic coefficients | `MeanGridCubic.cubic_mean_sign_exists`, `CubeTopCoefficients.meanPolynomial_cubic_coefficient` | `Polynomial/MeanGridCubic.lean`, `Polynomial/CubeTopCoefficients.lean` |
| 22, raw obstruction | exact rational target differs from every oriented three-pole cubic | `ExplicitCubicRawObstruction.cubic_ne_oriented_with_readout` | `Polynomial/ExplicitCubicRawObstruction.lean` |
| 22, quantitative pole | bounded pole point and uniformly nonzero target Hessian minor | `ExplicitCubicQuantitativeBounds.exists_pole_with_bounded_nonsingular_minor` | `Polynomial/ExplicitCubicQuantitativeBounds.lean` |
| 22, squarefree recovery | symmetric cubic tensors are determined by squarefree data under cross-minor hypotheses | `SymmetricCubicRecovery.eq_of_squarefree` | `Polynomial/SymmetricCubicRecovery.lean` |
| 22, rational chart | exact inverse, row bounds, and finite product-grid interpolation | `PureCubicChart.chart_inverse_mul`, `PureCubicGraph.eq_zero_of_chartGrid` | `Polynomial/PureCubicChart.lean`, `Polynomial/PureCubicGraph.lean` |

Depends on [mathlib](https://github.com/leanprover-community/mathlib4) (version pinned
in `lakefile.toml`). Build with:

```bash
lake exe cache get   # fetch prebuilt mathlib (first time only)
lake build
lake build HeadComplexity.Examples.All   # optional build for just examples
lake build HeadComplexity.Results.All   # optional build for just results
```

For **exact, reproducible** build/verify instructions, including the
mathlib-cache `curl` fix, the Snellius SLURM job scripts, and how to confirm the
results are axiom-clean, see [`BUILDING.md`](BUILDING.md).

See the [repository README](../README.md) for the wider project context.

The follow-up module `Atoms/RoPEReorientation.lean` checks the pure-head coefficient relation, `RoPEReorientation.exists_positive_direction_of_ne_zero`, and the two quadratic identities used in Theorem 15. Theorem 16 now proves the stronger assertion without complement invariance in `Results/PureRoPETwoHeads.lean`. The new results preserve the original model definitions and use the existing exact vanilla architecture equivalence.
