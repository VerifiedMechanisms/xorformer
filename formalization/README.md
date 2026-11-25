# head-complexity

Lean 4 formalization of the head-complexity results for one-layer attention. The
definitions and theorems mirror the informal proofs in the top-level `theorems/` writeups.

## Status: vanilla results and literal rotary comparisons

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
Theorem 16 proves the reverse implication at every head count at most two,
without complement invariance. Theorem 18 formalizes the finite-frequency
interpolation and the exact rectangular rotary architecture, including separate
model and head dimensions, explicit output projections, shared embeddings,
and the fixed query's self attention. Fixed and free frequencies have the same
exact scalar score class. Theorem 20 proves equality at every head count for
all input lengths at most four. Theorems 17, 19, and 21 give structured
head-preserving cases and general bounds with extra heads. The pure-specific
bound is `2^H - 2` for `H ≥ 2`. Any strict improvement requires at least five
input bits, at least three pure heads, and at least four vanilla heads.

Theorem 22 is fully machine-checked: an explicit family on `18m` bits has
pure rotary minimum three and vanilla minimum between four and six for
all sufficiently large `m`. The proof includes coefficient compactness,
grouped Boolean averaging, local polynomial divisibility, the tensor obstruction,
and both literal rotary-frequency conventions.
`not_universal_pureRoPEHStar_eq_SharedHStar` explicitly refutes universal equality.
Exact dummy-input invariance extends the separation to every sufficiently large
input length. The Lean threshold is existential. A separately audited
[quantitative proof](../artifacts/rope/research/effective_replication_threshold.md)
gives the sufficient replication count `10^40000`; that numerical constant is
not formalized and is not asserted to be the first separating count.

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
| 16 | unconditional two-head pure equivalence | `pureRoPEComputable_iff_vanilla_of_le_two`, `pureRoPEHStar_eq_vanilla_of_le_two` | `Results/RoPETwoHeads.lean` |
| 17 | arbitrary affine-statistic polynomial bound | `AffineStatistic.computable_of_polynomial` | `Results/AffineStatisticUpperBound.lean` |
| 18 | literal rectangular rotary bridge | `rectangularStandardPureRotaryComputable_iff_scalar`, `rectangularFreePureRotaryComputable_iff_scalar` | `Model/RotaryInterpolation.lean`, `Model/RectangularPureRoPE.lean` |
| 19 | general and pure-specific exponential simulation bounds | `FiniteDifference.computable_of_positive_denominators`, `pureRoPEComputable_vanilla_improved_exponential_bound` | `Results/FiniteDifferenceUpperBound.lean`, `Results/PureFiniteDifference.lean` |
| 20 | every head count on at most four input bits | `pureRoPEComputable_iff_vanilla_of_input_le_four`, `vanilla_three_computes_fourBit_nonparity` | `Results/RoPEFourInputs.lean` |
| 21 | complement-invariant three-head classifiers use at most four vanilla heads | `vanilla_four_of_pureRoPE_three_complement` | `Results/RoPEThreeComplement.lean` |
| 22 | pure minimum three versus vanilla minimum four to six | `PureThreeReplicatedGrid.eventually_complexity_separation`, `not_universal_pureRoPEHStar_eq_SharedHStar` | `Results/PureThreeSeparation.lean` |
| 22 | separation at every sufficiently large input length | `pureRoPE_separation_every_large_input_length` | `Results/PureSeparationAllLargeInputs.lean` |

`Results/InputPaddingInvariance.lean` proves exact invariance of all four minimum
counts under adding unused bits. `Results/RoPEBoundaryCases.lean` states the
zero-head and empty-input cases explicitly. `Model/PureRoPEHeadSchedules.lean`
also permits a different free frequency list in each head and proves equivalence
to the common standard-frequency architecture.

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

`Atoms/RoPEReorientation.lean` checks the coefficient and antipodal identities
of the original Theorem 15. The stronger Theorem 16 uses a token-endpoint
construction in `Results/RoPETwoHeads.lean`. Its strict perturbations are proved
in `Atoms/RoPEStrictness.lean`, including a nondegenerate representation at every
head count. `Results/RoPEArchitecturalComparison.lean` composes the two-head
result with the literal bridge and defines the architectural minimum counts.
No existing vanilla definition is changed.

The all-head structured results are
`AffineStatistic.computable_of_collinear_denominators` and
`AffineStatistic.computable_of_denominator_plane`. The reciprocal specialization
`vanilla_three_of_zero_constant_reciprocals` is in
`Results/ReciprocalUpperBound.lean`. The route obstructions in
`Atoms/RoPEShearObstruction.lean`, `Atoms/RoPEProjectiveObstruction.lean`,
`Atoms/CubicPencilObstruction.lean`, and `Atoms/RoPEArrowhead.lean` concern
specific transformations. None establishes a Boolean head-count separation.
`Examples/RoPEApproximation.lean` proves a positive uniform one-head score gap,
which likewise does not separate Boolean classifications.
