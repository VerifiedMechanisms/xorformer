# head-complexity

Lean 4 formalization of the head-complexity results for one-layer attention. The
definitions and theorems mirror the informal proofs in the top-level `theorems/` writeups.

## Status: core results through theorem 13, plus later theorem-stack coverage

The core results through theorem 13 are machine-checked, with no `sorry` or
`admit`, depending only on the three standard Lean axioms
`[propext, Classical.choice, Quot.sound]`. The full build runs a
`#print axioms` gate. `H*` is `HStar`, the least number of heads realizing
`f`.

The formalization also covers previously stated results from the wider theorem
stack. In particular, it provides the coordinate-restriction API used with
theorem 12 and a polynomial-certificate presentation of the positive-projection
sandwich and exactness result in theorem 69. These are Lean formalizations of
existing mathematical statements, not newly numbered theorems.

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
| 10 | linear-fractional normal form `H*=L_frac` | `HStar_eq_Lfrac` | `Results/FractionalNormalForm.lean` |
| 11 | levels 0/1: const / nonconstant LTF | `HStar_eq_zero_iff`, `HStar_eq_one_iff` | `Results/LowComplexity.lean` |
| 12 | symmetric `H*=C(F)` (sign changes) | `HStar_symmetricFn` | `Results/SymmetricComplexity.lean` |
| 13 | explicit strict separation `deg±<H*` | `f10_strict_separation` | `Results/StrictSeparation.lean` |

### Additional theorem-stack coverage

| Existing note | Lean coverage | File |
|---|---|---|
| theorem 12 with restriction monotonicity from theorem 28 | `HStar_restrict_le`, `HStar_lower_bound_of_symmetric_face` | `Results/SymmetricFaceLowerBound.lean` |
| theorem 21 determinant-span schema | `ClearedSpanCertificate.HStar_le` | `Results/DeterminantSpan.lean` |
| theorem 26 counting lower bound, conditional on Warren's estimate | `card_headComputableFunctions_le_warren`, `card_headComputableFunctions_le_two_pow_of_warren`, `worstCaseHeadComplexity_gt_div_of_warren` | `Results/CountingLowerBound.lean` |
| theorem 30 threshold-degree span schema | `DegreeClearedSpanCertificate.HStar_le_of_ThresholdDegLE`, `DegreeClearedSpanCertificate.dimension_obstruction` | `Results/ThresholdDegreeSpan.lean` |
| theorem 28 invariances, juntas, and sign-rank | `HStar_dummyVariables`, `HStar_complement`, `partitionSignRank_le_all` | `Results/DummyVariables.lean`, `Results/StructuralInvariances.lean`, `Results/PartitionSignRank.lean` |
| theorem 45 Fourier support cost | `FourierSupportCertificate.HStar_le` | `Results/FourierSupport.lean` |
| theorem 48 affine-free sparsity | `HStar_le_affineFreeSparsity`, `affineFreeSparsity_le_ptfSparsity` | `Results/AffineFreeSparsity.lean` |
| theorem 49 equality | `HStar_equality`, `thresholdDeg_equality` | `Results/EqualityExact.lean` |
| theorem 62 affine slabs | `HStar_affineSlab_le_two`, `HStar_affineSlab_classification` | `Results/AffineSlab.lean` |
| theorem 63 arbitrary affine-statistic sign changes | `AffineStatisticProfile.signChange_four_cases` | `Results/AffineStatisticSignChanges.lean` |
| theorem 69 positive-projection sandwich and tightness | `thresholdDeg_le_HStar_le_positiveProjectionSignChanges`, `HStar_eq_thresholdDeg_of_eq_positiveProjectionSignChanges` | `Results/PositiveProjection.lean` |
| theorem 69 fixed-certificate and checked instances | `HStar_eq_thresholdDeg_of_weightedPolynomial`, `HStar_eq_two_of_positiveWeightedSignDeg_le_two`, `HStar_isolatedXor3` | `Results/PositiveWeightedSignDegree.lean`, `Results/WeightedFaceExact.lean` |
| theorem 82 one-bit threshold degree | `oneBitGate_thresholdDeg_trichotomy` | `Results/OneBitGateThresholdDegree.lean` |
| theorem 83 parity-block amplification | `thresholdDeg_parityBlockXor`, `HStar_parityBlockXor_le_ptfSparsity` | `Results/ParityBlockThresholdDegree.lean` |
| theorem 85 calibrated threshold votes | `HStar_thresholdVote_le` | `Results/CalibratedThresholdVote.lean` |
| theorem 87 one-bit non-XOR recursion | `HStar_freshBitGate_le_succ_of_ne_xor_xnor` | `Results/OneBitNonXorGate.lean` |
| theorem 93 raw-calibrated vote support | `HStar_thresholdVote_le_rawVoteCost`, `HStar_thresholdVote_le_exactAffineFreeVoteCost` | `Results/RawCalibratedVote.lean` |
| theorem 109 low affine-cylinder cost exactness | `HStar_low_actc_classification` | `Results/LowAffineCylinderCost.lean` |
| theorem 110 affine-cylinder sandwich | `thresholdDeg_le_HStar_le_actc_le_min_ctc_affineFreeSparsity` | `Results/AffineCylinderThreshold.lean` |
| theorems 138, 141, and 144 positive-statistic gates | `HStar_le_of_positiveStatisticRawBitDegLE`, `oneBitGate_HStar_sandwich_positiveProjection`, `oneBitGate_HStar_exact_of_degree_tight_positiveProjection` | `Results/PositiveOrderOneBitGate.lean` |
| theorem 170 positive lexicographic multigrids | `PositiveLexMultigrid.HStar_le_alternations`, `PositiveLexMultigrid.HStar_fiber_le` | `Results/PositiveMultigrid.lean` |
| theorem 173 positive multigrid cost | `HStar_le_positiveMultigridCost`, `positiveProjectionSignChanges_le_positiveMultigridCost`, `HStar_eq_of_thresholdDeg_eq_positiveMultigridCost` | `Results/PositiveMultigrid.lean` |
| theorem 179 two-block affine grid strips | `HStar_twoBlockAffineGridStrip_classification`, `HStar_affineGridStrip_eq_bivariateGridThresholdDeg` | `Results/TwoBlockAffineGridStrip.lean` |
| theorem 183 finite-checker soundness | `smallDimension_exact_of_check_eq_true` | `Results/FourBitCertificateChecker.lean`, `Results/SmallDimensionExactCertificate.lean` |
| theorem 190 homogeneous slice-rank-two obstruction | `homogeneousSliceRankTwoSignRep_of_computableWithHeadsN`, `HStar_gt_of_no_homogeneousSliceRankTwoSignRep` | `Results/SliceRankTwo.lean` |
| theorem 192 multiway sign CP-rank bound and input-count barrier | `multiwaySignCPRank_le_of_HStar_le`, `multiwaySignCPRank_le_tangent_count_of_input_bound` | `Results/MultiwaySignTensorRank.lean` |
| theorem 193 positive-secant blow-up and obstruction | `PositiveSecant.orientedSecantFeasible_iff_blowupFeasible`, `SignedSecant.H_lt_HStar_of_no_positiveBlowup` | `Polynomial/PositiveSecantBlowup.lean`, `Results/SecantObstruction.lean` |
| theorem 194 signed-secant obstruction | `SignedSecant.H_lt_HStar_of_no_signedBlowup_countBranchChartTypes` | `Polynomial/SignedSecantBlowup.lean`, `Polynomial/OrientedSecantSymmetry.lean`, `Results/SecantObstruction.lean` |
| theorem 195 atomic-margin sparsification | `HStar_le_atomicSampleCount`, `HStar_real_le_atomicCondition`, `HStar_real_le_atomicConditionNumber` | `Results/AtomicMarginSparsification.lean`, `Results/AtomicCondition.lean` |

Lean exposes both presentations of the theorem 69 invariant.
`positiveProjectionSignChanges` is the literal minimum ordered-image
alternation count $C_{+}$, while `positiveWeightedSignDeg` is its minimum
polynomial-certificate presentation. Their equality is machine-checked as
`positiveProjectionSignChanges_eq_positiveWeightedSignDeg`.

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
