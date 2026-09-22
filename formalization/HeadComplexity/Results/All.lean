import HeadComplexity.Results.RestrictionLowerBounds
import HeadComplexity.Results.ExactFamilies
import HeadComplexity.Results.ThresholdDegree
import HeadComplexity.Results.WeightedUpperBound
import HeadComplexity.Results.FractionalNormalForm
import HeadComplexity.Results.LowComplexity
import HeadComplexity.Results.SymmetricComplexity
import HeadComplexity.Results.StrictSeparation
import HeadComplexity.Results.ClearedNormalForm
import HeadComplexity.Results.SymmetricFaceLowerBound
import HeadComplexity.Results.PositiveWeightedSignDegree
import HeadComplexity.Results.WeightedFaceExact
import HeadComplexity.Results.DeterminantSpan
import HeadComplexity.Results.ThresholdDegreeSpan
import HeadComplexity.Results.CountingLowerBound
import HeadComplexity.Results.DeterminantFeatureBridge
import HeadComplexity.Results.StructuralInvariances
import HeadComplexity.Results.DummyVariables
import HeadComplexity.Results.PartitionSignRank
import HeadComplexity.Results.MultiwaySignTensorRank
import HeadComplexity.Results.SliceRankTwo
import HeadComplexity.Results.PositiveProjection
import HeadComplexity.Results.PositiveMultigrid
import HeadComplexity.Results.AffineFreeSparsity
import HeadComplexity.Results.FourierSupport
import HeadComplexity.Results.AtomicMarginSparsification
import HeadComplexity.Results.AtomicCondition
import HeadComplexity.Results.AffineCylinderThreshold
import HeadComplexity.Results.OneBitGateThresholdDegree
import HeadComplexity.Results.ParityBlockThresholdDegree
import HeadComplexity.Results.CalibratedThresholdVote
import HeadComplexity.Results.OneBitNonXorGate
import HeadComplexity.Results.RawCalibratedVote
import HeadComplexity.Results.PositiveOrderOneBitGate
import HeadComplexity.Results.SecantObstruction
import HeadComplexity.Results.AffineSlab
import HeadComplexity.Results.TwoBlockAffineGridStrip
import HeadComplexity.Results.EqualityExact
import HeadComplexity.Results.AffineStatisticSignChanges
import HeadComplexity.Results.LowAffineCylinderCost
import HeadComplexity.Results.SmallDimensionExactCertificate

set_option linter.style.header false

/-!
# Main results: machine-checked entry points developed so far

This is the table of contents for theorem writeups that currently have Lean
implementations. Each `alias` below elaborates the named declaration and keeps
the public result surface connected to its existing theorem note. The broader
`theorems/` directory also contains artifact-backed and literature-dependent
results that are not yet kernel-checked here. Every declaration exported from
this file must be axiom-clean (`[propext, Classical.choice, Quot.sound]`).

See `README.md` for the theorem↔file map and `PROOF_OVERVIEW.md` for the proof
architecture.
-/

namespace HeadComplexity

/-! ## Results regarding softmax beyond the H* -/

/-- **Theorem 1.** The numerator, restricted to two coordinates, splits additively. -/
alias theorem1_additive_split := restricted_numerator_additive_split

/-- **Theorem 2.** Antipode identity for the restricted numerator. -/
alias theorem2_antipode := restricted_numerator_antipode

/-! ## Lower bound results for H* -/

/-- **Theorem 3.** A checkerboard restriction forces `H* ≥ 2`. -/
alias theorem3_checkerboard := checkerboard_restriction_HStar_ge_two

/-! ## Results for H* for specific boolean functions -/

/-- **Theorem 4.** Every monotone symmetric threshold has `H* = 1`. -/
alias theorem4_threshold := HStar_threshold

/-- **Theorem 5.** Internal exact-count predicates have `H* = 2`. -/
alias theorem5_exact := HStar_exact

/-- **Theorem 8.** Parity needs one head per bit: `H*(XOR_n) = n`. -/
alias theorem8_parity := HStar_parity

/-! ## Results regarding threshold degree beyond the H* -/

/-- **Theorem 6.** Threshold degree is bounded by head complexity:
`computableWithHeadsN n H f → ThresholdDegLE f H`. -/
alias theorem6_degree_le := degree_le_of_computableWithHeadsN

/-- **Theorem 7.** Parity has threshold degree exactly `n`. -/
alias theorem7_parity_degree := parity_thresholdDeg

/-! ## Upper bound results for H* -/

/-- **Theorem 9.** Weighted-sum upper bound `H* ≤ M − 1` … -/
alias theorem9_weighted := HStar_le_weighted_sum

/-- … and the universal bound `H* ≤ 2ⁿ − 1`. -/
alias theorem9_universal := HStar_le_universal_boolean

/-! ## Exact results for H* -/

/-- **Theorem 10.** Exact linear-fractional normal form: `H*(f) = L_frac(f)`. -/
alias theorem10_normal_form := HStar_eq_Lfrac

/-- **Theorem 10.** The same normal form for the literal shared-embedding model. -/
alias theorem10_shared_embedding_per_head_count :=
  computableWithSharedHeadsN_iff_fracComputable

/-- **Theorem 10.** Exact shared-embedding head complexity equals `L_frac`. -/
alias theorem10_shared_embedding_normal_form := SharedHStar_eq_Lfrac

/-- **Theorem 11.** `H* = 0` iff `f` is constant … -/
alias theorem11_level0 := HStar_eq_zero_iff

/-- … and `H* = 1` iff `f` is a nonconstant linear threshold function. -/
alias theorem11_level1 := HStar_eq_one_iff

/-- **Theorem 12.** Symmetric sign-change characterization:
`H*(symmetricFn F) = signChanges n F`. -/
alias theorem12_symmetric := HStar_symmetricFn

/-! ## Separation results for H* -/

/-- **Theorem 13.** Threshold degree can be strictly smaller than head
complexity. -/
alias theorem13_strict_separation := f10_strict_separation

/-! ## Lean interfaces for existing structural results -/

/-- Cleared-polynomial refinement of the linear-fractional normal form used by
the existing restriction and sign-rank arguments. -/
alias theorem28_cleared_polynomial_interface := cleared_polynomial_normal_form

/-- Restriction corollary of the symmetric sign-change theorem: every symmetric
coordinate face gives an ambient lower bound. -/
alias theorem12_symmetric_face_corollary := HStar_lower_bound_of_symmetric_face

/-- Polynomial-certificate presentation of the positive-projection sandwich
from the existing theorem 69 writeup. -/
alias theorem69_positive_projection_sandwich :=
  thresholdDeg_le_HStar_le_positiveWeightedSignDeg

/-- Matching endpoints in the theorem 69 sandwich determine head complexity. -/
alias theorem69_positive_projection_exactness :=
  HStar_eq_thresholdDeg_of_eq_positiveWeightedSignDeg

/-- On symmetric functions, the positive-projection polynomial presentation
specializes to the theorem 12 sign-change count. -/
alias theorem12_positive_projection_degree :=
  positiveWeightedSignDeg_symmetricFn

/-- Threshold-degree specialization used in theorem 12. -/
alias theorem12_threshold_degree := thresholdDeg_symmetricFn

/-- Fixed-certificate form of theorem 69 exactness. -/
alias theorem69_fixed_projection_exactness :=
  HStar_eq_thresholdDeg_of_weightedPolynomial

/-- The theorem 12 restriction corollary combined with the theorem 69 upper
certificate. -/
alias theorem69_face_certificate_exactness :=
  HStar_eq_of_symmetricFace_and_weightedPolynomial

/-- Polynomial presentation of theorem 69's low-alternation exact-two case. -/
alias theorem69_low_alternation_two :=
  HStar_eq_two_of_positiveWeightedSignDeg_le_two

/-- Checked positive weighted-band instance of theorem 69. -/
alias theorem69_weighted_band_instance := HStar_weightedOpenBand_eq_two

/-- Checked nonsymmetric three-bit instance of theorem 69. -/
alias theorem69_isolated_xor_instance := HStar_isolatedXor3

/-! ## Additional formalizations of existing theorem notes -/

/-- **Theorem 21.** A universal cleared-span certificate bounds every Boolean
function by its denominator count. -/
alias theorem21_determinant_span_schema := ClearedSpanCertificate.HStar_le

/-- **Theorem 30.** A degree-restricted cleared-span certificate computes every
Boolean function whose threshold degree is at most the certified degree. -/
alias theorem30_threshold_degree_span :=
  DegreeClearedSpanCertificate.HStar_le_of_ThresholdDegLE

/-- **Theorem 30.** Such a fixed-denominator span needs at least as many
nonredundant cleared features as the low-degree polynomial space. -/
alias theorem30_span_dimension_obstruction :=
  DegreeClearedSpanCertificate.dimension_obstruction

/-- **Theorem 26.** `H` relaxed affine fractions use exactly
`1 + 2 * H * (n + 1)` real parameters. -/
alias theorem26_counting_parameter_count := card_countingParameter

/-- **Theorem 26.** Every `H`-head function is a strict sign pattern of the
fixed-input cleared parameter polynomials. -/
alias theorem26_strict_sign_pattern_reduction :=
  card_headComputableFunctions_le_strictPatterns

/-- **Theorem 26.** Warren's strict sign-pattern estimate gives the displayed
exact real-valued count for `H`-head functions. -/
alias theorem26_warren_count := card_headComputableFunctions_le_warren

/-- **Theorem 26.** Under Warren's estimate, the number of `H`-head functions
is at most `2^(35 * n^2 * H)` in the stated finite regime. -/
alias theorem26_coarse_count :=
  card_headComputableFunctions_le_two_pow_of_warren

/-- **Theorem 26.** Under Warren's estimate, some truth table needs more than
`H` heads whenever `35 * n^2 * H < 2^n`. -/
alias theorem26_exists_hard_function := exists_HStar_gt_of_warren

/-- **Theorem 26.** Conditional explicit division form of the worst-case
`Omega(2^n / n^2)` lower bound. -/
alias theorem26_worst_case_lower_bound :=
  worstCaseHeadComplexity_gt_div_of_warren

/-- **Theorem 26.** Universal interpolation gives the worst-case upper bound
`W(n) ≤ 2^n - 1`. -/
alias theorem26_worst_case_upper_bound := worstCaseHeadComplexity_le

/-- **Theorem 21.** A nonzero selected cleared-feature determinant supplies a
universal head upper bound. -/
alias theorem21_determinant_feature_schema :=
  ClearedFeatureDeterminantCertificate.HStar_le

/-- **Theorem 21.** Modular right-inverse certificate form for large generated
cleared-feature matrices. -/
alias theorem21_modular_right_inverse_schema :=
  ClearedFeatureDeterminantCertificate.HStar_le_of_integer_zmod_feature_rightInverse

/-- **Theorem 28.** Head complexity is invariant under coordinate
permutations. -/
alias theorem28_permutation_invariance := HStar_permute

/-- **Theorem 28.** Head complexity is invariant under the global input bit
flip. -/
alias theorem28_bit_flip_invariance := HStar_flip

/-- **Theorem 28.** Head complexity is invariant under output complement. -/
alias theorem28_complement_invariance := HStar_complement

/-- **Theorem 28.** Adding a block of dummy variables preserves head
complexity. -/
alias theorem28_dummy_variables := HStar_dummyVariables

/-- **Theorem 28.** Junta transport preserves the exact head complexity. -/
alias theorem28_junta_transport := HStar_juntaTransport

/-- **Theorem 28.** Tangent and degree expansions jointly bound partition
sign-rank. -/
alias theorem28_partition_sign_rank := partitionSignRank_le_all

/-- **Theorem 28.** Partition sign-rank gives a logarithmic lower bound on
head complexity. -/
alias theorem28_partition_sign_rank_inversion :=
  clog_partitionSignRank_sub_one_le_HStar

/-- **Theorem 45.** A strict Walsh support certificate gives its exact
support-cost head upper bound. -/
alias theorem45_fourier_support := FourierSupportCertificate.HStar_le

/-- **Theorem 45.** Uniform Fourier error below one implies the corresponding
support-cost upper bound. -/
alias theorem45_fourier_tail :=
  FourierSupportCertificate.HStar_le_of_fourier_uniform_lt_one

/-- **Theorem 48.** Affine-free polynomial-threshold sparsity upper-bounds head
complexity. -/
alias theorem48_affine_free_sparsity := HStar_le_affineFreeSparsity

/-- **Theorem 48.** Affine-free sparsity never exceeds ordinary PTF
sparsity. -/
alias theorem48_sparsity_hierarchy := affineFreeSparsity_le_ptfSparsity

/-- **Theorem 48.** Threshold degree supplies the uniform affine-free support
bound. -/
alias theorem48_degree_support_bound :=
  HStar_le_one_add_sum_choose_of_ThresholdDegLE

/-- **Theorem 195.** A normalized finite atomic-margin certificate can be
sampled to an exact representation with the explicit natural head bound. -/
alias theorem195_atomic_margin_sample_bound :=
  AtomicMarginCertificate.HStar_le_atomicSampleCount

/-- **Theorem 195.** Output-normalized atomic margin gives a quadratic head
bound with the explicit absolute constant `33`. -/
alias theorem195_atomic_margin_sparsification :=
  AtomicMarginCertificate.HStar_real_le_atomicCondition

/-- **Theorem 195.** Literal infimum form of the output-normalized atomic
condition-number upper bound. -/
alias theorem195_atomic_condition_number :=
  HStar_real_le_atomicConditionNumber

/-- **Theorem 62.** Every affine slab has head complexity at most two. -/
alias theorem62_affine_slab_upper_bound := HStar_affineSlab_le_two

/-- **Theorem 62.** Affine slabs have the exact zero, one, or two
classification. -/
alias theorem62_affine_slab_classification := HStar_affineSlab_classification

/-- **Theorem 49.** Equality of two nonempty Boolean blocks has exact head
complexity two. -/
alias theorem49_equality_exact := HStar_equality

/-- **Theorem 49.** Equality of two nonempty Boolean blocks has exact threshold
degree two. -/
alias theorem49_equality_threshold_degree := thresholdDeg_equality

/-- **Theorem 63.** Sign changes along an arbitrary affine statistic give the
exact small-change cases and the support-sensitive general upper bound. -/
alias theorem63_affine_statistic_sign_changes :=
  AffineStatisticProfile.signChange_four_cases

/-- **Theorem 69.** Literal ordered positive-projection sandwich. -/
alias theorem69_ordered_projection_sandwich :=
  thresholdDeg_le_HStar_le_positiveProjectionSignChanges

/-- **Theorem 69.** Literal ordered positive-projection endpoint exactness. -/
alias theorem69_ordered_projection_exactness :=
  HStar_eq_thresholdDeg_of_eq_positiveProjectionSignChanges

/-- **Theorem 69.** Equality of the ordered and polynomial presentations of
the optimized positive-projection invariant. -/
alias theorem69_projection_presentations_equal :=
  positiveProjectionSignChanges_eq_positiveWeightedSignDeg

/-- **Theorem 82.** Exact threshold-degree trichotomy for an arbitrary
one-bit gate. -/
alias theorem82_one_bit_gate_threshold_degree :=
  oneBitGate_thresholdDeg_trichotomy

/-- **Theorem 83.** XOR with a fresh parity block raises threshold degree by
exactly the size of the block. -/
alias theorem83_parity_block_threshold_degree := thresholdDeg_parityBlockXor

/-- **Theorem 83.** The parity-block degree identity gives the corresponding
head-complexity lower bound. -/
alias theorem83_parity_block_lower_bound :=
  thresholdDeg_add_le_HStar_parityBlockXor

/-- **Theorem 83.** Minimum polynomial-threshold sparsity gives the stated
exponential sparse-PTF fallback upper bound. -/
alias theorem83_parity_block_sparse_upper :=
  HStar_parityBlockXor_le_ptfSparsity

/-- **Theorem 85.** A weighted threshold vote whose raw features have
one-atom approximations within the strict margin costs at most one head per
feature. -/
alias theorem85_calibrated_threshold_vote := HStar_thresholdVote_le

/-- **Theorem 87.** Combining an arbitrary feature with one fresh raw bit
through any gate other than XOR or XNOR costs at most one extra head. -/
alias theorem87_one_bit_non_xor_recursion :=
  HStar_freshBitGate_le_succ_of_ne_xor_xnor

/-- **Theorem 93.** Raw calibration costs add over the active features in a
strict weighted vote. -/
alias theorem93_raw_calibrated_vote := HStar_thresholdVote_le_rawVoteCost

/-- **Theorem 93.** The exact multilinear affine-free support costs give a
concrete fallback for a strict weighted vote. -/
alias theorem93_exact_support_vote :=
  HStar_thresholdVote_le_exactAffineFreeVoteCost

/-- **Theorem 110.** Threshold degree, head complexity, affine-cylinder cost,
cylinder cost, and affine-free sparsity form the stated sandwich. -/
alias theorem110_affine_cylinder_sandwich :=
  thresholdDeg_le_HStar_le_actc_le_min_ctc_affineFreeSparsity

/-- **Theorem 109.** Affine-cylinder cost at most two gives the exact universal
zero-, one-, or two-head classification. -/
alias theorem109_low_affine_cylinder_cost := HStar_low_actc_classification

/-- **Theorem 138.** A raw bit coupled to one positive statistic is compiled
with its polynomial degree many heads. -/
alias theorem138_positive_statistic_raw_bit :=
  HStar_le_of_positiveStatisticRawBitDegLE

/-- **Theorem 141.** Degree-tight positive-projection features have the exact
one-bit gate table. -/
alias theorem141_degree_tight_gate_classification :=
  oneBitGate_HStar_exact_of_degree_tight_positiveProjection

/-- **Theorem 144.** Universal one-bit gate sandwich in literal ordered
positive-projection form. -/
alias theorem144_positive_order_gate_sandwich :=
  oneBitGate_HStar_sandwich_positiveProjection

/-- **Theorem 170.** A finite positive-statistic multigrid costs at most the
number of label alternations along its lexicographic traversal. -/
alias theorem170_positive_lexicographic_multigrid :=
  PositiveLexMultigrid.HStar_le_alternations

/-- **Theorem 170.** Every one-block fiber of a multigrid certificate gives a
restriction lower bound. -/
alias theorem170_multigrid_fiber_lower_bound :=
  PositiveLexMultigrid.HStar_fiber_le

/-- **Theorem 170.** Matching threshold degree and multigrid alternations give
the exact head complexity. -/
alias theorem170_multigrid_endpoint_exactness :=
  PositiveLexMultigrid.HStar_eq_of_thresholdDeg_eq_alternations

/-- **Theorem 173.** Positive multigrid cost upper-bounds head complexity. -/
alias theorem173_positive_multigrid_cost :=
  HStar_le_positiveMultigridCost

/-- **Theorem 173.** Optimized positive-projection alternations are bounded by
positive multigrid cost. -/
alias theorem173_positive_projection_le_multigrid_cost :=
  positiveProjectionSignChanges_le_positiveMultigridCost

/-- **Theorem 173.** Matching threshold degree and positive multigrid cost give
the exact head complexity. -/
alias theorem173_multigrid_endpoint_exactness :=
  HStar_eq_of_thresholdDeg_eq_positiveMultigridCost

/-- **Theorem 173.** Positive multigrid cost is invariant under output
complement. -/
alias theorem173_multigrid_complement_invariance :=
  positiveMultigridCost_complement

/-- **Theorem 173.** Positive multigrid cost is invariant under simultaneous
coordinate permutation of the function and partition. -/
alias theorem173_multigrid_permutation_invariance :=
  positiveMultigridCost_permute

/-- **Theorem 179.** Two-block affine grid strips have the exact zero-, one-,
or two-head classification. -/
alias theorem179_affine_grid_strip_classification :=
  HStar_twoBlockAffineGridStrip_classification

/-- **Theorem 179.** For two nonempty blocks, affine-grid-strip head
complexity equals strict bivariate grid threshold degree. -/
alias theorem179_affine_grid_strip_exactness :=
  HStar_affineGridStrip_eq_bivariateGridThresholdDeg

/-- **Theorem 190.** Every cleared `H`-head score with `H ≥ 2` has a
homogeneous degree-`H` slice-rank-two strict sign realization whose second
linear generator is an actual positive denominator. -/
alias theorem190_slice_rank_two :=
  homogeneousSliceRankTwoSignRep_of_computableWithHeadsN

/-- **Theorem 190.** Failure of every homogeneous slice-rank-two strict sign
realization forces head complexity strictly above `H`. -/
alias theorem190_slice_rank_two_obstruction :=
  HStar_gt_of_no_homogeneousSliceRankTwoSignRep

/-- **Theorem 192.** Every coordinate partition of an `H`-head function has
multiway sign CP rank at most `k * (k^H - (k-1)^H)`. -/
alias theorem192_multiway_sign_tensor_rank :=
  multiwaySignCPRank_le_of_HStar_le

/-- **Theorem 192.** The ambient fiber expansion bounds a partition tensor by
`2^(n - |I_j|)` for each omitted mode `j`. -/
alias theorem192_ambient_cp_rank_ceiling :=
  multiwaySignCPRank_le_two_pow_complement

/-- **Theorem 192.** On at most `2H + 1` inputs, the ambient ceiling of every
partition into nonempty blocks is already below the tangent count. -/
alias theorem192_input_count_barrier :=
  multiwaySignCPRank_le_tangent_count_of_input_bound

/-- **Theorem 193.** Exact positive-secant diagonal blow-up equivalence for
oriented Boolean-cube products. -/
alias theorem193_positive_secant_blowup :=
  PositiveSecant.orientedSecantFeasible_iff_blowupFeasible

/-- **Theorem 193.** Infeasibility of every positive blow-up orientation branch
gives the strict head-complexity lower bound. -/
alias theorem193_positive_secant_obstruction :=
  SignedSecant.H_lt_HStar_of_no_positiveBlowup

/-- **Theorem 194.** Exact signed-secant diagonal blow-up equivalence. -/
alias theorem194_signed_secant_blowup :=
  SignedSecant.orientedSignedSecantFeasible_iff_signedBlowupFeasible

/-- **Theorem 194.** The symmetry-reduced signed-blow-up obstruction implies
the strict head-complexity lower bound. -/
alias theorem194_signed_secant_obstruction :=
  SignedSecant.H_lt_HStar_of_no_signedBlowup_countBranchChartTypes

/-- **Theorem 183 checker interface.** A successful kernel check of complete
four-bit certificate data proves exact equality in every dimension at most
four. The archived payload itself is not embedded by this alias. -/
alias theorem183_checked_small_dimension_exactness :=
  smallDimension_exact_of_check_eq_true

end HeadComplexity
