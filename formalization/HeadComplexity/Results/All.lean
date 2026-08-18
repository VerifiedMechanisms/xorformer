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
import HeadComplexity.Results.DeterminantFeatureBridge
import HeadComplexity.Results.StructuralInvariances
import HeadComplexity.Results.DummyVariables
import HeadComplexity.Results.PartitionSignRank
import HeadComplexity.Results.PositiveProjection
import HeadComplexity.Results.AffineFreeSparsity
import HeadComplexity.Results.FourierSupport
import HeadComplexity.Results.AtomicMarginSparsification
import HeadComplexity.Results.AffineCylinderThreshold
import HeadComplexity.Results.OneBitGateThresholdDegree
import HeadComplexity.Results.PositiveOrderOneBitGate
import HeadComplexity.Results.SecantObstruction
import HeadComplexity.Results.AffineSlab
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

/-- **Theorem 62.** Every affine slab has head complexity at most two. -/
alias theorem62_affine_slab_upper_bound := HStar_affineSlab_le_two

/-- **Theorem 62.** Affine slabs have the exact zero, one, or two
classification. -/
alias theorem62_affine_slab_classification := HStar_affineSlab_classification

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

/-- **Theorem 110.** Threshold degree, head complexity, affine-cylinder cost,
cylinder cost, and affine-free sparsity form the stated sandwich. -/
alias theorem110_affine_cylinder_sandwich :=
  thresholdDeg_le_HStar_le_actc_le_min_ctc_affineFreeSparsity

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

/-- **Theorem 193.** Exact positive-secant diagonal blow-up equivalence for
oriented Boolean-cube products. -/
alias theorem193_positive_secant_blowup :=
  PositiveSecant.orientedSecantFeasible_iff_blowupFeasible

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
