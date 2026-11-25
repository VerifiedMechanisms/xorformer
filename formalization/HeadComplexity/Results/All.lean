import HeadComplexity.Results.RestrictionLowerBounds
import HeadComplexity.Results.ExactFamilies
import HeadComplexity.Results.ThresholdDegree
import HeadComplexity.Results.WeightedUpperBound
import HeadComplexity.Results.FractionalNormalForm
import HeadComplexity.Results.AffineFractionNormalForm
import HeadComplexity.Results.LowComplexity
import HeadComplexity.Results.SymmetricComplexity
import HeadComplexity.Results.StrictSeparation
import HeadComplexity.Results.RoPEComparison
import HeadComplexity.Atoms.RoPEReorientation
import HeadComplexity.Results.RoPEArchitecturalComparison
import HeadComplexity.Results.AffineStatisticUpperBound
import HeadComplexity.Results.DenominatorPlaneUpperBound
import HeadComplexity.Results.FiniteDifferenceUpperBound
import HeadComplexity.Results.RoPESmallInputs
import HeadComplexity.Results.RoPEThreeComplement
import HeadComplexity.Atoms.RoPEProjectiveObstruction
import HeadComplexity.Atoms.RoPEShearObstruction
import HeadComplexity.Atoms.CubicPencilObstruction
import HeadComplexity.Results.RoPEGeneralBounds
import HeadComplexity.Results.ReciprocalUpperBound
import HeadComplexity.Atoms.RoPEArrowhead
import HeadComplexity.Atoms.RoPETiltObstruction
import HeadComplexity.Results.ReciprocalFiniteDifference
import HeadComplexity.Results.ProductDifferenceSign
import HeadComplexity.Results.PureFiniteDifference
import HeadComplexity.Results.PureThreeSeparation
import HeadComplexity.Results.BooleanTangentUpperBound

set_option linter.style.header false

/-!
# Main results: the stack of entry points to the theory developed so far

A machine-checked table of contents. Each foundational `alias` below names the
headline Lean statement for one theorem writeup in `theorems/`. Because the build
elaborates these aliases, this file *verifies* every result. These results must be
axiom-clean (`[propext, Classical.choice, Quot.sound]`).

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

/-- **Theorem 10.** Exact image of the atom coefficient map. -/
alias theorem10_affine_coefficients := AffineFraction.realizable_iff

/-- **Theorem 10.** Exact scores are constants plus sums of
admissible affine ratios, with one ratio per head. -/
alias theorem10_affine_score_normal_form := shared_score_iff_affineFraction

/-- **Theorem 10.** Thresholding preserves each head budget. -/
alias theorem10_affine_per_head_count :=
  computableWithSharedHeadsN_iff_affineFractionComputable

/-- **Theorem 10.** Head complexity is the least ratio count. -/
alias theorem10_affine_complexity := SharedHStar_eq_LaffineFrac

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

/-! ## Rotary scalar models -/

/-- **Theorem 14.** Exact vanilla-to-pure-rotary scalar simulation, at every
head count. Theorem 18 supplies the literal fixed-frequency bridge. -/
alias theorem14_pure_simulation := pureRoPEComputable_of_vanilla

/-- **Theorem 14.** Pure rotary scalar head complexity is at most vanilla. -/
alias theorem14_pure_le_vanilla := pureRoPEHStar_le_vanilla

/-- **Theorem 14.** Retaining additive positions cannot increase the scalar count. -/
alias theorem14_retained_le_pure := retainedRoPEHStar_le_pure

/-- **Theorem 14.** Threshold degree lower-bounds the retained rotary scalar count. -/
alias theorem14_degree_lower_bound := thresholdDeg_le_retainedRoPEHStar

/-- **Theorem 14.** Both rotary scalar complexities equal sign changes on symmetric functions. -/
alias theorem14_symmetric := ropeHStar_symmetric

/-- **Theorem 16.** Pure and vanilla computability agree at every head budget
at most two, without complement invariance. -/
alias theorem16_pure_two_heads := pureRoPEComputable_iff_vanilla_of_le_two

/-- **Theorem 16.** The same result for literal rectangular rotary attention. -/
alias theorem16_architectural_two_heads :=
  standardPureRotaryComputable_iff_vanilla_of_le_two

/-- **Theorem 17.** A polynomial in an arbitrary affine statistic requires at
most its degree bound many vanilla heads. -/
alias theorem17_affine_statistic := AffineStatistic.computable_of_polynomial

/-- **Theorem 17.** Collinear denominator slopes preserve the original head count. -/
alias theorem17_collinear_denominators := AffineStatistic.computable_of_collinear_denominators

/-- **Theorem 17.** A denominator plane containing a positive uniformly oriented
affine form also preserves the original head count. -/
alias theorem17_denominator_plane := AffineStatistic.computable_of_denominator_plane

/-- **Theorem 18.** The exact rectangular pure rotary architecture has the
existing scalar normal form at every head count. -/
alias theorem18_rotary_scalar_bridge :=
  rectangularStandardPureRotaryComputable_iff_scalar

/-- **Theorem 18.** Fixed and free shared frequencies give identical Boolean
head budgets in the exact rectangular architecture. -/
alias theorem18_fixed_free := rectangularStandardPureRotaryComputable_iff_free

/-- **Theorem 19.** Arbitrary positive affine ratios have a general exponential
vanilla head bound. -/
alias theorem19_finite_difference := FiniteDifference.computable_of_positive_denominators

/-- **Theorem 19.** Pure atoms improve the general bound to 2^H-2 for H≥2. -/
alias theorem19_pure_improved_bound := pureRoPEComputable_vanilla_improved_exponential_bound

/-- **Theorem 20.** All head budgets agree for at most four input bits. -/
alias theorem20_small_inputs := pureRoPEComputable_iff_vanilla_of_input_le_four

/-- **Theorem 21.** Complement-invariant three-head pure classifiers need at
most four vanilla heads. No three-head equality is asserted here. -/
alias theorem21_three_head_complement := vanilla_four_of_pureRoPE_three_complement

/-- **Theorem 22.** The explicit replicated family eventually needs exactly
three pure rotary heads and between four and six vanilla heads. -/
alias theorem22_pure_vanilla_separation :=
  PureThreeReplicatedGrid.eventually_complexity_separation

/-- **Theorem 22.** The separation holds in the literal rectangular rotary
architecture with standard fixed or freely chosen frequencies. -/
alias theorem22_architectural_separation :=
  PureThreeReplicatedGrid.exists_rotary_three_not_vanilla_three

/-- **Theorem 22.** Universal equality of the minimum head counts is false. -/
alias theorem22_not_universal_equality := not_universal_pureRoPEHStar_eq_SharedHStar

end HeadComplexity
