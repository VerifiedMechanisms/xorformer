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
import HeadComplexity.Results.PureRoPETwoHeads
import HeadComplexity.Results.PureRoPETwelvePairExact
import HeadComplexity.Results.ThreeFaceFourHeads
import HeadComplexity.Results.FourHeadCrossOnlyExample
import HeadComplexity.Results.PureFourHeadLocalPattern
import HeadComplexity.Results.TwoProductsThreeHeads
import HeadComplexity.Results.FourHeadBlockComplement
import HeadComplexity.Results.ThreeHeadRegularBlockPattern
import HeadComplexity.Results.ThreeHeadEmbeddedPattern
import HeadComplexity.Results.FourHeadQuarticPattern
import HeadComplexity.Polynomial.ThreeHeadReplication
import HeadComplexity.Results.PureRoPEReplication

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
head count. The literal fixed-frequency interpolation bridge is handwritten. -/
alias theorem14_pure_simulation := pureRoPEComputable_of_vanilla

/-- **Theorem 14.** Pure rotary scalar head complexity is at most vanilla. -/
alias theorem14_pure_le_vanilla := pureRoPEHStar_le_vanilla

/-- **Theorem 14.** Retaining additive positions cannot increase the scalar count. -/
alias theorem14_retained_le_pure := retainedRoPEHStar_le_pure

/-- **Theorem 14.** Threshold degree lower-bounds the retained rotary scalar count. -/
alias theorem14_degree_lower_bound := thresholdDeg_le_retainedRoPEHStar

/-- **Theorem 14.** Both rotary scalar complexities equal sign changes on symmetric functions. -/
alias theorem14_symmetric := ropeHStar_symmetric

/-- **Theorem 16.** Pure rotary and vanilla Boolean classes agree at two heads. -/
alias theorem16_pure_two_head_equivalence := pureRoPEComputable_two_iff_vanilla

/-- **Theorem 16.** The minimum counts agree whenever pure rotary needs at most two heads. -/
alias theorem16_pure_two_head_complexity := pureRoPEHStar_eq_vanilla_of_le_two

/-- **Theorem 16.** Any strict pure rotary improvement needs at least three pure heads. -/
alias theorem16_separation_requires_three := pureRoPE_separation_requires_three_heads

/-- **Theorem 17.** The twelve-bit quadratic has threshold degree two and
exactly four pure rotary and vanilla heads. -/
alias theorem17_twelve_pair_exact := PureRoPEThreeHead.TwelvePair.exact_complexities

/-- **Theorem 17.** The literal original shared architecture also needs four heads. -/
alias theorem17_twelve_pair_shared := PureRoPEThreeHead.TwelvePair.sharedHStar_eq_four

/-- **Theorem 18.** A union of three nonnegative affine zero sets has a
four-head realization in the original shared architecture. -/
alias theorem18_three_faces := ThreeFaceFourHeads.computable_four

/-- **Theorem 19.** The cross-only local pattern excludes all four-head
vanilla representations, including degenerate denominator orientations. -/
alias theorem19_cross_only_vanilla_lower := FourHeadLocalPattern.crossOnly_HStar_ge_five

/-- **Theorem 19.** An explicit seventeen-bit cubic has threshold degree three
and needs at least five vanilla heads. Its pure four-head upper bound is open. -/
alias theorem19_explicit_target := FourHeadCrossOnlyExample.certified_target

/-- **Theorem 19.** The stronger original local pattern also excludes four
pure rotary heads, so that pattern cannot give a four-versus-five separation. -/
alias theorem19_original_pattern_pure_lower := PureFourHeadLocalPattern.pureRoPEHStar_ge_five

/-- **Theorem 20.** Cubic parity faces exclude every vanilla three-head model. -/
alias theorem20_tripartite_lower := ThreeHeadTripartitePattern.HStar_ge_four

/-- **Theorem 20.** The obstruction allows arbitrary auxiliary coordinates. -/
alias theorem20_embedded_lower := ThreeHeadEmbeddedPattern.HStar_ge_four

/-- **Theorem 21.** Quartic parity faces exclude every vanilla four-head model. -/
alias theorem21_quartic_lower := FourHeadQuarticPattern.HStar_ge_five

/-- **Theorem 22, upper-bound component only.** The explicit replicated,
biased classifier has three exact pure scalar atoms. The vanilla lower bound
and the literal rotary-matrix bridge remain handwritten. -/
alias theorem22_explicit_pure_upper := PureRoPEReplication.explicitFunction_pure_three

/-- **Theorem 22, algebraic component only.** Exact signs of the biased cleared
polynomial on the entire cube. This does not assert a vanilla lower bound. -/
alias theorem22_explicit_cleared_sign := PureRoPEReplication.explicitFunction_full_cube_sign

end HeadComplexity
