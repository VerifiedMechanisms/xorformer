# Beyond the Xorformer Counting Barrier

## Current outcome

This run starts from `aa0cceb140ba75149353f92943b1fba78e7e0ec5`, the required `origin/ar/47c1ff45613b`, and works on `ar/4e24baaa5491`. The original unrestricted definition of `HeadComplexity.worstCaseHeadComplexity`, the head-admissibility structure, and the computability predicates are unchanged.

The requested bound of order $N/n^{3/2}$, every smaller fixed positive power saving, and the explicit $N\log n/n^2$ fallback remain open. The strongest unconditional theorem proved in this run is a finite-constant improvement of the quadratic-denominator bound. No refutation of the original $O(N/n^2)$ conjecture is claimed.

The active research period runs from 2026-11-24 15:27:59 UTC until 2026-11-25 03:27:59 UTC. The final hour includes fresh source builds, complete transitive axiom checks, independent semantic reviews, and a committed handoff.

## Strongest unconditional original-model theorem

Write $N=2^n$. For every integer $n\geq256$,

$$ W(n)\geq\frac{N-1}{n(n+7)}. $$

The exact Lean declaration is `HeadComplexity.BootstrapWeightedCounting.worstCase_real_lower` in [BootstrapWeightedCounting.lean](../../formalization/HeadComplexity/Research/BootstrapWeightedCounting.lean). The public alias is `HeadComplexity.bootstrap_weighted_counting_worst_case_lower_bound` in [Results/All.lean](../../formalization/HeadComplexity/Results/All.lean).

A stronger logarithmic-denominator form holds for every $n\geq8$:

$$ B_1(n)=\frac{16e^2N^2(n+8)}{n(N-1)},\qquad W(n)\geq\frac{(N-1)\log2}{n\log B_1(n)}. $$

Its exact declaration is `HeadComplexity.BootstrapWeightedCounting.worstCase_real_log_lower`, publicly exported as `HeadComplexity.bootstrap_weighted_counting_worst_case_log_lower_bound`.

The corollary `HeadComplexity.BootstrapWeightedCounting.worstCase_real_one_sub_epsilon`, also publicly exported, proves $W(n)\geq(1-\epsilon)N/n^2$ whenever $\epsilon\gt0$, $n\geq256$, and $\epsilon n\geq8$. It makes the leading constant one explicit without changing the order of growth. The declaration `HeadComplexity.BootstrapWeightedCounting.worstCase_eventually_one_sub_epsilon` states the resulting eventual bound directly with `Filter.atTop`; its public alias is `HeadComplexity.bootstrap_weighted_counting_worst_case_eventually_one_sub_epsilon`.

The proof uses the new kernel-checked weighted Warren theorem and an origin-normalized original-model parameterization with $2nH$ parameters. Numerator parameters receive weight $H-1$ and denominator parameters weight one. The resulting unrestricted finite count, for $H\geq2$ and $2nH\leq N$, is

$$ |\mathcal F_{n,H}|\leq2\left(\frac{16e^2N^2(H-1)}{n^2H^2}\right)^{nH}. $$

This is `HeadComplexity.WeightedNormalizedCounting.card_le_optimal` in [WeightedNormalizedCounting.lean](../../formalization/HeadComplexity/Research/WeightedNormalizedCounting.lean). The lower-bound proof separately handles widths outside the displayed parameter range. It does not assume a margin, fixed denominator dictionary, bounded coefficients, restricted cancellation, or a target-independent denominator family.

The initial bootstrap is committed as `4b6181a5`; the later leading-constant corollaries and their public aliases are included in `d9234e8f`. See [bootstrap_weighted_lower_bound.md](bootstrap_weighted_lower_bound.md) for the finite arithmetic.

There is also an unconditional almost-all version at the same scale. `HeadComplexity.QuadraticScaleTypicalComplexity.card_le_exp_one_sub_epsilon` proves, for $n\geq8$, $H\gt0$, $\epsilon\gt0$, $\epsilon n\geq20$, and $n^2H\leq(1-\epsilon)N$,

$$ |\mathcal F_{n,H}|\leq\exp((1-\epsilon/2)N\log2). $$

This is kernel checked in [QuadraticScaleTypicalComplexity.lean](../../formalization/HeadComplexity/Research/QuadraticScaleTypicalComplexity.lean), commit `e5cf85fb`. It sharpens the leading constant in the distributional statement without crossing the quadratic scale.

## The requested finite margin audit

The original note [margin_sensitive_polynomial_capacity.md](../power-saving-20261124/margin_sensitive_polynomial_capacity.md) is audited and corrected. The complete original-model bridge is now kernel checked as `HeadComplexity.OriginalMarginCapacity.card_highMarginFunctions_le` in [OriginalMarginCapacity.lean](../../formalization/HeadComplexity/Research/OriginalMarginCapacity.lean).

For relative margin $0\lt\gamma\leq1$, set

$$ p=1+3(n+1)H,\qquad d=\left\lceil(n+1)\log(2/\gamma)\right\rceil,\qquad D=2d+2. $$

When $p\leq N$, the finite count is

$$ |\mathcal F_{n,H,\gamma}|\leq[2(n+1)!]^H\left(\frac{4eDN}{p}\right)^p. $$

The amplitude is exactly the requested $|b|+\sum_h\|\phi_h\|_\infty$, with every supremum over the complete Boolean cube. Every original head has one scalar $\alpha$ and coherent denominator slopes. The proof uses only coordinate permutation and simultaneous complementation of all bits inside a head. It does not silently allow independent bit flips or mixed-sign denominator slopes.

Both requested finite estimates are kernel checked in [MarginCapacityEstimates.lean](../../formalization/HeadComplexity/Research/MarginCapacityEstimates.lean):

- `HeadComplexity.MarginCapacityEstimates.card_highMargin_sqrt_scale`: for $n\geq32$ and $H\leq N/(100n\sqrt n)$, at most $2^{N/2}$ tables admit relative margin at least $\exp(-\exp(\sqrt n))$.

- `HeadComplexity.MarginCapacityEstimates.card_highMargin_logarithmic_scale`: for $n\geq32$ and $H\leq N\log n/(100n^2)$, at most $2^{N/2}$ tables admit relative margin at least $\exp(-\exp(n/\log n))$.

The logarithmic statement is derived directly from the finite formula. It does not substitute a dimension-dependent exponent into a fixed-exponent asymptotic claim. In each case, writing the test exponent as $t$ makes $H=cN/(nt)$, and the leading entropy contribution is $3cN$; coefficient-order charts and the remaining logarithms are lower-order terms. The Lean estimates supply explicit finite bounds rather than relying on this asymptotic explanation.

The declarations `card_highMargin_sqrt_overhead` and `card_highMargin_logarithmic_overhead` include comparison width $K=\lceil CH\rceil+B$, with $C\geq1$, source coefficient $c=1/(100C)$, and the sufficient additive-overhead condition

$$ 500(B+1)n^2\leq N. $$

The detailed hypothesis inventory is [finite_count_audit.md](finite_count_audit.md). These are margin-restricted capacity results, not unrestricted lower bounds.

## Exact missing quantifiers

Let $\mathcal F_{n,H}$ be the original truth tables of width $H$, and let $\mathcal G_{n,K,\gamma}$ be the tables with some original representation of width $K$ having relative margin at least $\gamma$. A valid unrestricted proof can establish either

$$ \mathcal F_{n,H}\subseteq\mathcal G_{n,K,\gamma}, $$

or a sufficiently small upper bound on

$$ \mathcal B_{n,H,K,\gamma}=\mathcal F_{n,H}\setminus\mathcal G_{n,K,\gamma}. $$

Membership in the latter set means that every original comparison representation at width $K$ has margin below $\gamma$. Padding by zero heads covers smaller comparison widths. One badly conditioned representation does not put a table in this set. The theorem `RelativeMarginQuantifiers.exists_same_score_small_margin` explicitly constructs arbitrarily bad-margin representations of the same score by adding a cancelled constant head.

The definitions and exact high-plus-low counting implication are checked in [RelativeMarginQuantifiers.lean](../../formalization/HeadComplexity/Research/RelativeMarginQuantifiers.lean). The target-specific implications `ConditionalMarginLowerBounds.worstCase_gt_sqrt_of_repair`, `worstCase_gt_logarithmic_of_repair`, and their low-count variants retain their missing premises explicitly. None is presented as an unconditional theorem.

One sufficient alternative is the feasible-chart estimate in [FeasibleChartEntropy.lean](../../formalization/HeadComplexity/Research/FeasibleChartEntropy.lean). With $L=nH+1$ active linear parameters, the needed continuation entropy is at most $L\sqrt n$ for the aimed bound, or $Ln/\log n$ for the fallback, after selecting an unordered globally feasible unit-contact certificate. The exact finite implication is kernel checked. The required bound on all feasible continuations of every certificate is still unproved.

A precise margin-free fallback lemma is available in the closer original orientation class. For $L=nH+1$, let $\mathcal C_c$ be `CoherentDenominatorCharts.coherentPatterns c`, the union over all $2^H$ coherent orientations of the globally feasible tables attached to one unordered active certificate. It retains the nonzero determinant, every full-cube unit-gap inequality, the coefficient box, and the existential box size without imposing a uniform coefficient bound. The missing statement is

$$ |\mathcal C_c|\leq\exp(Ln/\log n)\qquad\text{for every }c,\quad n\geq32,\quad L\leq N\log n/(25n). $$

The already kernel-checked `CoherentDenominatorCharts.worstCase_gt_of_logarithmic_chart_entropy` turns this lemma into $H\lt W(n)$. Taking $H=\lfloor N\log n/(50n^2)\rfloor$ would prove the fallback for all sufficiently large $n$. Only that chosen sequence of widths needs the new chart bound; uniformity over all smaller widths is unnecessary. This requires no margin repair or head overhead. The missing estimate must exploit the joint Boolean rows of the original sum of affine ratios; the generic positivity, parameter monotonicity, and block-convexity properties discussed below do not supply it.

## The decisive counting obstruction

The optimized weighted count cannot cross the current scale. The kernel-checked theorem `HeadComplexity.WeightedCountBarrier.optimal_certificate_exceeds_all_tables_at_quadratic_scale` proves

$$ 2^N\lt2\left(\frac{16e^2N^2(H-1)}{n^2H^2}\right)^{nH} $$

whenever $n\geq4$, $H\geq2$, $2nH\leq N$, and $n^2H\geq N$. At the aimed width the logarithm of this certificate divided by $N$ grows like $c\sqrt n\log2$; at the fallback width it grows like $c\log n\log2$.

`AnisotropicWeightBarrier.every_coordinate_certificate_exceeds_all_tables` extends the obstruction from uniform block weights to arbitrary positive coordinate weights. [NormalizedPolynomialSupport.lean](../../formalization/HeadComplexity/Research/NormalizedPolynomialSupport.lean) checks the actual all-one-row monomials forcing the degree constraints, so the obstruction is not based on an assumed support pattern. These statements rule out further parameter-weight optimization within this particular cleared-polynomial count. They do not assert that the represented class itself has at least $2^N$ elements.

## Repair and structural results, with their limits

The following are kernel-checked auxiliary results. Each limitation is part of the handoff.

- One-head truth tables and products of two threshold functions have quantitative admissible repairs in `IntegerSeparatorMarginRepair` and `TwoFactorMarginRepair`. No general constant-overhead extension is proved.

- `MidrangeMarginCentering` removes constant offsets at unchanged width without worsening relative margin. `ActiveMarginImprovement.exists_strict_margin_improvement` proves a local improvement from a correction strictly improving every active vertex. Neither supplies a quantitative endpoint with controlled total width.

- `ExceptionalMarginRepair.relativeMargin_ge_of_exceptional_patch` makes a bounded-amplitude partial-label correction preserve the whole table when the source has a quantitative gap outside the prescribed exceptional set. The missing premise is the existence of such a source representation with a sufficiently small exceptional set.

- `LowParameterDenominatorCapacity`, `GroupedDenominatorCapacity`, `SharedStatisticsCapacity`, `AffineFiberCapacity`, and `ProjectiveFiberCapacity` give finite capacity bounds for explicit structured denominator classes, retaining arbitrary real numerators and signed cancellation. No universal access or high-margin-or-structured dichotomy is proved.

- `SplitSmoothableCapacity` and `SplitSmoothableEstimates` count explicit algebraic cluster classes. Ordinary moment and Cayley-Bacharach access does not follow from Boolean projection moments: exact ghosts, spliced circuits, and rank-growth examples obstruct the naive transfers.

- `MinorityContactCapacity.one_minority_unique` forces the full table in a one-minority unit-basis branch; its fixed-dimensional continuation counts handle small minority spaces. Balanced contact patterns still leave quadratic entropy. Exact same-basis counterexamples in `UnimodularFeasibleBasisObstruction` refute general branch uniqueness, even with an integer inverse basis.

- `TwoMinorityBasisBranches.two_open_feasible_branches` gives two genuine open full-cube unit-gap branches with the same unimodular basis and the same two minority contact positions. Their explicit witnesses have the same signs of all numerator-difference coefficients. It refutes two-minority uniqueness and one branch per coefficient-sign orthant. It does not refute a polynomial bound on branches.

- `TwoMinorityNeighborObstruction` strengthens this failure to every affine coefficient comparison against $0,\pm r,\pm1$. The same eight-bit contact basis has exact admissible witnesses at $r=17/9$ and $r=3$, with identical comparison signs but different labels at vertex 15. The missing subset sum is $r-2$. `same_all_coefficient_comparisons`, `same_positive_level_comparisons`, and `different_labels` are kernel checked, together with full-cube gaps and basis injectivity. See [two_minority_neighbor_obstruction.md](two_minority_neighbor_obstruction.md). This refutes the proposed coefficient-comparison determination lemma, not a general continuation-count bound.

- `OneMinorityBalanceObstruction` proves that every denominator in one specified actual branch satisfies $22b_0\leq\sum_i b_i$, while an admissible full-cube witness exists. This refutes constant-denominator deformation of that branch, not inverse-polynomial balancing or a representation-changing repair.

- `ExactLayerGateLowerBound.original_nonnegative_layer_gate_heads_ge` proves that an exact nonzero nonnegative score supported on one Hamming layer needs at least $n$ heads. It blocks a proposed exact value gate, not a sign repair.

- `FullCubeNormOptimization`, `FullCubeNormCrossMoments`, and `TwoExtremumDuplication` check algebraic consequences of actual supremum-norm stationarity. A norm-controlled joint replacement and a bounded-width iteration theorem are still missing. Analytic existence, constraint qualification, and access to the required stable optimum are not hidden inside those algebraic declarations.

- `PositiveReciprocalExpansion.reciprocal_with_endpoint_identities` and `ratio_with_full_cube_mass` give an exact finite positive reciprocal expansion. `OriginalAnchoredExpansion.original_head_expansion` connects it to every genuine original head, in either coherent orientation, with total affine-block norm at most $(n+1)\|\phi\|_\infty$. Every block is uniformly approximable by one admissible head. There are up to $2^n$ blocks, so this is not a narrow repair. `norm_eval_eq_atomSup` checks equality with the requested whole-cube norm.

- `ProbabilityMixtureApproximation.normalized_product_approximation_of_width` gives a genuine-head uniform approximation to an arbitrarily long product of normalized constant-numerator reciprocal factors with common positive orientation. Error below $\epsilon$ requires only $m\gt2\log(2N)/\epsilon^2$ heads, zero bias, and total amplitude at most one. The common negative-orientation version is also kernel checked. Product length is absent, but affine numerators and mixed orientations are outside the theorem.

- `CoherentEdgeVariation` checks the monotone edge-variation inequality. `NonnegativePointApproximation.point_error_ge_one_fifth` now proves directly for original heads that a nonnegative-head sum with nonnegative bias cannot approximate a mixed point uniformly to error below $1/5$, at any width. `mixedProduct_nonnegative_compiler_error` gives two explicit genuine reciprocal factors of opposite orientations whose product requires error at least $4/25$ for every such nonnegative compiler. All sixteen witness evaluations are kernel checked. These statements do not exclude signed output heads or truth-table repairs. See [nonnegative_mixed_product_obstruction.md](nonnegative_mixed_product_obstruction.md).

- `SharedDenominatorGapPath.eventually_admissible_path` and `transport_norm_le` verify a genuine norm-contracting replacement when two heads share a strictly positive affine denominator. The analogous construction for different denominators leaves the affine numerator class; the actual tangent counterexample in `PencilMoebiusTangentObstruction` rules out that direct extension.

The fully kernel-checked sharp one-head optimum is `HeadComplexity.OneHeadOriginalMarginOptimum.hasRelativeMargin_iff` in [OneHeadOriginalMarginOptimum.lean](../../formalization/HeadComplexity/Research/OneHeadOriginalMarginOptimum.lean). For the five-bit threshold which is true at Hamming weight at least two, a width-one representation of relative margin at least $\gamma$ exists exactly when

$$ \gamma\leq\frac5{11+4\sqrt6}. $$

The proof covers every original representation, including arbitrary bias and both orientations. `exists_attaining` constructs a genuine head with strictly positive denominator slopes achieving equality, and `exists_no_same_width_improvement` makes the global replacement quantifier explicit. This refutes the blanket claim that every margin below one admits a same-width improvement. The optimum is a healthy constant, so it does not obstruct the requested tiny-margin repair with comparison overhead.

Two endpoint statements make the optimization gap precise. `MarginOneCollapse.hasRelativeMargin_one_head` proves that an attained relative margin of one for a nonconstant table forces a one-head margin-one representation. `NearUnitMarginCollapse.computable_one_head_of_near_unit_margin` proves that $2^n(1-\gamma)\lt1$ already forces unrestricted one-head computability, although the selected head need not preserve the margin. Both are kernel checked; see [margin_one_collapse.md](margin_one_collapse.md) and [near_unit_margin_collapse.md](near_unit_margin_collapse.md).

A fixed-width maximum need not exist. `LiteralMarginNonattainmentWitness.hasRelativeMargin_below_one` is a kernel-checked genuine one-head literal construction for every $\gamma\lt1$. Its exact margin on $n$ bits is $1/(1+n\epsilon)$, with $\epsilon\gt0$, and its full-cube norm is one. The independently audited written classification in [margin_one_nonattainment.md](margin_one_nonattainment.md), combined with the kernel-checked collapse theorem, proves that no nonconstant table on $n\geq2$ attains margin one at any finite width. The original constant-denominator numerator restriction is essential to this classification. The literal counterexample is now fully kernel checked: `LiteralMarginNonattainment.hasRelativeMargin_iff_lt_one` proves, in every dimension `n+2` and at every fixed width at least one, that a literal admits margin at least $\gamma$ exactly when $\gamma\lt1$. Thus its supremal margin is one and is not attained. The stronger classification covering every nonconstant table remains written mathematics, not a Lean theorem. This rules out assuming an attained best-margin representation in the open admissible domain; it does not rule out repair at either requested tiny margin. A new written compactness argument in [normalized_head_boundary_faces.md](normalized_head_boundary_faces.md) proves that the best margin is attained in the full-cube value closure, and every strictly smaller margin is achievable by genuine heads at the same width. It gives no quantitative lower bound on that optimum. Boundary-stratum variations, rather than compactified attainment alone, remain an additional requirement for the optimization route.

The finite coefficient-box counterexample in `ScaledBoxPackingObstruction` refutes a proposed determinant-only packing lemma. A fixed involution already admits infinitely many disjoint positive-radius boxes near a boundary face. It does not refute a Boolean-specific chamber bound.

## Two late routes and their exact remaining gaps

The address-face route distinguishes individual head data from total score data. If the individual numerator and denominator restrictions are fixed, continuation to $k$ more coordinates has only $1+2kH$ parameters. Fixing the total score on the face does not fix those head data. The written theorem in [exact_address_fiber_capacity_gap.md](exact_address_fiber_capacity_gap.md) embeds every original width $H$ table into one opposite-face fiber with exactly $2H+1$ admissible heads, while the score on the selected face is identically one. Both coherent orientations, the constant-denominator case, and finite strict slack are handled. `SameFaceScoreFiber` checks a smaller explicit same-score-fiber example. The full embedding is written mathematics. `RelativeMarginRestriction.relativeMargin_restrict_ge` and `hasRelativeMargin_restrict` are kernel checked and show that restricting any original comparison representation to a coordinate face cannot decrease its relative margin. Thus a healthy comparison repair for the embedded fiber restricts to a healthy repair for the original table. A sharp reconstruction bound on such singular fibers must still address original-model capacity; generic decomposition identifiability cannot discard them. Since the labels on one half-cube are fixed, the entire enlarged fiber also has the trivial count at most $2^{N/2}$ in its enlarged cube size. The example does not refute a half-table global budget.

The norm-stationarity route has a written generic rank theorem in [unrestricted_capacity_quadratic_feature_rank.md](unrestricted_capacity_quadratic_feature_rank.md). With $d=\binom n2$ and $H\geq\lceil(N/d)\log d\rceil+\lceil N/d\rceil+3$, quadratic reciprocal features vanishing at each head's prescribed two endpoints generically span every row outside the common endpoint intersection. A Boolean sphere-cover interpolation proves the rank by a nonzero polynomial minor, then transfers it to strictly positive affine denominators. Under additional regular KKT, unique-extremum, and duplication-stability hypotheses, the dual is supported on the common endpoints and the centered amplitude must be one. This is a written conditional consequence, not an unrestricted repair theorem. A width-constrained optimum may have no spare heads, and exceptional denominator configurations may be essential. The needed lemma is a quantitative bound on their truth-table entropy or a bounded-width escape theorem. Generic rank alone supplies neither.

The final observation route gives a uniform bound independent of head parameters. `SelectedNegativeControl.original_four_neighbors_le` proves that two downward and two upward negative observations control every nonnegative original head at a vertex. If their total values are at most one, `total_le_four_of_observations` bounds the positive total at the vertex by four. For a uniformly random independent half of the cube, the expected number of uncontrolled vertices is at most $2(1+n/3)(3/2)^n$. The deterministic original-model inequalities and the exact binomial sums in `NegativeObservationBinomial` are kernel checked; the probability and Markov arguments are written proofs in [random_negative_observation_control.md](random_negative_observation_control.md). The exceptional set is small enough for the existing patch construction, but the required signed gap on its complement is still missing.

There is an exact obstruction to inferring that gap from bounded positive mass. `NonnegativePartitionEmbedding.exists_bounded_near_partition_of_computable` starts from every original width $H$ table and constructs $H+2$ genuine nonnegative heads, each with minimum zero, bias $-1$, and full-cube amplitude at most four. The score is arbitrarily close to zero while retaining the complete strict truth table; the more explicit theorem gives exactly a positive scalar multiple of the source score. Thus this access condition excludes no source truth tables. A sharp upper count of that normalized class could still prove a new unrestricted capacity bound. The construction does not prove that any table lacks a healthier comparison representation. A written consequence of its exact formula puts every original source table in every neighborhood of one fixed limiting tuple of head values at width $H+2$. The target-dependent denominator parameters need not converge to one fixed parameter tuple, so merely counting the boundary value strata loses essential information. See [unrestricted_capacity_positive_partition_gap.md](unrestricted_capacity_positive_partition_gap.md).

A stronger canonical reduction is now fully kernel checked. `SameWidthPositiveNormalization.hasNormalizedMargin_or_complement` puts every original margin certificate, or its global output complement, into nonnegative minimum-zero heads with bias $-1$ and amplitude at most three at exactly the same width, retaining at least one third of its margin. The computability version has no quantitative margin premise. `ComplementCapacityReduction.original_card_le_twice_normalized` proves the precise factor-two upper count; `normalized_card_le_original` proves the reverse inclusion bound. These count truth tables, not parameter witnesses. Consequently the positive normal form retains the unrestricted capacity problem, including the original arbitrary signed cancellation. It supplies no new positive margin lower bound. See [same_width_positive_normalization.md](same_width_positive_normalization.md).

The loss of three is sharp. `PositiveNormalizationSharpness.relativeMargin_le_third` proves that every nonconstant table represented by nonnegative heads with bias $-1$ has relative margin at most $1/3$, at any width or amplitude. `literal_source_margin`, `literal_normalized_margin`, and `hasNormalizedMargin_literal_iff` give a genuine one-bit source of margin one and its exact normalized optimum of one third. For literals in dimensions at least two, `PositiveLiteralNonattainment.relativeMargin_lt_third` now proves the strict bound below one third at every finite width, even without a minimum-zero or amplitude-cap assumption. Equality would center the same genuine heads into a forbidden original margin-one representation. Also, the canonical amplitude bound already implies that the positive total is at most two everywhere, so the observation bound of four adds no stronger value control in that form.

The final abstract counting attempt adds parameter monotonicity to this positive viewpoint. The written construction in [coordinate_monotone_permutation_entropy.md](coordinate_monotone_permutation_entropy.md) has positive rational scores between $1/2$ and $3/2$, monotone dependence on every positive parameter, and convex feasible fibers in every complete head block, but retains $(H!)^n$ tables and near-full entropy at both critical widths. The first failed implication is that these properties alone force entropy $O(nH\log(N/(nH)))$. The construction is not an original xorformer family: the shared Boolean rows and the specific sum of affine ratios must provide any missing improvement.

## Written proofs and finite computations

The following remain written mathematics rather than complete Lean declarations: the quantitative universal construction of width $2323202N/(n\log n)$ and margin $\exp(-100n^2\log(n+1))$; the partial-label grid compiler with controlled full-cube amplitude; the constant-error central-layer value-approximation lower bound of order $\sqrt n$; and the ordinary Cayley-Bacharach incidence-capacity argument. Their local algebraic ingredients and stated finite inequalities are separately formalized where indicated in their notes. None supplies the missing unrestricted access lemma.

Additional independently audited written obstructions concern value compilation. The high-order mixed-difference theorem in [mixed_point_high_order_amplitude.md](mixed_point_high_order_amplitude.md) forces exponential amplitude for sufficiently accurate approximation of a balanced point gate, even at unlimited width. The opposite-orientation two-head closure theorem in [opposite_two_head_bounded_closure.md](opposite_two_head_bounded_closure.md) excludes a bounded-amplitude approximation by one head of each orientation to mixed point gates with at least two coordinates of each type. The scalar-cylinder construction in [scalar_cylinder_exponential_mass.md](scalar_cylinder_exponential_mass.md) achieves width equal to the maximum of one and the smaller literal count, with exponential amplitude independent of the requested tolerance. These are value-approximation statements, not hard truth tables for the task's tiny margins. In particular, a point-indicator truth table itself has a healthy narrow representation.

Floating optimization and root searches are exploratory evidence only. In particular, a purported boundary branch with maximum normalized constant coefficient zero was rejected by exact reconstruction: it implied $-2b_0-2b_4\geq0$, contradicting strict positivity. The exact $1/22$ example has independent rational checking and Lean proofs. Search failures are not nonexistence theorems, and multiple parameter roots with the same truth table do not count as additional tables.

The detailed two-hour checkpoints are in [RESEARCH_LOG.md](RESEARCH_LOG.md). The full hypothesis audit and the individual notes identify the first failed lemma of each route rather than treating an ill-conditioned witness as an unrestricted obstruction.

## Verification status

The public theorem build and its transitive `#print axioms` output are recorded in `bootstrap-weighted-build.txt`, `bootstrap-weighted-axioms.txt`, `bootstrap-leading-constant-build.txt`, and `bootstrap-leading-constant-axioms.txt`. The only transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`.

A preflight built 114 changed theorem modules and audited 2,563 declarations without project axioms. The first final-hour check, against source `1fa75211`, rebuilt the default target with 4,145 jobs and all 140 then-committed changed modules with 9,317 jobs, then audited 2,981 theorem declarations and fourteen explicit main-theorem axiom prints. Every check passed; its logs have prefix `final-hour-start`.

The final source audit at 03:19 UTC, against `44da9da5dc67ada89b846b116f83de5f9d454768`, passed the default build with 4,145 jobs and all 158 committed changed modules with 9,335 jobs. All 3,170 theorem declarations passed the transitive axiom audit, and all fourteen exact main-theorem prints used only `propext`, `Classical.choice`, and `Quot.sound`. [verify_run.py](verify_run.py) records the source revision, exit codes, elapsed times, module manifest, and logs in `final-verification.json` and the companion `final-*.txt` files. All theorem sources were then frozen; subsequent changes are documentation and verification artifacts.

Final source verification has passed. The original definitions and the audited Lean tree remain unchanged, as recorded in `final-integrity.json`. The requested unrestricted power saving and logarithmic fallback remain open. The closing checkpoint in `RESEARCH_LOG.md` records the final attempts and their precise remaining gaps.
