# Beyond the Xorformer Counting Barrier

## Current outcome

This run starts from `aa0cceb140ba75149353f92943b1fba78e7e0ec5`, the required `origin/ar/47c1ff45613b`, and works on `ar/4e24baaa5491`. The original unrestricted definition of `HeadComplexity.worstCaseHeadComplexity`, the head-admissibility structure, and the computability predicates are unchanged.

The requested bound of order $N/n^{3/2}$, every smaller fixed positive power saving, and the explicit $N\log n/n^2$ fallback remain open at this checkpoint. The strongest unconditional theorem proved in this run is a finite-constant improvement of the quadratic-denominator bound. No refutation of the original $O(N/n^2)$ conjecture is claimed.

The active research period runs from 2026-11-24 15:27:59 UTC until 2026-11-25 03:27:59 UTC. This handoff is being assembled during ongoing work; final verification details will be filled in during the last hour.

## Strongest unconditional original-model theorem

Write $N=2^n$. For every integer $n\geq256$,

$$ W(n)\geq\frac{N-1}{n(n+7)}. $$

The exact Lean declaration is `HeadComplexity.BootstrapWeightedCounting.worstCase_real_lower` in [BootstrapWeightedCounting.lean](../../formalization/HeadComplexity/Research/BootstrapWeightedCounting.lean). The public alias is `HeadComplexity.bootstrap_weighted_counting_worst_case_lower_bound` in [Results/All.lean](../../formalization/HeadComplexity/Results/All.lean).

A stronger logarithmic-denominator form holds for every $n\geq8$:

$$ B_1(n)=\frac{16e^2N^2(n+8)}{n(N-1)},\qquad W(n)\geq\frac{(N-1)\log2}{n\log B_1(n)}. $$

Its exact declaration is `HeadComplexity.BootstrapWeightedCounting.worstCase_real_log_lower`, publicly exported as `HeadComplexity.bootstrap_weighted_counting_worst_case_log_lower_bound`.

The corollary `HeadComplexity.BootstrapWeightedCounting.worstCase_real_one_sub_epsilon`, also publicly exported, proves $W(n)\geq(1-\epsilon)N/n^2$ whenever $\epsilon\gt0$, $n\geq256$, and $\epsilon n\geq8$. It makes the leading constant one explicit without changing the order of growth.

The proof uses the new kernel-checked weighted Warren theorem and an origin-normalized original-model parameterization with $2nH$ parameters. Numerator parameters receive weight $H-1$ and denominator parameters weight one. The resulting unrestricted finite count, for $H\geq2$ and $2nH\leq N$, is

$$ |\mathcal F_{n,H}|\leq2\left(\frac{16e^2N^2(H-1)}{n^2H^2}\right)^{nH}. $$

This is `HeadComplexity.WeightedNormalizedCounting.card_le_optimal` in [WeightedNormalizedCounting.lean](../../formalization/HeadComplexity/Research/WeightedNormalizedCounting.lean). The lower-bound proof separately handles widths outside the displayed parameter range. It does not assume a margin, fixed denominator dictionary, bounded coefficients, restricted cancellation, or a target-independent denominator family.

The initial bootstrap is committed as `4b6181a5`; the later leading-constant corollaries and their public aliases are included in `d9234e8f`. See [bootstrap_weighted_lower_bound.md](bootstrap_weighted_lower_bound.md) for the finite arithmetic.

## The requested finite margin audit

The original note [margin_sensitive_polynomial_capacity.md](../power-saving-20261124/margin_sensitive_polynomial_capacity.md) is audited and corrected. The complete original-model bridge is now kernel checked as `HeadComplexity.OriginalMarginCapacity.card_highMarginFunctions_le` in [OriginalMarginCapacity.lean](../../formalization/HeadComplexity/Research/OriginalMarginCapacity.lean).

For relative margin $\gamma\gt0$, set

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

- `OneMinorityBalanceObstruction` proves that every denominator in one specified actual branch satisfies $22b_0\leq\sum_i b_i$, while an admissible full-cube witness exists. This refutes constant-denominator deformation of that branch, not inverse-polynomial balancing or a representation-changing repair.

- `ExactLayerGateLowerBound.original_nonnegative_layer_gate_heads_ge` proves that an exact nonzero nonnegative score supported on one Hamming layer needs at least $n$ heads. It blocks a proposed exact value gate, not a sign repair.

- `FullCubeNormOptimization`, `FullCubeNormCrossMoments`, and `TwoExtremumDuplication` check algebraic consequences of actual supremum-norm stationarity. A norm-controlled joint replacement and a bounded-width iteration theorem are still missing. Analytic existence, constraint qualification, and access to the required stable optimum are not hidden inside those algebraic declarations.

The finite coefficient-box counterexample in `ScaledBoxPackingObstruction` refutes a proposed determinant-only packing lemma. A fixed involution already admits infinitely many disjoint positive-radius boxes near a boundary face. It does not refute a Boolean-specific chamber bound.

## Written proofs and finite computations

The following remain written mathematics rather than complete Lean declarations: the quantitative universal construction of width $2323202N/(n\log n)$ and margin $\exp(-100n^2\log(n+1))$; the partial-label grid compiler with controlled full-cube amplitude; the constant-error central-layer value-approximation lower bound of order $\sqrt n$; and the ordinary Cayley-Bacharach incidence-capacity argument. Their local algebraic ingredients and stated finite inequalities are separately formalized where indicated in their notes. None supplies the missing unrestricted access lemma.

Floating optimization and root searches are exploratory evidence only. In particular, a purported boundary branch with maximum normalized constant coefficient zero was rejected by exact reconstruction: it implied $-2b_0-2b_4\geq0$, contradicting strict positivity. The exact $1/22$ example has independent rational checking and Lean proofs. Search failures are not nonexistence theorems, and multiple parameter roots with the same truth table do not count as additional tables.

The detailed two-hour checkpoints are in [RESEARCH_LOG.md](RESEARCH_LOG.md). The full hypothesis audit and the individual notes identify the first failed lemma of each route rather than treating an ill-conditioned witness as an unrestricted obstruction.

## Verification status

The public theorem build and its transitive `#print axioms` output are recorded in `bootstrap-weighted-build.txt`, `bootstrap-weighted-axioms.txt`, `bootstrap-leading-constant-build.txt`, and `bootstrap-leading-constant-axioms.txt`. The only transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`.

A preflight built 114 changed theorem modules and audited 2,563 declarations without project axioms. The final run of [verify_run.py](verify_run.py) will additionally rebuild the default target, all subsequently added modules, every changed module's transitive theorem axioms, and the exact public lower-bound declarations. Its source revision, exit codes, elapsed times, module manifest, and logs will be recorded in `final-verification.json` and the companion `final-*.txt` files.

Final verification and the concluding research status are pending while the run remains active.
