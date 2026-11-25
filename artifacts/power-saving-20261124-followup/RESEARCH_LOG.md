# Beyond the Xorformer Counting Barrier

## Clock and starting state

The active research period began on 2026-11-24 at 15:27:59 UTC. The twelve-hour deadline is 2026-11-25 at 03:27:59 UTC. The final verification hour starts at 02:27:59 UTC.

The starting revision is `aa0cceb140ba75149353f92943b1fba78e7e0ec5`, equal to `origin/ar/47c1ff45613b`. Work is on `ar/4e24baaa5491`. The initial working tree was clean. The original definitions will remain unchanged.

## Initial audit

The inherited `lake build` passed, reporting 3419 jobs. Its transcript is saved in `baseline-build.txt`. This is a baseline check, not verification of a new lower bound.

The existing finite margin-sensitive count is a written theorem. Its reciprocal approximation and conditional sign-preservation step are Lean-checked in `HeadComplexity.Research.ConditionedReciprocalApproximation`. The full polynomial parameter construction, finite union count, and Warren theorem are not supplied there.

The existing declaration `HeadComplexity.worstCaseHeadComplexity_gt_div_of_warren` takes `WarrenStrictSignPatternBound` as an explicit premise. Its standard-axiom audit does not eliminate that premise. It must not be described as an unconditional kernel proof of the analytic counting theorem.

## Parallel investigations

- Audit the finite count and derive the two requested margin regimes with explicit constants and head overhead.
- Seek a truth-table-preserving admissible margin repair; test the first failed structural lemma.
- Seek a different unrestricted capacity bound that uses positivity or the Boolean input structure.
- Formalize the precise original-model relative margin and truth-table quantifiers, while investigating whether singular low-margin strata can be counted separately.

The first substantive checkpoint will record elapsed time, the strongest proved statement, the decisive inequality or obstruction, and the next different attempt. A conditional theorem, an auxiliary margin count, and an inherited green build are checkpoints only.

## Early verified checkpoint, approximately 17 minutes

The finite high-margin audit is committed as `5576475`. Both requested scales have the explicit sufficient threshold and overhead constants recorded in `finite_count_audit.md`.

A complete Warren proof was found in the permitted prior-run repository and imported without changing existing definitions. Its 13-module build and transitive audit of 101 declarations passed. The provenance, exact theorem interface, and evidence are recorded in `warren-provenance.md`. This makes the existing quadratic-denominator lower bound unconditional in this checkout; it is inherited mathematics, not a new exponent gain.

The new module `Research.RelativeMarginQuantifiers` checks the exact full-cube amplitude definition, the existence of a nonquantitative common positive margin at fixed dimension and width, and the precise high-margin plus universally-low-margin counting implication for the original worst-case complexity. It also proves that adding one cancelled constant head makes the relative margin arbitrarily small while preserving the entire score table. Thus an existentially bad representation cannot identify a bad truth table.

The repair route has a stronger written obstruction with a checked approximation lemma: a fixed pencil can force every numerator refit, including arbitrary repeated denominators, to have a margin exponentially small in width divided by dimension. Changing the denominator dictionary is not excluded. The next attempt permits all new poles along a fixed direction, then examines genuinely changing directions. The independent capacity route is examining the Boolean address cost in factorial interpolation examples and a normalized finite count with better constants.

## Two-hour checkpoint, 17:25 UTC

Elapsed active time is approximately one hour and fifty-seven minutes. The aimed unrestricted power saving and the logarithmic fallback remain open. Work continues for the full allocation.

The strongest unconditional lower bound now checked against the unchanged original definition is `HeadComplexity.NormalizedLogCounting.worstCase_real_log_lower` in `Research/NormalizedLogCounting.lean`, also exported as `HeadComplexity.normalized_counting_worst_case_log_lower_bound`. For every integer $n\geq8$ it proves

$$ W(n)\geq\frac{(2^n-1)\log 2}{2n\log(2e\cdot2^n/n)}. $$

This is an improved finite denominator, still of order $2^n/n^2$. The module and public aggregate build passed; transitive axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. The decisive unrestricted estimate remains the normalized Warren bound with $2nH$ parameters and degree $H$. At the aimed width its logarithmic entropy divided by $N$ grows like $2c\sqrt n$, and at the fallback width like $2c\log n$. Thus it cannot establish either target for fixed positive $c$.

The complete original-model finite margin count, including the coefficient-order charts, has now been formalized. `MarginCapacityEstimates` proves both requested scales and the constant-factor plus additive head-overhead versions, with explicit constants. `ConditionalMarginLowerBounds` checks the exact implication from either a whole-table margin repair or a bound on tables for which every comparable-width representation has insufficient margin. These declarations retain the missing hypothesis and are not unconditional lower bounds.

There is positive repair progress: one-head tables have a uniform factorial-scale margin repair, and a general low-threshold-degree table compiles into admissible heads with an explicit factorial margin. There is also an unrestricted capacity theorem for low-dimensional affine, polynomial-curve, and clustered denominator families. None of these structural classes has been proved to cover every narrow representation.

The principal failed lemmas are now isolated. Fixed denominator pencils and even fixed directions can force very small margins. Sign-only repairs of individual clusters fail to preserve comparisons with the rest of a signed sum. A genuine two-head affine-product construction rules out constant-overhead compilation into deterministic priority pieces, despite already having polynomial margin. Three genuine heads can cancel collectively although every pair of normalized feature families is independent. Finally, an abstract positive multiaffine family with convex fibers in every full parameter block retains the full permutation entropy; block convexity alone cannot remove the counting loss. The last construction is not an original-model counterexample.

The next distinct attempts use the exact unit-level interpolation constraints of a rational active basis, pursue a sign-preserving positive integral construction that permits changing denominator directions, and test whether dense-width affine-product compilation can avoid the known small-width obstruction. A fixed one-head interpolation system with arbitrary prescribed positive linear observations can itself support exponentially many tables. Those observations are not actual Boolean unit-level evaluations with full-cube unit gaps; that construction does not settle the feasible actual-basis branch count.

## Four-hour checkpoint, 19:28 UTC

Elapsed active time is four hours. The strongest unconditional lower bound remains the normalized logarithmic-denominator theorem recorded above. Neither a positive power saving nor the logarithmic fallback has been proved. The original definitions are unchanged, and the run continues.

The new finite comparison classes now have kernel-checked capacity bounds at the desired scales. `AffineProductCapacity.card_represented_le_half_tables` counts arbitrary real affine-product sums of width at most $N/(100n\log(n+1))$. `DenominatorCodebookCapacity.card_represented_with_overhead` counts arbitrary real numerators over a target-independent codebook with $\log M\leq nt$, at width $N/(100Cnt)$ with explicit constant and additive overhead. The respective missing lemmas are a sufficiently narrow sign-preserving compiler and a uniform codebook repair. The exact original-to-affine-product compiler `FiniteDifferenceProductCompiler.original_compiler` is now checked, but its width $2^H-1$ is far too large. The old exact-cleared-table rank obstruction explains why merely approximating the cleared numerator cannot uniformly reduce that width.

The repair requirement has also been weakened without hiding its quantifiers: `ApproximateMarginCounting` proves that comparison representations agreeing on all but $N/16$ inputs suffice when the high-margin class contains at most $2^{N/2}$ tables. The resulting lower bounds still have an explicit, unproved approximate-repair premise. Genuine two-head products of two threshold functions do have a uniform factorial-scale margin repair. A deterministic priority compiler, even allowing approximation, requires growing overhead on examples that already have good margin. A dense-width anchored-cylinder compiler also fails, despite good original margins, so these compiler obstructions do not identify universally low-margin truth tables.

The active-basis route now has exact feasible counterexamples, including one-head examples: the same selected cube basis, unit values, full-cube unit slack, coefficient bounds, and numerator slope signs can admit different whole truth tables. These examples rule out uniqueness of continuation from such data. They do not disprove a quantitative count of all feasible branches. A special one-head extension operation does preserve the entire table when new denominator coefficients decrease, but this monotonicity currently depends on keeping the old numerator and denominator fixed.

Boolean projection moments have additional exact dependencies absent from ordinary Veronese moments. A checked six-point ghost annihilates every Boolean projection moment. A checked seven-point example has a moment-rank plateau followed by renewed growth, contradicting a naive dimension-times-order circuit bound. Therefore ordinary Cayley-Bacharach or inverse-system results cannot be applied directly to the projected moment spaces. A finite-order ghost lift and a local smoothable-scheme formulation are the next attempts to recover a valid ordinary algebraic structure. Straight common-base radial transfer was already formalized in the starting material; new work must address genuinely curved paths, moving numerators, or multiple base denominators.

The decisive unrestricted obstruction is still the degree factor in the normalized count. At $H=cN/n^{3/2}$ its entropy bound exceeds $N\log2$ by a factor growing like $\sqrt n$; at $H=cN\log n/n^2$ the factor grows like $\log n$. Every proposed replacement now states the exact structural or counting lemma needed to remove that loss. The next distinct investigations concern local inverse systems of bounded length, quantitative access to degenerate parameter strata, and positive-multiplier or fixed-codebook representations that may change every original denominator jointly.


## Six-hour checkpoint, 21:28 UTC

Elapsed time is six hours from the recorded start. The strongest unconditional original-model lower bound remains `NormalizedLogCounting.worstCase_real_log_lower`, with the exact formula recorded at the two-hour checkpoint. The requested power saving and logarithmic fallback remain open. The run continues, and the original definitions are unchanged.

A new complete weighted Warren theorem is kernel checked as `HeadComplexity.weightedStrictPolynomialSignPatterns_card_le`. With positive integer parameter weights at most the weighted degree, its finite count has numerator $(4eDN/p)^p$ divided by the product of parameter weights. The proof includes a weighted diagonal root bound, analytic perturbation wrappers, and strict sign counting. This improves and formalizes the previously written weighted-count ingredient rather than assuming it.

The new cluster counts handle curvilinear clusters, arbitrary finite monomial downsets, filtered local algebras, and real split smoothable local algebras. `SplitSmoothableCapacity.card_smoothableFunctions_le` is kernel checked, including adjugate matrix coordinates, an even positive determinant multiplier for the entire score, and preservation of all strict signs under real-topological approximation. Its module built with 3,746 jobs, and all 76 theorem declarations have only the three standard axioms. The simplified nonuniform formula and its eventual half-table estimate at the aimed width remain independently audited written proofs. Root is formalizing those finite entropy simplifications separately.

The decisive restricted estimate for total length $K$, maximum cluster length $Q$, number of clusters $G$, and $t=\sum_gq_g^2$ is

$$ \log T\leq p\log\left(\frac{4e(3+2Q)N}{p}\right)+2(n+1)K\log Q+((n+1)G+t)\log K,\qquad p=1+2(n+1)K+t. $$

For cluster lengths comparable to $\sqrt n$ and $K\leq N/(1000n^{3/2})$, this is below $N\log2/2$ eventually, including composition and filtration-order choices. The two large contributions are only constant multiples of $K n^{3/2}$. This is a capacity theorem for the stated cluster class, not an unrestricted access theorem.

The full-cube feasible-chart route now has a kernel-checked coherent-orientation reduction and exact finite entropy budgets in `CoherentDenominatorCharts` and `FeasibleChartEntropy`. It still needs a bound on the number of feasible branches within each chart. The new genuine one-head example `FixedBasisBalanceObstruction.constant_mass_le_eighth` proves that every denominator in its specified actual-basis branch has constant mass at most one eighth. Exact rational computations also found a twelve-variable branch with maximum one ninth. These rule out stronger constant-balancing guesses, but do not refute inverse-polynomial balancing or a change of representation. A five-million-trial exploratory search over a special triangular basis family found no nonconstant branch; this is numerical evidence only.

`MidrangeMarginCentering.exists_centered_certificate` now removes all constant head offsets at unchanged width, preserves the entire score, and cannot decrease relative margin. This removes a trivial fake collision mechanism. The remaining access obstruction is collective: an entire strict label region can be thin near a rank-drop locus without compactness forcing it to reach that locus. Neither one ill-conditioned representation nor a local stationary-point calculation identifies a universally low-margin truth table.

A further exact Boolean projection circuit has arbitrarily large affine span and a unique universal constant-residue relation. Its score is zero and removable, so it is not a hard-table counterexample. It blocks an overly strong low-dimensional-circuit lemma while remaining compatible with a sparse quotient construction. Ordinary border-rank to smoothable-scheme transfer also needs care after Boolean projection, because projective spans can jump.

The next distinct attempts are a quantitative whole-label-cell escape argument after centering, a joint original-model margin optimization experiment, and an audit of factorial homogenization as a possible score-transfer construction. A new general Hankel-matrix calculation suggests that the canonical homogeneous polynomial can require quadratic, rather than constant, border-Waring overhead; its scope is being independently checked before use. This would block one specific algebraic compiler, not a truth-table repair.

The earlier two-hour log sentence about exponentially many unit-basis branches has been corrected: the underlying construction used arbitrary positive linear observations. Actual full-cube unit-basis branch entropy remains open. This correction does not affect any Lean declaration or any proved lower bound.

## Eight-hour checkpoint, 23:28 UTC

Elapsed active time is eight hours. The original unrestricted definitions are unchanged. The strongest new unconditional lower bounds are now `HeadComplexity.WeightedNormalizedCounting.worstCase_real_lower` and `worstCase_real_log_lower`, exported publicly as `HeadComplexity.weighted_normalized_counting_worst_case_lower_bound` and `HeadComplexity.weighted_normalized_counting_worst_case_log_lower_bound`. For every $n\geq8$ they give

$$ W(n)\geq\frac{2^n-1}{n(n+8)},\qquad W(n)\geq\frac{(N-1)\log2}{n\log(32e^2N^2/(N-1))},\qquad N=2^n. $$

These improve the leading constant of the earlier normalized bound by a factor approaching two. They remain of order $N/n^2$ and do not refute the original conjecture. The public aggregate build passed with 4,136 jobs; both public declarations have transitive axioms exactly `propext`, `Classical.choice`, and `Quot.sound`. Implementation and public-export commits are `b74da76b` and `b0d5ca3c`.

The decisive optimized unrestricted finite count is, for $H\geq2$ and $2nH\leq N$,

$$ T\leq2\left(\frac{16e^2N^2(H-1)}{n^2H^2}\right)^{nH}. $$

The new `WeightedDegreeOptimization` module proves that separate positive numerator and denominator block weights cannot improve this degree-to-weight ratio: their product is at most $[D^2/(4(H-1))]^H$. At width $cN/n^{3/2}$ the logarithm of the resulting certificate divided by $N$ grows like $c\sqrt n\log2$; at width $cN\log n/n^2$ it grows like $c\log n\log2$. Thus this particular weighted count cannot cross either target for a fixed positive $c$.

The two requested high-margin estimates and their constant/additive width overhead remain completely kernel checked. A further conditional tradeoff, `SublinearOverheadRepairTradeoff.worstCase_gt_of_sqrt_overhead_repair`, shows that a repair using about $\sqrt n$ times as many heads with relative margin $\exp(-(n+1))$ would imply width lower bounds of order $N/(n^{3/2}\log n)$. The repair premise is explicit and unproved. A new quantitative written vertex bank uses $n+1$ admissible heads per corrected input, with controlled coefficient amplitude; it needs a bound on the number of exceptional inputs that is not supplied by active-basis cardinality.

The algebraic route now has a written capacity theorem for reduced ordinary Cayley-Bacharach configurations at both requested scales, using a weighted incidence estimate and a Hilbert-window inequality. The numerical window summation and the reduction from ordinary first-jet annihilation to reduced Cayley-Bacharach are kernel checked. The geometric incidence theorem and the resulting restricted capacity estimate remain written proofs. The indispensable missing hypothesis is access from every original narrow truth table to these ordinary configurations. Boolean projection moments alone do not supply it.

A written all-kernel lifting counterexample now forces superlinear support overhead of order $H^{7/6}$, even allowing arbitrary new poles and residues. It preserves every function of every Boolean projection and does not rule out preserving one reciprocal score or its signs. The new kernel-checked `CauchyMomentInterpolation.exists_original_heads_with_moment_cancellation` makes that distinction concrete: any real Boolean score table has an exact admissible representation with $N+D+1$ heads and ordinary scalar denominator moments through $D$ zero. Its width is too large at the critical scale.

The new `AffineFiberCapacity` and `ProjectiveFiberCapacity` modules count tables of arbitrary head width when the joint denominator observations have few affine or projective fibers. Both have explicit half-table criteria and standard-axiom audits. No dichotomy forcing few fibers has been established. `GlobalParityMargin.relativeMargin_parity_le` proves that every original representation of parity has relative margin at most $2/N$, regardless of its width. Conversely, a written Boolean monomial compiler gives every truth table unrestricted-width atomic margin at least $3^{-n}$. Thus a dual argument that forgets support size cannot distinguish the exceptionally tiny margins in the requested estimates.

The active-basis repair route has now failed even under unimodularity. Existing exact one-head examples have an integer inverse basis and two different full truth tables with full unit gaps. A new origin-containing unimodular example is being kernel checked. These refute uniqueness and constant-denominator replacement; they do not bound the number of feasible branches or refute a representation-changing repair.

A read-only remote refresh found newer branches `origin/ar/027ac8030b43` at `3869e33a` and `origin/ar/3d65948e8222` at `0e145215`. The former still gives the known original-model upper bound of order $N/(n\log n)$ and supplies polynomial signed-statistic and row-correction constructions. No requested unrestricted lower bound was found. The latter concerns a separate positional-model comparison. No code from these refreshed branches was imported.

The next genuinely different attempts are width-sensitive approximation using denominator concentration, joint support-sensitive atomic repair, and a Boolean split that exposes sums of Cauchy matrices with head-dependent row and column generators. The run continues through the remaining allocation. The final hour will be used for a fresh build, transitive axiom checks, and a committed handoff, while tractable proof work continues.

## Ten-hour checkpoint, 01:28 UTC

Elapsed active time is ten hours. The aimed unrestricted power saving and the logarithmic fallback remain open. The strongest unconditional result is now `HeadComplexity.BootstrapWeightedCounting.worstCase_real_log_lower`, with the simpler public form `HeadComplexity.bootstrap_weighted_counting_worst_case_lower_bound`:

$$ W(n)\geq\frac{N-1}{n(n+7)}\qquad(n\geq256),\qquad W(n)\geq\frac{(N-1)\log2}{n\log(16e^2N^2(n+8)/(n(N-1)))}\qquad(n\geq8). $$

The new kernel-checked corollary gives $W(n)\geq(1-\epsilon)N/n^2$ for every $\epsilon\gt0$ whenever $n\geq256$ and $\epsilon n\geq8$. These remain quadratic-denominator lower bounds. The implementation and public exports were built and checked with only `propext`, `Classical.choice`, and `Quot.sound`; the original definitions are unchanged. The initial bootstrap is commit `4b6181a5`, and the leading-constant corollaries are included in shared checkpoint `d9234e8f`.

The numerical counting barrier is now sharp at the quadratic scale itself. `WeightedCountBarrier.optimal_certificate_exceeds_all_tables_at_quadratic_scale` proves

$$ 2^N\lt2\left(\frac{16e^2N^2(H-1)}{n^2H^2}\right)^{nH}\qquad\text{if }n\geq4, H\geq2, 2nH\leq N, n^2H\geq N. $$

`AnisotropicWeightBarrier.every_coordinate_certificate_exceeds_all_tables` extends this obstruction to arbitrary positive coordinate weights satisfying the actual monomial degree constraints. Thus further optimization of these parameter weights cannot establish either requested gain. This is a statement about the upper-bound expression, not a lower count of represented tables.

The full-cube margin route has new constructive and negative evidence. `ActiveMarginImprovement.exists_strict_margin_improvement` proves that a bounded-amplitude correction strictly improving every active vertex gives an admissible local margin improvement with additive head overhead. An abstract sparse dictionary shows that even perfect outside control and repeated local improvements need not yield a constant-overhead endpoint. This is not an original-model counterexample. The new partial-label compiler has an audited written bound and a kernel-checked exceptional-set patch bridge; its source hypothesis still requires a quantitative gap away from a controlled exceptional set. Active-basis cardinality alone does not supply that hypothesis.

`ExactLayerGateLowerBound.original_nonnegative_layer_gate_heads_ge` proves that an exact nonnegative score supported on one Hamming layer needs at least $n$ original heads. A separately audited written argument gives an order $\sqrt n$ lower bound for constant-error uniform value approximation to the central-layer indicator. These rule out constant-cost value gates used in one proposed repair, not sign-preserving whole-table repair in general.

The joint-denominator capacity route now handles target-dependent groups of affine pencils, including all signed cancellation, in `LowParameterDenominatorCapacity` and `GroupedDenominatorCapacity`. Its half-table counts hold at both target scales under explicit denominator parameter and chart budgets. Access to those grouped families is still unproved. A written universal healthy representation of width at most $2323202N/(n\log n)$ and margin at least $\exp(-100n^2\log(n+1))$ is quantitatively audited; its width is too large to provide the required comparison repair.

Actual full-cube norm optimization now has checked algebraic cross-moment identities. At a putative duplication-stable optimum, within-head second moments vanish, while the total cross moment is $1-K^2$ for amplitude budget $K$. A negative cross-head term is therefore forced when $K\gt1$. Converting that term into a norm-controlled, width-preserving improvement is the first missing lemma. Value approximation of products alone does not supply such an improvement.

The one-head actual-basis route has a useful new distinction. `MinorityContactCapacity.one_minority_unique` forces one full truth table in every one-minority unit-contact branch; the corresponding fixed-dimensional continuation count is also checked. Yet `OneMinorityBalanceObstruction` gives an exact admissible example whose every fixed-branch denominator satisfies $22b_0\leq\sum_i b_i$. A numerical claim of a branch forcing $b_0=0$ was rejected by exact arithmetic: its constraints include $-2b_0-2b_4\geq0$, so its reported positive witness was infeasible. All floating searches are marked as finite exploratory evidence.

A combined preflight built 114 changed modules and transitively audited 2,563 theorem declarations with no project axioms. More modules have since been added, so this is a checkpoint rather than final verification. The final hour begins at 02:28 UTC and will rebuild the default target, every changed research module, and all transitive axiom checks.

A read-only remote refresh found `origin/ar/3d65948e8222` at `632a10d0`, concerning positional-architecture separation, and no change to the relevant universal upper-bound branch `origin/ar/027ac8030b43`. No code was imported from this refresh.

The next genuinely different attempt uses complementary unit-contact subspaces and Boolean chamber geometry. A determinant bound controls the collective exterior expansion of an actual Boolean interpolation matrix, but bare box packing cannot finish the argument: a fixed two-dimensional involution already admits infinitely many disjoint normalized coefficient boxes near a boundary face. The finite Boolean normal rows must enter the remaining lemma. In parallel, work continues on two-extremum norm-stationarity identities and the quantitative exceptional-set compiler. The run remains active.

## Final-hour checkpoint, 02:28 UTC

Elapsed active time is eleven hours. The strongest unrestricted worst-case theorem remains the bootstrapped logarithmic-denominator bound and its finite consequence $W(n)\geq(2^n-1)/(n(n+7))$ for $n\geq256$. The new declaration `BootstrapWeightedCounting.worstCase_eventually_one_sub_epsilon`, publicly exported, states directly that every constant below one eventually works in front of $2^n/n^2$. The target power saving and logarithmic fallback remain open. The original model and complexity definitions are unchanged.

The new unconditional almost-all theorem `QuadraticScaleTypicalComplexity.card_le_exp_one_sub_epsilon` bounds the number of tables of width $H\leq(1-\epsilon)N/n^2$ by $2^{(1-\epsilon/2)N}$ when $n\geq8$ and $\epsilon n\geq20$. Its hypothesis and entropy arithmetic passed an independent audit. This remains a quadratic-scale statement.

The coefficient-comparison repair of the unit-contact argument now has an exact eight-bit counterexample. `TwoMinorityNeighborObstruction` proves two admissible full-cube unit-gap witnesses on the same basis, with the same signs of every affine coefficient comparison against $0,\pm r,\pm1$, but different truth tables. Their ratios are $17/9$ and $3$; the decisive unchecked subset sum at vertex 15 is $r-2$. Both integer witnesses, all 256 cube inequalities, basis injectivity, and the differing label are kernel checked. This rules out that specific determination lemma, not a bound on the total continuation entropy.

The positive reciprocal expansion is now fully kernel checked and connected to every original head. `OriginalAnchoredExpansion.original_head_expansion` gives exact affine face blocks with total full-cube block norm at most $(n+1)\|\phi\|_\infty$, and every block is uniformly approximable by one genuine head. The number of blocks is exponential, so the expansion supplies no narrow repair. The high-order mixed-point amplitude obstruction remains an independently audited written consequence.

The exact-address route has exposed a separate obstruction: a written construction hides every original width $H$ truth table on the opposite face of a score identically one on the chosen face, using $2H+1$ genuine heads and amplitude at most $2D+2$. `RelativeMarginRestriction` checks that every healthy comparison representation restricts to a healthy source representation, including the contrapositive over every comparison representation. A singular score fiber therefore cannot be discarded through generic head identifiability. The fixed half-cube labels still give the trivial half-table entropy ceiling, so this is not itself a large-class lower count.

A written generic quadratic-reciprocal rank theorem now forces a regular duplication-stable dual onto the common head extrema once $H=O(N\log n/n^2)$. Under its explicit KKT hypotheses the centered amplitude is one. Exceptional configurations, existence of a regular optimum, and support recycling remain unresolved. The first attempted unrestricted same-width improvement lemma also fails: the five-bit threshold at Hamming weight two has a sharp one-head relative margin $5/(11+4\sqrt6)$. Its scalar four-row argument is kernel checked; the full original-model universal upper bound has just built, and work continues on the matching actual-head witness.

The first final-hour verification ran against source `1fa75211`: the default `lake build` passed with 4,145 jobs; all 140 committed changed modules built with 9,317 jobs; all 2,981 theorem declarations passed the transitive axiom audit; and all fourteen explicit main-theorem axiom prints used only `propext`, `Classical.choice`, and `Quot.sound`. Logs use the prefix `final-hour-start`. A fresh final audit will include the remaining committed proof work. The run continues through the final hour.

## Closing checkpoint, 03:26 UTC

Elapsed active time is 11 hours and 58 minutes. The allocation ends at 03:27:59 UTC, and final documentation and integrity checks continue through its closing minutes. The requested unrestricted power saving and logarithmic fallback remain open. The strongest unconditional theorem remains `BootstrapWeightedCounting.worstCase_real_log_lower`; its simpler consequence is

$$ W(n)\geq\frac{2^n-1}{n(n+7)}\qquad(n\geq256). $$

The eventual corollary `worstCase_eventually_one_sub_epsilon` proves every fixed leading constant below one for $2^n/n^2$. These statements concern the original `HeadComplexity.worstCaseHeadComplexity`. No original admissibility, computability, or complexity definition was changed.

Both requested margin-restricted half-table estimates are kernel checked, including the direct logarithmic calculation and constant/additive comparison-width overhead. They remain intermediate results: there is no proof of a uniform healthy repair at comparable width, and no adequate count of the tables for which every comparison representation has insufficient margin.

The decisive unrestricted obstruction remains the exact inequality in `WeightedCountBarrier.optimal_certificate_exceeds_all_tables_at_quadratic_scale`:

$$ 2^N\lt2\left(\frac{16e^2N^2(H-1)}{n^2H^2}\right)^{nH}\qquad(n\geq4, H\geq2, 2nH\leq N, n^2H\geq N). $$

It rules out further optimization within that cleared-polynomial counting certificate, including the verified coordinate-weight variants. It does not lower-bound the represented truth-table class. The precise remaining margin-free fallback lemma is the bound $|\mathcal C_c|\leq\exp((nH+1)n/\log n)$ for every globally feasible coherent certificate at $H=\lfloor N\log n/(50n^2)\rfloor$. Its original-model consequence is already kernel checked in `CoherentDenominatorCharts.worstCase_gt_of_logarithmic_chart_entropy`.

The final hour produced additional exact original-model structure. Same-width positive normalization, allowing the global output complement, retains one third of the relative margin, with a truth-table count loss at most two; the factor three is sharp. Nonnegative-head sums with nonnegative bias cannot uniformly compile the explicit mixed-orientation reciprocal product below error $4/25$. Near-unit margin for a nonconstant table forces an existing strict one-head classifier. The fully kernel-checked `LiteralMarginNonattainment.hasRelativeMargin_iff_lt_one` proves that every fixed positive width admits a literal at exactly the margin thresholds below one in dimension at least two. `PositiveLiteralNonattainment.relativeMargin_lt_third` excludes the canonical positive endpoint at every width. The scalar `TwoValuedFaceGeometry.four_corner_labels_constant` is kernel checked; the stronger classification excluding unit margin for every nonconstant table remains written mathematics.

The last genuinely different attempt revisited compactification after the nonattainment result. A written finite-dimensional compactness argument proves that the best margin is attained in the closure of normalized full-cube value tuples; density transfers every strictly smaller margin back to genuine heads at unchanged width. It gives no numerical margin bound. The positive-partition construction further puts every original width $H$ truth table in strict sign germs near one fixed value tuple at width $H+2$. Its head parameters need not converge to one fixed parameter tuple. Thus counting the discrete boundary value strata alone cannot supply the missing entropy reduction. The next mathematical step must control the original joint Boolean-row geometry or prove a quantitative optimum bound across its boundary strata; generic rank, parameter monotonicity, and block-convexity do not do so.

Final source verification at 03:19 UTC checked revision `44da9da5dc67ada89b846b116f83de5f9d454768`: default `lake build` passed with 4,145 jobs; all 158 changed modules built with 9,335 jobs; all 3,170 theorem declarations passed the transitive axiom audit; and all fourteen explicit main-theorem axiom prints used exactly `propext`, `Classical.choice`, and `Quot.sound`. Later commits contain documentation and verification artifacts only. The original-definition files and the complete audited Lean tree were checked unchanged after that audit. All finite optimization searches remain labeled exploratory evidence, not proofs.

Final read-only refreshes at 03:21 and 03:23 UTC found the relevant external branches unchanged: `ar/027ac8030b43` at `3869e33a`, `ar/3d65948e8222` at `632a10d0`, and `ar/917a77699289` at `ca87f252`. No code was imported. The committed handoff records kernel declarations, written proofs, conditional lemmas, counterexamples, exact build results, and the remaining unrestricted gap.
