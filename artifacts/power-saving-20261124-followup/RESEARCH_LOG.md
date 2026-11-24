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
