# Beyond the Counting Bound

## Target and proof standard

Prove that the sequence $n^2W(n)/2^n$ is unbounded for the unchanged model in the attached `version-5.tex`.

$$ \forall C\gt0\qquad \forall n_0\qquad \exists n\geq n_0\qquad \exists f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace,\qquad H^{\ast}(f)\gt C\frac{2^n}{n^2}. $$

The desired conclusion is not an assumption in any argument. Denominators may depend on the target. Neither fixed-denominator dimension bounds nor exact real-table dimension bounds establish this Boolean sign-representation statement.

The source and start time are recorded in `run.json`. The attachment is outside this repository and is not modified.

## Initial audit

The manuscript's normalized score has a discrete sign and $2nH$ real parameters:

$$ S(x)=\sigma+\sum_{h=1}^H\frac{u_h\cdot x}{1+b_h\cdot x},\qquad \sigma\in\lbrace-1,1\rbrace. $$

Clearing denominators at each of the $2^n-1$ nonzero inputs gives parameter polynomials of degree $H$. The monomial $\sigma\prod_h b_{h,1}$ at $x=e_1$ proves that replacing this degree by the input dimension is invalid.

Warren's bound yields the exponent $1+2nHL_n$, where $L_n=\log_2(2e(2^n-1)/n)$. This proves the stated lower bound of order $2^n/n^2$ but no unbounded improvement factor.

The repository file `formalization/HeadComplexity/Results/CountingLowerBound.lean` makes the analytic theorem an explicit hypothesis named `WarrenStrictSignPatternBound`. Its finite reductions are formalized; Warren's theorem itself is not proved there. This distinction must remain visible in any new formalization.

## Approaches awaiting investigation

- Sharper sign counting for sums of fractions on the admissible positive-denominator domain.
- Positive reciprocal varieties, variation arguments, and constraints not captured by total parameter degree.
- Combinatorial or number-theoretic constructions forcing lower bounds uniformly over all denominator choices.
- Earlier research branches, audited for complete mechanisms and exact counterexamples to tempting shortcuts.

No theorem establishing the target has been proved at this checkpoint.

## Complete monotonicity and Boolean tangents

The [positive exponential interpolation theorem](complete-monotonicity-tangent.md) gives every Boolean tangent direction at a table equal to a single reciprocal head. One baseline extension works for every direction, and every mixed derivative has the strict sign required by complete monotonicity. The construction has explicit rational coefficients and a uniform positive perturbation interval. Independent exact arithmetic checks the coefficients through dimension ten and all binary directions through dimension three.

The extension uses exponentially many exponential terms. It therefore disproves an order-only tangent restriction, without controlling the permitted number of affine-ratio heads. The remaining sign-counting step must retain that factorization structure. No asymptotic lower bound follows.

## Boolean product base loci

The [two-factor audit](boolean-product-base-locus.md) classifies every pair of nonzero affine forms whose product vanishes on the Boolean cube. The resulting ordered base locus has exactly $n(n+1)$ reduced points. On three bits, the product map has eight generic ordered complex factorizations. An explicit positive exchange identity gives $n+1$ distinct unordered positive factorizations in every dimension; on three bits, four regular positive branches persist on an open set. The classification and exchange identities are Lean checked in `BooleanZeroProduct.lean`, and an independent rational verifier checks the three-bit Jacobians and tables.

These results invalidate an automatic division by head permutations in a proposed product-degree argument. They do not estimate the coordinate signs of the many-head tangent family. Recent matroid fiber and polar-degree formulas, together with hyperplane-covering results, were checked against this distinction. The required many-head sign bound remains a theorem-strength gap. No denominator exponent between one and two has been obtained.

## Binary active margins and positive multipliers

The [active-margin construction](binary-active-minima.md) starts from the regular sixteen-bit, three-head zero fiber. An exact rational dual calculation gives 96 nonzero coordinates, with 44 positive and 52 negative signs. An independent full-cube enumeration finds just ten additional zero scores, and exact tangent calculations give signed derivatives greater than fourteen at all ten. The inverse function theorem then gives, for every sufficiently small positive common margin, a regular strict local minimum of the squared numerator norm subject to all 65,536 cube inequalities. Exactly 96 constraints are active and have strictly positive multipliers. The rational dual equation and sign certificate are Lean checked in `CoordinateZeroDual.lean`. The complete zero set and its selected-plus-extra decomposition are also kernel checked in `CoordinateZeroCube.lean`; the rational tangent check and analytic argument have their separately stated audit scope.

This disproves the proposed blanket exclusion of regular full-cube constrained minima by a maximum principle. It does not bound their total number or the number of full-cube sign patterns. The asymptotic target remains unproved.

## Fixed-dimensional positive reciprocal obstruction

The [four-dimensional construction](positive-four-dimensional-shattering.md) turns the binary switching rectangle construction into strictly positive reciprocal heads. For $H=2^{r-1}$ it shatters $(r-1)H/2$ fixed positive rational points in four real dimensions, with margin greater than $1/4$, constant numerator one, and denominator constant one. A direct triangular recursion proves the required rectangle incidences. A geometric coordinate transformation then makes every head's value at least $4/5$ on an incidence and less than $1/(16H)$ otherwise. This independently disproves a linear parameter-count bound for positive real-input heads, even with fixed input dimension. It does not shatter a Boolean cube.

The finite-sum compiler is Lean checked as `HeadComplexity.PositiveReciprocalBoxGap.separated_box_sum`. Independent exact arithmetic verifies 53,024 scores, including every labeling in the two smallest instances. The binary switching construction and its general geometric encoding have complete written proofs; they are not claimed as Lean formalizations. The earlier affine scale bound excludes a literal encoding of the many geometric levels by a small affine Boolean table. The remaining problem is a sign-sensitive bound using the Boolean input structure, with unrestricted cancellation.

## First adversarial audit

**Counting refinements.** The two-block multidegree estimate recorded in the earlier `autoresearch-runs` commit `cc640ff`, theorem 217, has the form below, with an absolute constant $C$:

$$ \mathcal N(n,H)\leq\left(\frac{C4^n}{(n+1)^2H}\right)^{(n+1)H}. $$

Its source is the sign-condition estimate in [Basu and Rizzie, Theorems 12 and 13](https://arxiv.org/html/1507.03958). At $H=c2^n/n^2$, the logarithm of the displayed right side is $(c+o(1))2^n$. Thus the refinement still only excludes a bounded range of constants $c$. It cannot establish the selected target by itself. Status: blocked at the required unbounded improvement factor.

**Sparse algebraic counting.** [Rojas and Vidyasagar, Theorems 3 and 4](https://arxiv.org/html/math/0112208v3) replace total-degree bounds with normalized Newton volume and give an explicit block-degree entropy correction. A small degree in each head block does not alone eliminate the dependence on the number of blocks. No bound sufficient for this target has been obtained.

The direct [Newton-volume calculation](newton-volume-obstruction.md) shows that the common normalized parameter polytope has volume at least $(H/4)^{nH}$. This rules out a small-volume explanation for removing the logarithm. A method using more information than this volume would be a materially different approach.

**A misleading rational-network theorem.** [Pardo and Sebastian, Corollary 5.13](https://arxiv.org/html/2504.11345v1) concerns classifiers defined by the nonvanishing locus of rational functions over an algebraically closed field. Nonvanishing and positive-versus-negative classification are different predicates. Applying that theorem directly to the manuscript's real signs is invalid.

**Threshold-network capacity.** [Baldi and Vershynin, Theorem 3.1 and Section 10.3](https://arxiv.org/html/1901.00434) analyze threshold activations and impose a restriction on the growth of layer widths in their capacity lower bound. Their theorem neither applies to affine-ratio heads nor supplies a lower bound at the exponentially wide regime in question. A transfer of architectures would itself require a new proof.

**Margins and exact interpolation.** The manuscript's conditioning argument uses a positive normalized margin and a denominator contraction parameter bounded away from one. Neither is uniform over the allowed model. The regular-zero construction proves exact real-table interpolation with on the order of $2^n/n$ heads. Dimension counting for exact interpolation cannot exclude Boolean sign universality with fewer heads.

**Positive-domain oscillation.** The explicit construction in [reciprocal-oscillation.md](reciprocal-oscillation.md) gives $2^n-1$ positive zeros for a fixed linear functional along a one-head positive-denominator curve. Positivity alone therefore does not give the proposed low-oscillation shortcut. The generic identity and exact-zero statement have been proved in Lean.

**Existing complete counting formalizations.** The `xorformer-runs` commits `0fc32da` and `6f5c7d4` contain an unconditional strict Warren argument, with generic margins and constrained minima as major dependencies. The local manuscript-counting file remains conditional on its explicit Warren interface. Neither version yields the unbounded factor required here, so importing that development would not resolve the research objective.

## Second adversarial audit

**Real stability does not survive the needed quotient.** The earlier `xorformer-runs` commit `6195355` gives the following exact example. The admissible affine denominator $D=1/10+x+y+5z$ is real stable, whereas the Boolean reduction of its square is

$$ R=1/100+(6/5)(x+y)+26z+2xy+10xz+10yz. $$

It vanishes at $x=y=-13/10+i/10$ and $z=7/50+i/8$, all in the open upper half-plane. Direct symbolic rational arithmetic independently checked this zero and the Rayleigh value $-27/50$ at $(x,y,z)=(0,0,7/50)$. Thus stability of the unreduced denominator product does not provide the proposed invariant after Boolean reduction.

**Reciprocal-variety geometry.** [Kummer and Vinzant](https://arxiv.org/html/1610.04584) prove determinantal and hyperbolicity results for reciprocal linear spaces. [Rincon, Vinzant, and Yu, Proposition 3.10](https://arxiv.org/html/1907.08545) show that hyperbolicity passes to tangent spaces at real smooth points. Neither statement proves that sums of the manuscript's affine-ratio atoms retain a common hyperbolicity constraint. The required assertion for arbitrary signed numerators and target-dependent denominators is unproved. Status: blocked at a substantive geometric theorem, not a routine compatibility check.

**Finite candidate checks.** [experiments.md](experiments.md) specifies the exact admissible certificates and their independent integer verifier. In particular, a seven-point code support on eight bits has a four-head certificate, refuting the proposed isolated-support counting argument. Numerical failures were not used as evidence of infeasibility.

**Other reductions rejected as incomplete.** Fixed-denominator span dimension, full real-table interpolation dimension, the exact dual-certificate alternative, low-degree antipodal projections, and a proposed compression to sparse polynomial signs do not supply a lower bound for every allowed representation at the required scale. No general sparse-sign compression theorem has been proved here. Rephrasing the target through such an unproved assertion does not constitute a new proof mechanism.

The original target, architecture, denominator freedom, and worst-case definition have not been changed. No Lean declaration or paper proof establishing the selected asymptotic refutation exists in this work so far.

## Resumed audit: positive interpolation fibers

The first turn ended before the requested twelve hours. Research resumed on November 22 following the asker's correction. The target remains unproved and the duration requirement remains outstanding.

A new test concerned a possible way to remove the degree factor in sign counting: uniqueness, up to head permutations, of positive-denominator interpolation from as many cube evaluations as there are effective parameters. That proposed uniqueness statement is false. The computer-assisted theorem in [positive-fiber-obstruction.md](positive-fiber-obstruction.md) gives two regular, distinct two-head representations agreeing on 21 vertices of the five-bit cube. Their scores differ by more than $1/10$ at two other vertices. The inverse function theorem makes the ambiguity persist on an open set of interpolation data. Two independent exact rational verifiers check the contraction and separation certificates. A weaker quantitative bound on positive branches is not ruled out, but has not been proved.

[Zhang, Zhang, Loh, and Liang](https://arxiv.org/html/2201.13132v2) establish generic identifiability for particular two-component ranking mixtures. Those models have coupled probability numerators and substantially more structured observations; their theorem does not establish uniqueness for the manuscript's arbitrary affine numerators. The counterexample above directly tests the latter model.

[Grosdos, Robeva, and Zubkov](https://arxiv.org/html/2509.11088v1) study rational-function identities and coefficient varieties for reciprocal-activation networks. Their ambient space is a space of polynomial fractions, rather than Boolean sign tables. Their dimension and defining-equation results do not imply the selected lower bound.

[Zhang and Kileel](https://arxiv.org/html/2311.05116v3), Theorem 2.6, bound metric entropy using intrinsic dimension, section-component counts, and a logarithmic ambient-dimension term. Their rational-network application controls continuous outputs and Lipschitz losses. The resulting ambient-size logarithm and the absence of a uniform margin prevent a direct improvement of the unrestricted Boolean counting bound.

## A discrete matching mechanism and its limitation

The new [integer construction](integer-fiber-family.md) strengthens the finite ambiguity example: for every $n\geq5$, a two-head evaluation map on $4n$ cube vertices has at least $2^{n-4}$ distinct regular positive preimages. A five-bit integer certificate and a block triangular Jacobian argument prove this statement. It does not contradict an exponential upper bound in the number of parameters.

A different [pole-matching construction](pole-matching-fibers.md) uses the Chinese remainder theorem to distinguish independent permutations of poles in different selector coordinates. In an affine parameter slice with $2Hk$ free parameters on $n=k+\lceil\log_2(2H)\rceil$ input bits, it produces $(H!)^{k-1}$ regular positive interpolation branches. This rules out a bound $C^{nH}H!$, for fixed $C$, uniformly over such parameter slices, including sequences with $H=\Theta(2^n/n^2)$.

The audit distinguishes branch counts from sign counts. Every score in this matching construction has the same Boolean sign pattern. Consequently, the factorial branch count cannot be interpreted as a large family of Boolean functions, and it does not refute an estimate that counts signs directly. At the critical head scale its logarithm is only of order $2^n\log n/n$. A sign-sensitive argument, or a sharper estimate that accommodates these branches, remains necessary. No sufficient estimate of either kind has been proved here.

## Code-supported candidates are inexpensive

The construction in [code-supported-upper-bound.md](code-supported-upper-bound.md) proves that a function supported on a binary affine code of rank $r$ has head complexity at most $W(n-r)$ plus the sum of the parity-check row weights. It uses information coordinates, exact rational interpolation of parity penalties, and a finite strict-margin perturbation to recover admissible denominators. In particular, arbitrary subsets of a Hamming-code coset at length $n=2^r-1$ have complexity at most $(1+o(1))2^n/n^2$. This rules out that entire proposed hard family. It does not prove the target lower bound and does not imply a universal upper bound for all Boolean functions.

## Separate affinity is insufficient

The new [multiaffine shattering construction](multiaffine-shattering.md) proves that separate affinity in every parameter, even on the positive orthant, permits $\Omega(p\log p)$ independent sign tests in $p$ parameters. It uses Hall matchings and permutation interpolation. An explicit variant uses affine lines over finite fields, with a direct pair-intersection proof of the matching condition. Thus a linear VC bound cannot follow from separate affinity alone. The special coefficient structure of the head evaluations is not covered by this counterexample, and a bound exploiting that structure remains unproved.

The primary [Goldberg and Jerrum theorem](https://www.cs.ox.ac.uk/people/paul.goldberg/papers/goldbergjerrum.pdf), Theorem 2.2, uses the total degree of the parameter predicates. In this application that degree grows with the number of heads after denominators are cleared. Treating the reciprocal activation as degree one does not turn the network's final predicate into degree one. The theorem therefore retains the logarithm that prevents the selected improvement.

The finite-field construction is now fully formalized, including its unbounded ratio of tests to parameters. `HeadComplexity.FiniteFieldLines.unbounded_multiaffine_tests_per_positive_parameter` depends only on the standard Lean foundational axioms. The explicit eight-element-field example gives 108 independent sign tests in 64 positive parameters. This is an audited obstruction to the generic multiaffinity argument; it is not the requested head-complexity theorem.

The [parameter-line degree obstruction](parameter-line-degree.md) now proves, in the actual admissible model, that a polynomial predicate in the original coefficients must have degree at least the number of heads. This also gives a concrete counterexample to the head-independent degree step in Anthony and Bartlett's proof of Theorem 8.11. It does not refute their VC statement. The original Bartlett and Williamson result retains a logarithm of the total parameter count, so this literature route remains blocked at the required stronger counting theorem.

## Arbitrary positive linear sections can have many components

The [positive functional grid](positive-functional-grid.md) uses a squared polynomial numerator and exact partial fractions. On $n=d+k$ bits it gives a fixed linear functional of admissible $H$-head score evaluations whose parameter-space zero set is a grid of $(2^{d-1}-1)^{kH}$ isolated nondegenerate minima. Small positive levels have at least that many separate regular components, and this persists under small perturbations of the functional. At $k=d$ and $H=\lfloor C2^n/n^2\rfloor$, even the head-permutation orbit count has logarithm at least $(C/4+o(1))2^n$.

All scores in this construction are strictly positive on the entire cube. Hence the construction blocks a proposed bound on arbitrary linear-section preimages, while yielding only one Boolean sign pattern. A successful counting argument must use the specific coordinate sign tests or another invariant; replacing them by arbitrary evaluation functionals loses essential information. The target lower bound remains unproved.

## An exact mean value identity and a saddle obstruction

The [mean value identity](reciprocal-mean-value.md) gives a positive average of denominator-parameter evaluations with weights independent of the Boolean input. It is proved in Lean as `HeadComplexity.ReciprocalMeanValue.reciprocal_mean_value`. An elementary maximum-principle argument and direct differentiation show that fixed linear functionals of a head have no nonconstant interior local extrema in the full positive denominator domain. These latter consequences are written proofs, not Lean declarations.

The distinction between extrema and saddles is essential. The [full-domain saddle construction](reciprocal-saddle-grid.md) gives at least $\lfloor(d+1)/2\rfloor^k$ nondegenerate critical points for a single positive head on $d+k$ bits, with exactly one negative Hessian eigenvalue at each specified point. All 81 points of the nine-bit example have been checked using exact rational arithmetic. For equal blocks the logarithm of the critical-point count grows as $(n/2)\log n+O(n)$, so a fixed exponential bound in the number of denominator parameters is false.

The averaging identity has not been converted into a bound on coordinate sign patterns. Convex averaging can enter an orthant even when none of the averaged vectors lies there, and the saddle construction has only one Boolean sign pattern. This approach is blocked at the required sign-sensitive theorem. Neither auxiliary result proves an improvement to the manuscript's worst-case lower bound.

## Product tangents and finite interpolation checks

The [product-tangent audit](product-tangent-audit.md) identifies the cleared numerator as a tangent vector to a Hadamard product of affine evaluation tables. The tangent identity is exact but supplies no sign count. An explicit submodularity calculation then shows that the relaxed cone of positive log-submodular tables has every Boolean sign vector as a logarithmic tangent at a one-factor baseline. Thus that relaxation discards the necessary factorization constraint and cannot prove the target.

The [reciprocal-jet computations](reciprocal-jet-ranks.md) record 64 exact finite-field rank calculations, including a full-row-rank matrix with 8188 rows and 8192 columns. These test a possible critical-point construction, not the head lower bound. No general interpolation theorem is inferred from the finite results. Four additional admissible representations of fixed random truth tables have also passed independent exact verification; their scope is stated in [experiments.md](experiments.md).

## Coordinate zero fibers and another literature check

The [four-bit minor](zero-score-minor.md) disproves a proposed fixed-denominator rank bound at coordinate zeros. A separate integer search then found a stronger obstruction: the [regular-coordinate-zero construction](regular-coordinate-zeros.md) has full parameter rank for three heads on every dimension at least sixteen. Its base has an independently verified invertible 96 by 96 rational Jacobian at 96 exact zero scores. A coordinate-cloning argument extends it to every larger dimension. Thus the unsuccessful small numerical zero-fiber searches did not indicate a general rank-defect theorem. No asymptotic lower bound follows from these constructions.

The [recent rational-exponential network argument, Theorem G.17](https://openreview.net/pdf/2a35cc2c1f09b1a11f5274d5282ea47c0fd44423.pdf), explicitly multiplies the positive denominators across all hidden units. Its polynomial degree grows linearly with width, and its displayed dimension bound retains logarithms of width and total parameter count. The abbreviated near-linear notation in its theorem statement therefore does not remove the logarithm needed here. Its activation family also differs from the manuscript's affine-ratio heads. No stronger head-count theorem is imported from it.

The [pseudoproduct synthesis audit](pseudoproduct-literature-audit.md) examines a genuine construction of order $2^n/n^2$ in combinatorial circuit theory. Its operations are XOR and products of affine Boolean functions. Parity gives an exact obstruction to translating each such product into a bounded number of attention heads. The construction cannot be imported merely because its asymptotic expression matches the disputed bound.

The [priority-list obstruction](priority-list-obstruction.md) supplies a separate exact counterexample to replacing positive heads by a bounded number of deterministic priority rules. An explicit function on $4k+2$ inputs has exactly two heads but needs at least $k+1$ priority lists, even with a free affine score. The proof uses a restriction that fixes at most one coordinate per list and a four-point affine obstruction. An exact weighted-permutation averaging identity for individual positive heads is proved in the same note; the counterexample rules out the proposed constant-cost derandomization of that identity.

## A different stability invariant also fails

The [product-table example](product-table-stability.md) addresses a different proposed invariant from Boolean reduction of a polynomial: stability of the generating polynomial whose coefficients are the denominator-product values on the cube. Each individual positive affine denominator has a stable value-table generator, by an explicit upper-half-plane calculation. Four such denominators on four bits nevertheless have a product-table generator with an exact upper-half-plane zero and a negative Rayleigh difference. The associated measure with a positive external field has a positive covariance. Both the complex zero and the covariance have been checked in Lean and independently with rational arithmetic. Thus this stronger-looking value-table formulation does not repair the earlier stability approach. The sign-counting target remains unproved.

## Further interpolation audit

The [reciprocal-jet calculations](reciprocal-jet-ranks.md) now include completed matrices with 16324 rows in dimension fourteen and 32670 rows in dimension fifteen. Both have full row rank modulo 65521, with nonzero selected-minor determinants. The blocked elimination records its exact-integer arithmetic bounds and independent small-matrix checks. These finite ranks do not establish an asymptotic interpolation theorem or a head lower bound.

A separate symbolic calculation proves that the same full-rank assertion cannot hold in characteristic two or three once there are at least two pole blocks: each block contains the constant function in its row span, yielding one independent relation per additional block. The normalized identities are kernel checked in `ReciprocalJetCharacteristic.lean`. This identifies a specific obstruction to a small-characteristic coding approach, without drawing a conclusion about the real model.

## Additional primary-source checks

The [recent-counting audit](recent-counting-audit.md) records the exact max-min relative-rank bound of Basu and Parida, including its real-locus hypothesis and its substitution for Boolean sign orthants. Even under optimistic degree assumptions, that expression remains at the original quadratic-denominator scale. The same note distinguishes the analog-formula and fractional-set-function results from the unrestricted head problem. None supplies the missing asymptotic factor.

## Projective affine-statistic compiler and minimal infeasibility

[The projective construction](projective-affine-statistic.md) proves that a degree $K$ polynomial threshold predicate in any affine statistic uses at most $K$ heads, including mixed-sign affine coefficients. The construction and its ordered sign-change consequence are Lean checked. It follows that parity with any one vertex flipped uses $n-1$ heads; the upper bound and feasibility on every proper subset of the parity sample are formalized. Full parity still needs $n$ heads. Hence the parity constraints at head count $n-1$ form a minimal infeasible family of size $2^n$. This rejects a general polynomial-size Helly certificate in the parameter count. It is an auxiliary construction and obstruction, not progress establishing the requested asymptotic lower bound.

## Denominator orders fail to encode numerator feasibility

[The exact four-bit counterexample](denominator-orders.md) keeps the strict cube ordering of each of two positive affine denominators unchanged but changes which signs can be realized by arbitrary affine numerators. A ten-row integer annihilator proves infeasibility for one pair; the other has a strict integer-coefficient witness, formally realized with two heads. The matrices, annihilator, orders, infeasibility and feasibility are Lean checked. Thus a reduction to denominator order types alone cannot supply the missing counting estimate. The stronger oriented-matroid fewnomial theorem still requires a separate chamber estimate.

**Convex perspective.** The exact square-coefficient shift makes each false-label constraint a convex quadratic-over-linear epigraph, equivalently an arrow-matrix positive-semidefinite constraint. [The explicit audit](convex-perspective-audit.md) also constructs convex cones in three dimensions, with a common strict interior point, realizing every finite incidence table. Lean verifies the scalar and weighted perspective inequalities, the exact shift, and the cone construction. General convexity or spectrahedral representability cannot supply the target count. The special shared arrow structure remains an unproved theorem-strength gap; this approach is blocked.

## Open-code pole interpolation

A materially different mechanism now closes an auxiliary interpolation question: [products of perfect open-neighborhood codes](open-code-pole-interpolation.md) partition the cube into tiles of quadratically many points. A two-literal numerator isolates each assigned point on its center's distance-two sphere. A quantitative pole perturbation yields a strictly diagonally dominant matrix, and polynomial root avoidance transfers its nonzero determinant to strictly positive affine coefficients.

For $n=2^{r+1}$ this gives a full-span reciprocal second-order jet family using $q=4\cdot2^n/n^2$ positive forms. The code partition, Boolean isolation, determinant estimate, positive transfer, exact center count, and interpolation conclusion are assembled in Lean. The extension to every $n\geq2$ using fewer than $16\cdot2^n/n^2$ forms is also formalized, in `AllDimensionsJetInterpolation.every_dimension_full_rank`. Exact modular checks in dimensions two through eight independently verify finite instances.

This is a theorem for independent quadratic numerators over cubed affine denominators. Those interpolation coefficients are not the parameters of actual heads. The new construction neither improves the worst-case head lower bound nor proves the disputed upper bound. The head-count inference remains blocked at an unproved realization or sign-counting step. The target remains unchanged and unproved.

The [single-center compiler audit](quadratic-jet-compiler-obstruction.md) gives an explicit family of $2^{k^3}$ quadratic threshold functions on $3k$ bits. The manuscript's unrestricted counting bound implies that some require more than $k/24$ heads, even though each is the sign of a quadratic jet combination at one fixed positive denominator. Lean proves the explicit quadratic polynomial, injective family, exact cardinality, and integer exponent comparison. The analytic counting application is a written proof. Conversely, a spectral decomposition and symmetric finite differences give an upper bound of $2n+3$ heads for every quadratic predicate. The finite-difference identities, positivity, error bound, and sign-preservation inequality are Lean checked; their assembly into heads is a written proof. This identifies a linear worst-case conversion cost. It does not prove that costs add over centers or improve the exponential worst-case lower bound.

The [additive-combinatorics audit](additive-combinatorics-audit.md) checks the hypotheses of inverse Littlewood-Offord results and threshold-gate random restrictions. Positive binary weights give exact concentration $2^{-n}$, and a reciprocal with these weights retains dependence on every free coordinate under every restriction. Thus neither polynomially large concentration nor elimination of real-valued heads follows from the cited theorems. A November 2026 nondeterministic-degree result also concerns a different predicate and does not count affine-ratio heads. These transfers remain blocked.

A separate [Fourier compression obstruction](fourier-compression-obstruction.md) uses the classical complete quadratic bent function. On $2m$ bits it has exactly $m$ heads, but every strict Fourier sign polynomial needs at least $2^m$ terms. The weight-profile head count is Lean checked; the autocorrelation and norm proofs are written explicitly. This rules out a polynomial Fourier-support compiler for arbitrary head scores. The result is basis-specific and does not supply the selected worst-case lower bound.

## Stabilization closes a further critical-point shortcut

The [new transverse stabilization construction](stabilized-reciprocal-saddles.md) strengthens the earlier saddle obstruction. A rational transverse stabilizer has an explicitly invertible Hessian. A simultaneous contraction argument, with a specified rational scale, preserves every point of an exponentially large scalar zero grid. It gives at least $(2^{d-1}-1)^k$ nondegenerate critical points of a fixed linear functional of one positive reciprocal head on $d+k$ bits. A logarithmic variant gives $(2^d-1)^k$ critical points for a weighted logarithmic potential.

For equal blocks, both logarithms have quadratic order in the number of bits. Independent heads preserve this obstruction at the critical exponential width, even after head permutations are removed. A separate lift of the logarithmic potential includes all normalized numerator parameters: the functional $u\cdot\nabla\Phi(b)$ has an invertible off-diagonal Hessian at each point with $u=0$ and $b$ a nondegenerate critical point of $\Phi$. Thus an unrestricted small critical-point count in the full normalized parameter domain cannot provide the missing improvement. Every lifted score is identically one, so there is only one Boolean sign table.

The explicit construction, contraction, and free-numerator lift are written proofs. Five algebraic ingredients are Lean checked in `StabilizedReciprocalSaddles.lean`, and exact rational computations verify eight instances across the reciprocal and logarithmic cases. Neither an intermediate-exponent lower bound nor the selected unboundedness target has been established.

## Positive Cauchy fibers and compatible local offsets

The [permutation-fiber construction](permutation-fiber-shattering.md) supplies six reciprocal tests on three positive parameters that realize every binary pattern, with strictly positive poles and residues. Every individual test is strictly decreasing and strictly convex. The mechanism uses regular Cauchy fibers indexed by permutations, a complete rank calculation for their compatible first-order offsets, and a rational perturbation with an explicit error bound. The final 64 witnesses are independently evaluated with exact fractions and checked by `HeadComplexity.PositiveMobiusFiberShattering.six_positive_tests_shattered`.

The complete offset compatibility calculation is essential: offsets at the six branches satisfy one alternating relation, which the retained certificate obeys. This is a result for freely chosen reciprocal queries. It does not show that the queries are evaluations on the full Boolean cube in the manuscript's model, and it does not establish an asymptotic head lower bound. Larger finite searches remain experiments; an unsuccessful search is not an impossibility theorem.

## Regular critical image points after normalization

The [projective critical-point construction](projective-critical-points.md) removes a specific limitation of the earlier constant-score example. It normalizes the values at singleton inputs, builds a logarithmic potential with many nondegenerate critical points of its squared weighted-gradient norm, and transfers them to critical points of a fixed linear functional on the normalized table image. Selected pair evaluations recover every denominator parameter by an invertible linear system. Thus the image points are regular, distinct, and nonconstant.

The logarithm of their number has quadratic order in the input dimension. All the corresponding scores still have the same positive Boolean sign table. The construction concerns the specified singleton normalization; no full-table norm claim or independent-head amplification on the summed image is asserted. Four algebraic ingredients are Lean checked in `ProjectiveCriticalPoints.lean`; the analytic theorem is a written proof. The selected worst-case lower bound remains unproved.

## Nine tests from four positive parameters

A different finite mechanism now gives [nine tests on four positive parameters](four-parameter-shattering.md), exceeding twice the parameter count in the separable reciprocal relaxation. Four ordered coordinate comparisons feed fixed small-integer threshold gates; a geometric pole scale transfers all 512 patterns to reciprocal tests with an explicit positive margin. Exact rational verification, independent enumeration of all 10,000 cut vectors, and `HeadComplexity.MobiusFourParameterShattering.nine_tests_shattered` check the result. The residues are signed. The full Boolean-cube architecture imposes additional query constraints, so this is an obstruction to a proposed counting shortcut, not a head-complexity lower bound.

## Unbounded shattering by positive reciprocal tests

A new mechanism replaces the finite searches with a general theorem. The [reciprocal Hall-selector construction](reciprocal-matching-shattering.md) combines affine lines over finite fields, distinct representatives, and a two-term reciprocal level selector. On $2q^2$ positive parameters it shatters $q(q+1)\log_2(q)/2$ freely specified queries. Reciprocal inversion then doubles the parameter count and makes every residue strictly positive, while retaining every labeling with a uniform margin. Thus even strictly decreasing, strictly convex separable reciprocal tests have an unbounded tests-per-parameter ratio.

Both general shattering theorems and the positive-residue conversion pass Lean with only the standard foundational axioms. Independent exact verification checks 1,454 selector inequalities and 3,248 final test values. The query poles and residues here are freely specified. Their embedding on singleton Boolean inputs uses as many input coordinates as queries; it does not give a small-dimensional full-cube construction. This refutes a general linear VC shortcut, but neither the requested unboundedness statement nor any exponent between one and two is proved.

## A direct coordinate-fiber audit and a scale invariant

The [regular coordinate-fiber certificate](coordinate-score-fiber.md) works in the actual six-bit architecture. Two positive-denominator three-head scores agree on 36 specified real evaluations, have nonsingular square evaluation Jacobians, and acquire different strict labels at one unsampled vertex under the same constant readout. A 36-dimensional contraction argument with integer interval bounds certifies the second branch. The original Jacobian determinant is nonzero modulo 65521. The inverse function theorem then gives an open set of sampled values with both branches. This is a complete written counterexample to generic uniqueness for that coordinate projection; it is not an asymptotic branch-count theorem.

A separate [dominant-summand invariant](positive-subset-scales.md) limits the number of multiplicatively separated values of positive affine subset sums and their ratios. Its two finite packing theorems pass Lean. They exclude the literal geometric pole tables of the free-query Hall construction from a small-dimensional affine substitution. They do not control exact signs under unrestricted cancellation. Both approaches remain blocked at their sign-counting step, and the selected worst-case lower-bound target remains unproved.

## Homogeneous all-powers monotonicity is still a relaxation

The [coverage-coordinate construction](homogeneous-geometric-tangents.md) realizes every small Boolean perturbation of a one-factor value table using a fixed family of positive linear forms with variable positive real exponents. The resulting functions remain homogeneous of degree one, and every negative power remains strictly completely monotone. The baseline is independent of the chosen perturbation. Explicit subset inversion, a positive integral formula, and a quantitative Neumann-series estimate prove this in every dimension.

This closes a proposed analytic relaxation: neither homogeneity nor complete monotonicity of all negative powers retains the needed integer-factor restriction. The construction is generally nonpolynomial and does not supply an attention-head representation. Lean checks the coverage kernels and scale identities; independent exact arithmetic audits the inverse matrices, coefficient bounds, and budgets. The asymptotic sign count for integer products and their admissible tangent scores remains unproved.

## Three additional transfer checks and a reciprocal degree obstruction

The [transfer audit](latest-transfer-audit.md) checks a recent integer-polynomial parity correlation theorem, tensor-network VC bounds, and subadditivity of list replicability under joins. Explicit examples distinguish parity phases from real signs, exact tensor values from their signs, and disjoint-domain joins from addition of real scores. In particular a single admissible head has a Hilbert-matrix flattening of full exponential rank. None of those published theorems supplies the missing representation or composition statement.

The [reciprocal degree audit](reciprocal-boolean-degree.md) gives an explicit family of binary affine bases without broken circuits. Integer reduction transfers them to characteristic zero, and the reciprocal-space degree formula of Proudfoot and Speyer yields degree at least $2^{n(n-1)/2}$. Restricting all affine denominator coefficients to be positive preserves the complex Zariski closure, even though these reciprocal tables have only one sign pattern. The matroid comparison is Lean checked. Thus replacing the global degree by a subquadratic logarithmic bound is invalid for this parametrization; the needed positive real sign-region bound is still unproved.

## Polynomial moments recover integer factor multiplicities

The [homogeneous polynomial rigidity audit](polynomial-monotonicity-rigidity.md) gives a complete written proof that complete monotonicity of arbitrarily small negative powers forces a positive homogeneous polynomial to be a product of nonnegative linear forms. The positive Laplace measure becomes radial by homogeneity. Power moments and a polynomial square force finite directional support; rational residues then force positive integer masses. The factorization conclusion already appears in the cited literature.

Four moment and support lemmas pass Lean with only standard foundational axioms. The analytic representation and complete factorization proof remain written proofs. This closes the distinction between real-exponent and polynomial relaxations, but it does not bound the signs of moving head-score tangent spaces. The selected asymptotic target remains unproved.

## Explicit hyperbolic polynomial tangents realize every Boolean table

The [hyperbolic tangent construction](hyperbolic-boolean-tangents.md) starts from a fixed product of separated Lorentz quadratics, with one linear factor in odd degree. Homogeneous Boolean interpolation perturbs this polynomial in every Boolean direction. Explicit root brackets show that the uniform radius $1/(2(16n)^n)$ preserves strict hyperbolicity; a coefficient bound also preserves strict positivity of every coefficient. The positive orthant stays in the hyperbolicity cone, so the perturbed polynomials remain real stable. Their logarithmic variations at the fixed degree $n$ baseline have every Boolean sign table.

Nine interpolation and root-bracketing lemmas pass Lean. Exact arithmetic checks 4,158 endpoint estimates and 126 budget inequalities. The multivariate theorem is a complete written proof. This closes a different relaxation from the nonpolynomial real-exponent construction: polynomiality, homogeneity, positive coefficients, and hyperbolicity together still do not retain the linear-factor restriction. It supplies no attention-head representation and no asymptotic lower bound.

## Mixed binary coordinate fibers retain full parameter rank

The [integer binary-fiber construction](integer-binary-fibers.md) gives, for every $n\geq18$, an admissible positive-denominator three-head score with $6n$ selected binary values and an invertible square evaluation Jacobian. Exactly one selected value is negative. An explicit eighteen-bit certificate supplies the base case; a six-row nonsingular minor permits coordinate cloning. Independent rational arithmetic checks every selected value and inverse identities modulo two primes. Lean checks the finite scores and both rational Jacobian determinants with only the standard foundational axioms.

The same certificate fails the proposed minimum condition in two exact ways. Its unique signed multiplier vector has 57 positive and 51 negative coordinates, and a specified cube vertex has score $-7/30$. Thus it is neither a selected-constraint numerator-norm minimum nor a full-cube unit-margin representation. The rank-defect shortcut is disproved, while the more restrictive optimality route remains blocked. Numerical searches are not used as impossibility evidence. The manuscript's definitions and the asymptotic target remain unchanged.

## One additional head gives unit margin at the origin

The [origin repair construction](origin-margin-repair.md) starts from an arbitrary exact-model representation, strictifies it, and adds one explicit reciprocal head. It sets the origin score to its signed label and gives signed margin greater than three halves at every other vertex. The new denominator has strictly positive coherent coefficients. `OriginMarginRepair.computable_origin_margin_repair` kernel checks the complete construction from the original computability hypothesis, with no bounded-parameter or original-margin assumption.

The one-head singleton obstruction shows that keeping the head count unchanged is not always possible: the label that is negative only at the all-one vertex is already a counterexample. The additive overhead of one is harmless for the asymptotic target. This repairs the normalization step of the unit-margin approach but does not prove its missing sign-counting or minimum-counting theorem.

## Full-cube unit margins and active rank

The [rescaled integer construction](full-cube-unit-rank.md) preserves the arithmetic zero layer and activates the nearest negative level. It gives three heads on eighteen bits with origin value one, unit signed margin at every cube vertex, and 108 independent active parameter gradients. The complete integer cube inequality and the rank certificate pass Lean. An independent Gray-code verifier checks all 262,144 margins and two modular determinants.

The same point admits an explicit rational numerator descent that preserves every cube margin. The verifier checks the perturbed full table and the strict norm decrease exactly; the intervening feasible segment follows from linearity in the numerator coefficients. Thus full-cube unit margins alone do not force rank defect, while this example still does not refute a theorem specifically about canonical minima. That minimum theorem and the selected asymptotic lower bound remain unproved.

## Exponential priority-list separation by covering subcubes

A new compiler audit uses all faces of the cube rather than a single restriction. Every parity sign score has a positive alternating sum on every face. Each literal conjunction contributes on exactly two choices per coordinate, yielding the classical three-halves exponential lower bound of Basu, Bhatnagar, Gopalan, and Lipton, Theorem 6.5. The subcube-cover proof is now complete in Lean. Expanding coordinate priority lists into prefix conjunctions gives an exponential list lower bound, while exact attention parity complexity is linear. This rules out any polynomial-size priority-list compiler, including one with a free affine score. Both list orientations and repeated literal tests are handled in the written argument. See [the complete audit](parity-priority-separation.md). The classical conjunction theorem is credited to its authors; this is not the requested attention lower bound.

## A strict local minimum with full-cube unit margins and full active rank

Constraint generation, initialized by exact convex numerator optimization, produced a new eighteen-variable, three-head candidate. A separate exact integer certificate now places a genuine root of its 108 active equations in a rational box of radius one divided by ten to the fortieth power. Every unselected cube constraint has an independently checked gap. The active Jacobian is invertible, and the numerator-norm multipliers are all strictly positive. A contraction argument and local slack coordinates give a complete proof of strict local minimality for all cube constraints. See [the proof and certificate](unit-margin-strict-minimum.md).

This materially strengthens the earlier rank obstruction: requiring an interior local minimum does not restore rank defect. The construction does not certify global minimality or bound how many minima exist. Those alternatives remain theorem-strength gaps; the main asymptotic target is unchanged and unproved. The certificate is not based on the optimizer's success flag or on rounded singular values.

An additional kernel audit now checks the entire rounded Jacobian, inverse-residual row sums, and positive multiplier inequalities. The generic closed-ball contraction theorem and a separate first-order strict-minimum theorem also pass Lean. The latter uses the vanishing derivative of the objective minus the multiplier-weighted slacks and gives a positive lower bound proportional to the distance from the root. The concrete derivative and norm-estimate instantiation has now been assembled in Lean as `HeadComplexity.UnitMinimumAnalytic.exists_full_cube_strict_minimum`. A separate checked bridge identifies the cube enumeration and realizes the same score by three heads with shared embeddings. The complete concrete result uses only standard foundational axioms. It concerns a strict local minimum in the reduced coefficient coordinates, and no full asymptotic head theorem is inferred.
