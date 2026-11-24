# Beyond the Counting Bound

## Target and proof standard

Prove that the sequence $n^2W(n)/2^n$ is unbounded for the unchanged model in the attached `version-5.tex`.

$$ \forall C\gt0\qquad \forall n_0\qquad \exists n\geq n_0\qquad \exists f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace,\qquad H^{\ast}(f)\gt C\frac{2^n}{n^2}. $$

The desired conclusion is not an assumption in any argument. Denominators may depend on the target. Neither fixed-denominator dimension bounds nor exact real-table dimension bounds establish this Boolean sign-representation statement.

The source and start time are recorded in `run.json`. The attachment is outside this repository and is not modified.

## Global numerator norm audit

The [boundary-escape theorem](global-numerator-norm-obstructions.md) constructs an admissible negative-slope head with bounded normalized numerator norm on which any nonzero linear functional away from the origin is arbitrarily large. Thus every ordinary numerator-norm Lagrangian with a nonzero constraint multiplier away from the origin has infimum negative infinity. The same note gives a two-head family with full-cube unit margins and numerator norm tending to zero, although zero norm is infeasible. Both constructions and their actual fractional atoms are Lean checked. Global norm attainment and a nontrivial ordinary global norm-duality certificate are therefore unavailable without additional hypotheses. This does not exclude the separate strict local minimum, and does not improve the worst-case head lower bound.

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

## Positive functionals can have two strict normalized maxima

The [common-normal certificate](common-normal-maxima.md) gives two distinct nondegenerate strict local maxima of one positive linear functional on the entire normalized affine-head table image. It uses four input bits, strictly positive denominator slopes, and strictly positive table entries. A swap-invariant common normal solves the stationarity equations at both points, and an exact rational Hessian factorization proves positive definiteness of the corresponding least-squares Hessians. A rational inverse from origin, singleton, and pair entries verifies that these are distinct regular image points. The finite identities and real positive definiteness are Lean checked; the sphere restriction and local calculus deduction are written explicitly.

This closes the uniqueness shortcut left open by the earlier family of saddles. It does not supply many Boolean labels, classification complementarity, or an asymptotic maximum count. Both tables classify every cube input positively. No inference toward the requested lower bound is drawn from this finite obstruction.

The [permutation-orbit refinement](symmetry-orbit-maxima.md) gives six distinct nondegenerate strict maxima on six input bits. An exact full 13-parameter Hessian certificate and a three-coordinate symmetric functional produce all six points at once. A constant translation of both target and head tables makes the functional coefficients and all six tables positive, preserving the squared-distance objective. The finite identities and positive definiteness are Lean checked; the normalized-image calculus is written explicitly. A numerical 24-point candidate failed exact stationarity correction and was rejected. No growing asymptotic count or head lower bound follows.

## Elliptic normalization identity and its exact limitation

The [elliptic identity](head-elliptic-energy.md) gives a different denominator-parameter invariant. A normalized full head table satisfies an elliptic equation with a nonnegative potential bounded strictly below one quarter, independently of dimension and conditioning. The bound comes from an exact ellipsoid identity for normalized Boolean subset vectors. Nine algebraic declarations pass Lean, and 56 independent rational replays check the differential formulas on 2,032 cube entries.

The same calculation holds with an arbitrary fixed numerator table. Choosing that table to be any desired Boolean labeling times one fixed positive denominator realizes every sign pattern in this relaxed family. Thus the elliptic equation and potential bound alone cannot yield a sign restriction. An argument retaining the affine-numerator constraint under sums of heads is missing. The PDE-only approach is blocked by this explicit counterexample, not reopened as an unproved claim about the number of maxima.

## Independent denominator energy diverges under cancellation

The [two-head cancellation theorem](cancellation-energy.md) retains the affine-numerator restriction and tests composition of the new elliptic identity. A fixed two-bit function has exact head complexity two, yet its displayed family of admissible minimal-head representations has normalized block potential at least $1/(1024t^2)$ for every $0\lt t\leq1$. Both denominator orientations are positive. An exact squared-minor identity gives the lower bound; it is not inferred from numerical condition estimates.

The score table, strict signs, affine exclusion, norm bounds, and general unbounded angular-energy theorem pass Lean. A separate rational verifier checks the full first and second differential equations in 100 instances. The analytic interpretation is written explicitly. This disproves a uniform potential bound for independent denominator blocks even at minimal head count. It does not exclude a different representation or metric with controlled energy, and it gives no asymptotic sign count. Any such selection or geometric theorem remains a substantive missing mechanism.

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


## Uniform bounded-head covers and a quantitative margin barrier

The [clipped adjacent-ratio construction](luce-covering.md) approximates a positive-weight choice table simultaneously on every subset, even with unrestricted weight ratios. Expressing a bounded affine-ratio table using its origin and singleton values gives a cover with logarithmic size of order $n\log(n/\epsilon)$. Four algebraic ingredients pass Lean, and independent exact arithmetic checks 1,716 menus and 56 head identities and error bounds. The finite covering construction and counting deductions are complete written proofs.

For representations with margin at least $\gamma$ times the sum of individual head amplitudes and the bias magnitude, the resulting sign-count logarithm is at most $C(n+1)(H+1)\log(C(n+1)/\gamma)$. This would yield intermediate exponents under a subexponentially small margin guarantee. The guarantee is not part of the exact model. Moreover, Sherstov's halfspaces show that repairing even one-head classifiers to margin $\exp(-n^\beta)$ can require $\Omega(n^{1-\beta})$ heads. This blocks the proposed cheap uniform repair. No unrestricted exponent improvement is inferred. A recent all-menu multinomial-logit learning paper is cited for context, with its different oracle and guarantee stated explicitly.


## Exact reciprocal mean value blocks every subexponential margin repair

The [parity amplitude theorem](head-parity-amplitude.md) supplies a new exact identity. The full alternating sum of a positive affine ratio equals its value at a denominator-minimizing cube corner minus its value at an explicit point of the continuous cube. Reciprocal inclusion-exclusion moments determine that point and prove that it stays in the cube. Hence the unnormalized alternating sum of any amplitude-one head has absolute value at most two, a sharp constant. The identity, moment positivity, and both exact-atom denominator orientations pass Lean.

For any finite head count, the resulting parity score has relative margin at most $2^{1-n}$ when normalized by the sum of head amplitudes and bias magnitude. `HeadComplexity.HeadParityAmplitude.parity_relative_margin_bound` proves this for the manuscript's actual atoms. Consequently the proposed margin $\exp(-n^\beta)$ for $0\lt\beta\lt1$ is impossible for parity, even if the repair may use arbitrarily many heads. The margin-transfer route is now refuted, not merely missing a lemma. This does not contradict parity's linear head complexity and does not prove the selected worst-case target.

## November threshold-circuit restriction result does not transfer

[Reitwießner, Improved Bounds for Depth-Two Threshold Circuits Computing Andreev's Function, November 22, 2026](https://eccc.weizmann.ac.il/report/2026/330/download/) uses the fact that a fixed circuit's surviving threshold gates retain their weights under restrictions, and exploits constancy of sign-coherent Boolean gates on many prefix cubes. Its Lemma 11 counts varying thresholds with weights fixed before drawing the random lookup table. The manuscript permits target-dependent parameters, so those quantifiers cannot be interchanged.

There is also an explicit failure of the restriction step for real head outputs. The admissible reciprocal $1/(1+\sum_i x_i)$ varies on every prefix cube with a live coordinate. Its sign is constant, but subtracting three quarters already gives opposite labels at an all-zero vertex and a one-hot vertex. Thus discarding heads merely because their own signs are constant does not preserve the sum's labels. Neither the cited threshold-gate count nor its gate-survival estimate applies to these rational scores without a new representation theorem. No such theorem is asserted.

## Small integer pole matching refinement

The [pole-matching proof](pole-matching-fibers.md) now has an alternative using two base digits instead of the Chinese remainder theorem. All selector slopes are at most the square of the head count. A polynomial root-count argument distinguishes different pole sets using twice as many integer address samples as heads. The sample separation, matching injection, slice invariance, and factorial family cardinality pass Lean. Independent rational arithmetic verifies 648 distinct full tables, 40,288 table values, and 158,336 literal atom evaluations.

This refines the earlier restricted-family theorem. It does not assert that the corresponding unrestricted parameter fibers are finite or disconnected. The branch count remains insufficient to settle the critical-width sign count, and the refined constant-residue scores are positive everywhere.

## Formal polynomial identities do not control Boolean cancellation

[Saxena and Seshadhri's depth-three rank theorem](https://www.cse.iitk.ac.in/users/nitin/papers/rank-bound.pdf) concerns simple minimal formal polynomial identities, with a bound depending on the top fan-in. [Forbes, Kumar, and Saptharishi](https://drops.dagstuhl.de/storage/00lipics/lipics-vol050-ccc2016/LIPIcs.CCC.2016.33/LIPIcs.CCC.2016.33.pdf) explicitly distinguish equality on the Boolean cube from formal polynomial equality, and prove functional lower bounds for specified arithmetic circuit classes. Neither theorem counts unrestricted real signs of affine-ratio sums.

There is a direct exact-model reason not to substitute formal identities for Boolean cancellation. For $n\geq1$, put $t=\sum_i x_i$ and

$$ R_n(t)=\frac{\prod_{r=0}^{n}(t-r)}{\prod_{j=1}^{n+1}(t+j)}=1+\sum_{j=1}^{n+1}\frac{c_j}{t+j},\qquad c_j=(-1)^{n+j}\frac{(n+j)!}{((j-1)!)^2(n+1-j)!}. $$

The coefficients are the residues at the distinct poles $-j$, so partial fractions proves the identity. Every denominator has positive constant and positive coherent slopes, hence each summand is an admissible head. The score is zero on the entire Boolean cube, although it is nonzero at $t=1/2$. All residues are nonzero and all poles are distinct. Thus full-cube cancellation need not arise from a formal rational identity or coincident denominators. This example has one shared affine statistic; it does not refute every possible classification of cancellations.

Moreover, a rank estimate polynomial in the number of summands exceeds the ambient input dimension at the exponential head counts relevant here. A stronger sign-sensitive statement would still be needed even if the Boolean-identity issue were repaired. The proposed transfer is blocked at those two precise steps, and gives no intermediate exponent.

## Full table normalization does not bound all critical points

The [Gram-metric construction](full-table-critical-points.md) closes a specific gap in the earlier projective critical-point audit. It normalizes the whole zero-origin head table in Euclidean norm. One fixed linear functional has exponentially many distinct nondegenerate critical image points, with logarithmic count quadratic in the input dimension. A common rational amplitude vector avoids explicitly listed linear degeneracies. A single rescaled analytic system has a displayed block diagonal invertible limiting Jacobian, so the proof does not assume independent compatibility of a grid of derivative data.

Five algebraic ingredients pass Lean. Exact rational arithmetic checks 654 limiting systems. A separate directed dyadic interval verifier certifies all nine perturbed roots in the five-bit example, using a specified rational scale, invertible Jacobians, positive coefficients, and disjoint image-ratio intervals. The general family theorem has a complete written analytic proof, not an additional Lean declaration.

This rules out another uniform small count of all critical points. It does not establish a large count of classification minima, and all the scores obtained after adding bias two are positive. No sign-counting theorem or asymptotic head-count improvement follows.

The subsequent Hessian audit sharpens this limitation. Completing the square in the Gram inverse gives local coordinates in which the limiting scaled energy Hessian has a positive definite anchor block and an explicit signed diagonal data block. Adding the negative numerator-sphere block proves that every point in the constructed general family is a saddle. For the nine specified roots, a separate interval second-derivative calculation certifies an actual positive anchor direction. Consequently this family does not refute a count restricted to local maxima. Such a classification-relevant count remains unproved, not an implicit consequence of the critical-point construction.

## Typical labels also prohibit the proposed margin repair

The [typical-label amplitude theorem](typical-label-amplitude.md) applies dyadic chaining to the previously proved conditioning-independent cover of bounded head tables. With probability at least one minus the reciprocal of the input dimension, a random label table has absolute normalized correlation at most a constant times the square root of the input dimension times its logarithm divided by the cube size, simultaneously with every amplitude-one head. A single such event controls every finite signed sum of heads by linearity, including all target-dependent denominators and both coherent orientations.

Consequently almost every Boolean function requires exponentially small relative amplitude margin in every finite representation. This closes a possible repair that would have excluded parity as exceptional: restricting the proposed subexponential margin guarantee to typical targets does not make it true. Twelve deterministic Lean declarations check the constant in the chaining sum, the limit transfer, and the finite-head correlation argument. The probability and covering deductions are complete written proofs. This is an amplitude obstruction, not a head-count lower bound; the selected target remains unproved.

## Continuation and the stronger target

The resumed run retains the original unrestricted model and also considers an eventual lower bound of constant times the cube size divided by the input dimension. Neither that stronger conclusion nor the original unbounded improvement over the counting bound has been proved. The previous phase's unfinished verification is not treated as a pass or a reason to terminate research.

The [24-point symmetry certificate](symmetry-orbit-four.md) now proves distinct strict local maxima for one positive functional on normalized seven-bit head tables. Its Lean check replaces expensive determinant permutation enumeration with an exact inverse. This finite result still supplies no asymptotic maximum count and all translated tables have the same Boolean labels.

## The bounded numerator polytope supplies harmonic feasible families

The [amplitude-polytope theorem](amplitude-polytope-maximum.md) gives an explicit Minkowski decomposition of every fixed-denominator amplitude ball. Its extreme numerator branches solve one elliptic equation with no zeroth-order term. A direct analytic maximum principle proves that nonconstant positive-slope tables cannot be strict local maxima of linear functionals on the bounded table image. A stronger statement excludes even nonstrict maxima when the functional is nonzero at all singleton and pair vertices.

This does not justify deforming a classification representation to the parameter boundary. Four displayed harmonic inequalities enclose a bounded common positive chamber, and classification multipliers need not satisfy the genericity condition. The simultaneous-inequality transfer remains blocked. Six Lean declarations check the algebraic ingredients; the full geometric statements have written proofs.

## Boolean projection cancellation and high contact

The [Boolean-line ideal theorem](boolean-projection-cancellation.md) classifies all integer-velocity, constant-residue reciprocal identities that persist throughout a denominator deformation. It gives explicit six-point switching generators and a monomial reduction proof, informed by algebraic discrete tomography. An independent finite-difference construction has arbitrarily high contact while its denominator velocity vectors have full affine span.

These results address actual cube cancellation rather than substituting formal polynomial identities. They still do not bound the number of translated switching generators needed, handle arbitrary affine residues at one target-dependent parameter point, or count classification chambers. Those steps remain missing; no intermediate exponent or matching lower order is claimed. Nine Lean declarations verify the six-point mechanism, while the general ideal and moment-curve theorems are complete written proofs.

## Exact bounded-head convex hull

The [priority convex-hull theorem](priority-convex-hull.md) gives a global finite elimination identity and proves that the closed convex hull of all bounded admissible heads is exactly the convex hull of positive and negative coordinate priority tables. It yields an exact dual support formula, a sharp parity supremum, and a direct random-label correlation bound. Thirteen Lean declarations include the finite induction and priority-gate closure.

This does not give a head-count compiler. A displayed one-head reciprocal curve avoids every affine span of at most the cube size many dictionary points for a suitable explicit finite-search parameter. The resulting single head requires the maximum possible number of convex atoms, one more than the cube size. An exact two-bit example needs five atoms. Convexification therefore loses head count even for a single strictly positive head; a sign-pattern count before convexification remains missing.

## Affine projection modules and circulation circuits

The [affine-numerator extension](affine-projection-module.md) classifies all integer-velocity reciprocal deformation identities with arbitrary affine residues. Its kernel module has linear generators and an explicit terminating tagged-monomial normal form. This closes the numerator restriction for that deformation theorem, but gives no economical decomposition in the original number of heads and does not classify arbitrary fixed-parameter representations.

A separate exact graph theorem identifies a family of persistent reciprocal relations with graph circulations. Directed cycles yield minimal identities with growing affine span. Their formal squares form circuits, while their formal cubes are independent; every Boolean power still satisfies the circulation identity. This gives a concrete obstruction to importing the recent Schur-product bound for formal power circuits by assuming that minimal Boolean cancellation is formal cancellation. The missing multiplication-compatible Boolean space remains a substantive gap.

## Minimal moment circuits can have near-maximal contact

The [moment-circuit surgery theorem](moment-circuit-surgery.md) strengthens the contact obstruction to growing dimension. Repeated six-point substitutions and an explicit polynomial separating functional preserve a one-dimensional full-support truncated-moment kernel, while increasing the velocity span. The resulting positive integer configuration has contact order equal to its head count minus a term linear in the input dimension, full affine span, and no persistent reciprocal identity. Eight Lean declarations check the local switch, moment equations, and outside-span coefficient step; the general induction has a complete written proof.

This still does not address minimal Boolean representations. The score is exactly equivalent to its original diagonal family, has constant sign away from the origin, and at a fixed deformation parameter can be interpolated with at most one more head than the number of inputs. Any repaired contact route must therefore control complexity after such functional equivalences, not merely remove linear subidentities. No such complexity theorem or unrestricted sign-count estimate is asserted.

The ridge-function literature provides related fixed-direction interpolation and closed-path language. [Pinkus on polynomial ridge functions](https://www.cambridge.org/core/books/abs/ridge-functions/polynomial-ridge-functions/9F16FF8D15239524F01DDB6ADCC97320) studies spans of powers indexed by directions; [Akhmedov and Ismailov](https://arxiv.org/abs/2408.06443) study straight-line interpolation with fixed ridge directions. These settings do not supply a sign count for sums with adaptive denominators and a fixed reciprocal profile.

## Elliptic circuits survive the collinear-replacement audit

The [ellipse construction](ellipse-moment-circuits.md) has minimal truncated-moment support, no persistent identity, and no collinear constant-residue representation of the same persistent projection data. Its exact dimension formula comes from one missing trigonometric harmonic at every frequency divisible by three. This gives arbitrary-degree Boolean moment circuits smaller than the sharp formal-power circuit bound. A seven-point positive rational instance has ten kernel-checked declarations, including its moments and exact matrix inverses. The general dimension and existence arguments have complete written proofs.

This strengthens the obstruction to that precise formal-to-Boolean transfer. It does not rule out every weaker contact estimate, and it does not address arbitrary affine numerators at a fixed target-dependent parameter point. Neither asymptotic target follows.

## Minimum normalized denominator energy is zero at one extra head

The [sign-preserving spike theorem](vanishing-energy-spike.md) starts from any strict admissible representation, scales it down, and adds one reciprocal head concentrated at the origin. Every target label remains unchanged while the normalized independent-block denominator energy tends to zero. This includes target-dependent original denominators, both coherent orientations, and arbitrary signed cancellation. The proof gives an explicit quadratic energy bound in the scale parameter.

Fourteen general algebraic declarations pass Lean, including realization of the added term as an actual fractional atom and the entire finite-head assembly with strict signs. An independent rational audit checks 840 deformed representations, 6,540 label inequalities, 6,540 spike energy identities, and 7,248 angular projection identities. The differentiation and identification of the original gradient constant have complete written proofs. This resolves a specific representative-selection question about the energy infimum; it provides no head-count lower bound. The original target and the stronger order target remain unproved.

## A fixed-architecture transformer bound does not control growing head count

[Dooley and coauthors, September 2026](https://arxiv.org/html/2609.31999v1), prove a polynomial VC bound in input length for a fixed untrained transformer. Their definition fixes the number of heads, layers, and hidden dimension before the asymptotic statement, and their constants may depend on that architecture. Thus their stated input-length bound cannot be substituted as a uniform bound when the number of heads grows exponentially with input length. Their component-count method still requires a bound for all regular parameter fibers, which is precisely where the existing unrestricted route lacks an adequate estimate.

[Ashtiani and coauthors' Gaussian-mixture compression result](https://papers.nips.cc/paper/2018/file/70ece1e1e0931919438fcfc6bd5f199c-Paper.pdf) concerns approximation in total variation. It does not imply preservation of a comparison's sign at every cube input. The spike construction above gives a concrete reason that a small approximation error or small normalized energy need not control exact signs: arbitrarily small coordinates retain arbitrary labels. No margin-independent sign transfer or head-count theorem is obtained from that result.

## Full single-head linear fibers can have quadratically exponential multiplicity

The [full-head fiber construction](full-head-linear-fibers.md) removes the fixed-anchor and fixed-numerator restrictions from a prior section-complexity obstruction. Singleton and pair observations on a connected odd-cycle graph give an invertible anchor Jacobian. Two rational interpolation observations per remaining coordinate then produce many simple roots while independently fixing numerator coefficients. The resulting square observation system has isolated regular points in the full normalized head-coordinate domain, with distinct complete positive tables.

The general count has logarithm quadratic in the input dimension. Eight Lean declarations check the local algebra and a six-bit certificate; exact rational arithmetic verifies all 343 tables in that certificate. The general interpolation and inverse-function arguments have complete written proofs. This refutes a broad linear-observation fiber bound, not a bound for the coordinate sign predicates. It supplies no lower bound for unrestricted Boolean head complexity; both requested asymptotic targets remain unproved.
