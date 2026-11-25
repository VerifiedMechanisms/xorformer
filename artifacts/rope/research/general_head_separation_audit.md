# Independent Audit of the Arbitrary Head Separation

This note records an independent check of [Theorem 23](../../../theorems/03_rotary_attention/023_pure_rope_separation_every_head_count.md). The argument establishes a separation at every fixed head budget above two. The complete arbitrary-head separation is now Lean-checked in `PureGeneralSeparation.lean`, including the actual classifier, averaging, polynomial limit, physical coordinate, contraction rank, and compact frame steps.

## Source family and architectural constraints

For a fixed head count $H\geq3$, the construction has $H$ physical blocks with $2H$ coordinate groups each. The numerator coefficient sum in one block is $4H+2$, and its sum over all blocks is $B_H=4H^2+2H$. Each denominator direction has coefficient sum zero and absolute coefficient sum $2H$.

Substituting the specified masses into the pure scalar atom gives the numerator $N_i(q)$ and denominator $C_H+d_i(q)$ exactly. In particular, the self mass is $C_H-2B_H=12H^2-4H+20\gt0$, and every input mass is strictly positive. The two token values remain zero and one. Thus the construction respects the special numerator constraint; it does not rely on generic unrestricted affine fractions being pure atoms.

The established scalar-to-rotary bridge applies to every finite source dimension and head count. It supplies a common finite width, the fixed query token, shared token embeddings, standard fixed frequencies, and unrotated token-only values. No additive positional embeddings enter this application.

## Rank calculation

The source homogeneous polynomial is linear in the numerator variables, with denominator products of degree $H-1$. After contracting once along a vector with denominator component $d$, the coefficient of each numerator variable is a sum of products omitting two denominator indices.

For a second contraction with denominator component $e$, comparing numerator coefficients yields

$$ d_i e_j+d_j e_i=0\qquad(i\neq j). $$

For each pair, the comparison is available because there is a third index when $H\geq3$. Fixing an index where $d$ is nonzero shows that the possible $e$ form a space of dimension at most one. In the fiber $e=0$, the numerator component of the second contraction satisfies the same pair equations and also has dimension at most one. The contraction kernel therefore has dimension at most two, giving flattening rank at least $2H-2\gt H$.

This comparison legitimately uses polynomial derivatives to control the tensor kernel. If a flattened contraction annihilates a vector, evaluating its remaining arguments diagonally makes the corresponding second directional derivative zero. Characteristic zero ensures the normalization factor is nonzero. Only this implication is needed for the rank lower bound.

The physical block map is invertible by the displayed inverse in Theorem 23. The low-rank contraction locus is consequently exactly the paired-coordinate subspace, of dimension $H$, and that subspace contains the all-ones vector.

## Closed tensor obstruction

The cleared polynomial of an $H$-head vanilla score is a sum of $H$ terms, each with one affine numerator and the other $H-1$ affine denominators. Absorbing the free score constant into one numerator preserves this form. In the first block, the common denominator kernel has dimension at least $H$.

Contracting along this kernel leaves only terms in which the first block supplies the numerator. The second-block covectors then lie in the span of the $H$ denominator rows, so the contraction flattening has rank at most $H$.

The orientation condition used in the compactness argument is stronger than coordinatewise nonnegativity with optional zero entries: every nonconstant vanilla denominator has globally strict slope sign. Consequently its row in the first block is nonzero and has strict uniform sign. This remains true after summing slopes over replicas. A nonzero mixed tensor rules out the case in which every denominator is constant.

The orthonormal frame and normalized positive row have a common convergent subsequence. No head parameter is assumed bounded. Closedness of the rank condition places the limiting frame in the source denominator kernel; dimension equality makes it a basis of that kernel. The normalized row is perpendicular to it, contradicting its coordinate sum one because the kernel contains the all-ones vector.

## Finite grids, averaging, and sign rigidity

The normalized averaged polynomials live in a fixed finite-dimensional coefficient space, because both the group count and the degree bound are fixed once $H$ is fixed. A coefficient maximum of one prevents a zero limit. Moving grid points are valid here: bounded-degree coefficient convergence and convergence of the points imply convergence of evaluations.

The mixed coefficient uses exactly one group variable from each of the $H$ blocks. Any monomial of degree at most $H$ contributing to it must already use all those distinct groups once. Repeated-group terms cannot contribute. Therefore averaging preserves the literal factor-tensor formula with each linear slope replaced by its replica sum. A positive scalar coefficient normalization can be absorbed into all numerator rows without changing denominator orientation.

The source polynomial is primitive as a polynomial in the numerator variables over the denominator polynomial ring. Its numerator coefficients have greatest common divisor one. Over the denominator fraction field it is nonconstant linear and irreducible. Gauss's lemma therefore gives the required irreducibility before and after the invertible affine physical substitution.

The source zero set contains an open smooth real patch inside the cube. Weak sign matching makes the limiting polynomial vanish on that patch. Rational substitution and denominator clearing turn this local vanishing into a polynomial identity. Divisibility, followed by the degree bound, gives a nonzero scalar multiple; the signs force that scalar positive. This step also excludes every nonzero weak-sign representative of degree at most $H-1$.

## Quantifiers and conclusion

Each contradiction assumes infinitely many replication counts for a fixed $H$ and extracts a sequence tending to infinity. Thus each conclusion holds for all sufficiently large replication counts, rather than merely for one subsequence. Combining the two thresholds gives both exact pure minimum $H$ and vanilla minimum strictly greater than $H$ for the same family members.

The pure lower bound uses the separate compactness argument for degree at most $H-1$. It does not follow from the vanilla tensor obstruction alone. The writeup includes that necessary additional argument.

The resulting quantifiers are

$$ \forall H\geq3\ \exists m_0\ \forall m\geq m_0,\qquad H^{\ast}_{\mathrm{pure}}(f_{H,m})=H\quad\text{and}\quad H+1\leq H^{\ast}_{\mathrm{vanilla}}(f_{H,m})\leq2^H-2. $$

Together with the already proved zero-, one-, and two-head equivalences, this proves that the universal reverse implication holds exactly for budgets at most two. Exact invariance under adding unused input bits also gives a separating function at every sufficiently large input length for each fixed $H\geq3$.

No mathematical gap was found in this independent audit. The full Lean assembly is available in [PureGeneralSeparation.lean](../../../formalization/HeadComplexity/Results/PureGeneralSeparation.lean). Its theorem `eventually_complexity_separation_general` proves the displayed conclusion for every head count at least three, with no residual obstruction premise. Its theorem `eventually_not_vanilla_general` states the corresponding actual Boolean noncomputability result directly.

The formal compactness argument explicitly handles zero denominator matrices. An infinite zero-matrix subsequence would force every direction into the paired source kernel, which is impossible. Once these indices are excluded, each remaining oriented nonzero matrix supplies the positive normal needed for the frame contradiction. No lower bound on denominator slope magnitudes or bound on individual head parameters is assumed.
