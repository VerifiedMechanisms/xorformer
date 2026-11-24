# Sparse projection circuits with exponentially large primitive coefficients

## Statement

For every integer $k\geq1$, there is an integer signed measure $\mu_k$ on the plane with the following properties:

1. Its support has $H_k=9k+2$ distinct points.

2. Its projections onto the first coordinate, the second coordinate, and their sum all vanish identically as signed measures.

3. Every signed measure on the same support with these three vanishing projections is a scalar multiple of $\mu_k$.

4. Its primitive integer coefficients include one of magnitude one, have maximum magnitude $2^k$, and have total absolute mass $10\cdot2^k-8$.

Thus every Boolean projection vanishes, for every scalar test function and every moment order. A common translation makes all support coordinates strictly positive without changing any of these facts.

The base circuit and its uniqueness are kernel checked in `HeadComplexity.WeightedProjectionCircuit`. The gluing induction proving this family is a written proof below. The script `verify_weighted_projection_circuit.py` checks the first twelve members with exact integer marginal arithmetic and rank certificates modulo the prime $65537$.

This family obstructs a sign-compatible surface-refinement shortcut. It does not obstruct sparse fillings with arbitrary signed coefficients: the same family has a decomposition into only $3k$ translated and scaled six-point ghosts.

## The eleven-point base circuit

The points and coefficients are:

| Point | Coefficient |
| --- | ---: |
| $(3,1)$ | $-1$ |
| $(2,1)$ | $-1$ |
| $(3,2)$ | $1$ |
| $(0,1)$ | $1$ |
| $(2,3)$ | $-1$ |
| $(0,2)$ | $-2$ |
| $(1,0)$ | $-1$ |
| $(0,3)$ | $1$ |
| $(2,0)$ | $1$ |
| $(2,2)$ | $1$ |
| $(1,1)$ | $1$ |

All three marginal sums vanish. Their simultaneous kernel is one-dimensional, and every coefficient is nonzero. The Lean declarations `scalar_kernel_identity`, `constant_residue_identity_unique`, and `no_proper_support_relation` check these statements for arbitrary real residues and arbitrary scalar test functions. The distinguished input point is $(3,2)$ with coefficient one; the output point is $(0,2)$ with coefficient minus two.

Equivalently, its generating polynomial factors as

$$ P(u,v)=(u-1)(v-1)(u-v)(uv+v-1). $$

This exact factorization expresses the base as three translated copies, with signed coefficients, of the standard six-point ghost $(u-1)(v-1)(u-v)$. The factorization is a written polynomial identity; the scalar-kernel identity is checked independently in Lean.

## Separated gluing preserves minimality

Suppose two minimal circuits have supports $S$ and $T$, meeting at exactly one point $p$. Suppose their projected coordinate sets meet only at the corresponding projection of $p$, separately for each of the three projections. Scale their coefficients so that the coefficients at $p$ cancel, and remove that point. The resulting relation is again a minimal circuit.

**Proof.** Let $\nu$ be any relation on $(S\cup T)\setminus\lbrace p\rbrace$. Restrict it to $S\setminus\lbrace p\rbrace$, obtaining $\nu_S$. Each marginal of $\nu_S$ is supported only at the projection of $p$, because all other projected values occur only on this side of the gluing. All three remaining marginal masses equal the same number $m$, the total mass of $\nu_S$. Therefore $\nu_S-m\delta_p$ is a relation on $S$ and is a scalar multiple of its unique circuit. The same reasoning on $T$ forces the second scalar, since the coefficients at $p$ must cancel. Hence $\nu$ is a scalar multiple of the glued relation. All displayed coefficients after removing $p$ remain nonzero. $\blacksquare$

The required separation is achieved by a sufficiently large integer dilation about the marked input point, followed by translation to the old output point. Every new projected value differs from that shared value by an integer multiple of the dilation factor. Taking the factor larger than twice the range of the old projected values excludes any additional overlap.

## Induction and coefficient growth

Start with the eleven-point circuit. At step $k$, its output coefficient is $-2^k$. Glue a new base circuit at its coefficient-one input, scaled by $2^k$, and remove the canceled shared atom. The next output coefficient is $-2^{k+1}$. An original coefficient of magnitude one survives every step, so the coefficient vector remains primitive.

Each gluing adds eleven points and removes the shared point from both supports. Consequently

$$ H_{k+1}=H_k+9,\qquad H_k=9k+2. $$

The total absolute mass satisfies

$$ M_{k+1}=M_k+12\cdot2^k-2\cdot2^k=M_k+10\cdot2^k,\qquad M_k=10\cdot2^k-8. $$

Separated gluing proves uniqueness at every stage. This proves all four stated properties. Translation preserves the marginal identities and uniqueness, so strict positivity of both coordinates can be imposed afterwards. $\blacksquare$

## The failed surface-refinement inequality

Consider a proposed sign-compatible refinement of a weighted marginal relation into closed oriented surfaces. Suppose each connected surface has a common real face weight, every face is labeled by one original support atom, and every occurrence of an atom has the sign of that atom's coefficient. Each nonempty connected component then induces a nonzero sign-compatible relation on the original support.

For $\mu_k$, minimality forces the integer face-multiplicity vector of each such component to be a positive scalar multiple of the primitive coefficient vector. Since one primitive coefficient has magnitude one, integrality makes this scalar a positive integer. Hence even one nonempty component requires at least

$$ 10\cdot2^k-8 $$

face occurrences. There can be no bound of the form $C H_k$ with an absolute constant $C$ for this sign-compatible refinement.

This identifies the first failing step in the naive interval-pairing argument. Pairing coefficients at individual marginal fibers does not guarantee that the resulting weighted pieces close into surfaces with only linearly many triangle copies. Unequal primitive ratios can force exponential propagation.

## Why this does not refute signed sparse filling

Each base circuit is a sum of three six-point ghosts by the displayed factorization. The construction uses $k$ translated and dilated base circuits with arbitrary signed real scaling. It therefore uses only $3k$ six-point generators, or $18k\lt2H_k$ atom occurrences before cancellations.

Thus the exponential coefficient mass does not imply large support cost when arbitrary signed coefficients and cancellations are retained. A general support-linear decomposition into unrestricted-displacement ghosts remains open. No truth table is made hard by these zero-score relations alone, and no margin-repair impossibility is inferred.

## Verification boundary

`WeightedProjectionCircuit.lean` checks five declarations for the base circuit. Their transitive axiom output is in `weighted-projection-circuit-axioms.txt`, with only `propext`, `Classical.choice`, and `Quot.sound`. The successful module build is in `weighted-projection-circuit-build.txt`.

The gluing proof for all $k$, the surface-refinement obstruction, and the three-generator factorization are written proofs. The twelve finite rank checks are computations, recorded in `weighted-projection-circuit-finite.json`; they are not substitutes for the induction and are not represented as kernel-checked declarations.
