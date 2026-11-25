# Exact unit margin is not attained for nonconstant tables

## Statement and proof status

In the original unrestricted atom model, no nonconstant truth table on $n\geq2$ bits has a finite-width representation of relative margin exactly one. Nevertheless, the literal table $f(x)=2x_0-1$ has supremum relative margin one at every fixed positive width. Thus a best-margin representation need not exist, even for a literal.

The triangle-equality reduction from arbitrary width to one genuine head is kernel checked in [`MarginOneCollapse.lean`](../../formalization/HeadComplexity/Research/MarginOneCollapse.lean), especially `HeadComplexity.MarginOneCollapse.hasRelativeMargin_one_head`. The classification of two-valued original heads below is an independently audited written proof. Consequently the theorem for every nonconstant table remains written, rather than a Lean declaration.

For literals, the entire nonattainment conclusion is now kernel checked in [`LiteralMarginNonattainment.lean`](../../formalization/HeadComplexity/Research/LiteralMarginNonattainment.lean). The exact declaration `HeadComplexity.LiteralMarginNonattainment.hasRelativeMargin_iff_lt_one` states that, in dimension `n+2` and at any fixed positive width, a relative-margin threshold is achievable exactly when it is strictly below one. The genuine approximations are checked in [`LiteralMarginNonattainmentWitness.lean`](../../formalization/HeadComplexity/Research/LiteralMarginNonattainmentWitness.lean), with `HeadComplexity.LiteralMarginNonattainmentWitness.literal_margin` and `hasRelativeMargin_below_one`. The witness file indexes positive input dimension as `n+1`; the note uses $n$ directly.

Throughout, the denominator is strictly positive on the entire Boolean cube, all original attention weights are strictly positive, and relative margin uses the full-cube head suprema. Arbitrary signed coefficients, bias, and cancellation remain allowed.

## A two-valued original head must be constant

Subtracting a constant preserves genuine admissibility: subtract $c\gamma$ from $\eta$ and $c$ from every $m_i$. Thus any two distinct output levels can be centered into opposite values. Suppose a genuine original head $\phi=A/B$ takes values in $\lbrace-M,M\rbrace$, with $M\gt0$, and both values occur. Set $z_i=2x_i-1$ and write the affine numerator and denominator as

$$ A(z)=a_0+\sum_i a_i z_i,\qquad B(z)=b_0+\sum_i b_i z_i. $$

The original `FracAtom` parameters satisfy

$$ b_i=\frac{\rho_i(\alpha-1)}2,\qquad a_i=\frac{\rho_i\bigl(\alpha(m_i+\delta)-m_i\bigr)}2,\qquad \rho_i\gt0,\quad\alpha\gt0. $$

Let expectation be uniform over the cube. Since $B$ is positive and each sign occurs,

$$ |a_0|=|\mathbb E A|=M|\mathbb E(fB)|\lt M\mathbb E B=M b_0. $$

Here $f=\phi/M$ takes values $-1,+1$. Both positive quantities $\mathbb E[B\mathbf1 _{f=1}]$ and $\mathbb E[B\mathbf1 _{f=-1}]$ are nonzero, which proves the strict inequality without any cancellation assumption.

The identity $A^2=M^2B^2$ holds at every cube vertex. Comparing its linear and quadratic Fourier coefficients gives

$$ a_0a_i=M^2b_0b_i,\qquad a_i a_j=M^2b_i b_j\quad(i\neq j). $$

If $\alpha\neq1$, every $b_i$ is nonzero. The linear identities force $a_0\neq0$ and give $a_i=M^2b_0b_i/a_0$. Substituting in a quadratic identity for two distinct coordinates yields

$$ M^2b_i b_j\left(\frac{M^2b_0^2}{a_0^2}-1\right)=0. $$

This is impossible: the first factor is nonzero, while the parenthesized factor is positive by $|a_0|\lt Mb_0$.

If $\alpha=1$, all $b_i$ vanish, and the original parameter restriction becomes $a_i=\delta\rho_i/2$. The quadratic identities give $a_i a_j=0$ for distinct coordinates. Since $n\geq2$ and all $\rho_i$ are positive, this forces $\delta=0$. Both affine forms are then constant, contradicting the occurrence of both signs.

Thus no genuine original head on at least two bits is a nonconstant exactly two-valued function. In particular, a constant denominator does not permit arbitrary affine numerators in the original model: at $\alpha=1$, all numerator slopes share the factor $\delta$ and positive weights $\rho_i$. Ignoring this restriction would invalidate the conclusion. $\blacksquare$

## Collapse of a unit-margin sum

For a strict score $S=b+\sum_h\phi_h$, put $A_\mathrm{tot}=|b|+\sum_h\|\phi_h\|_\infty\gt0$. The full-cube triangle inequality gives

$$ f(x)S(x)\leq |b|+\sum_h\|\phi_h\|_\infty=A_\mathrm{tot}. $$

If relative margin is one, equality holds at every vertex. Every summand of the triangle-inequality deficit is nonnegative, so each deficit vanishes separately:

$$ f(x)b=|b|,\qquad f(x)\phi_h(x)=\|\phi_h\|_\infty\quad\text{for every }h,x. $$

A nonconstant table has both signs, hence $b=0$. Positive total amplitude supplies a head with positive norm. That head is exactly a positive multiple of the entire signed truth table, contradicting the two-valued classification when $n\geq2$.

This argument allows arbitrary width and arbitrary cancellation. Its triangle-equality portion is exactly the kernel-checked theorem cited above. The classification is the additional written step. $\blacksquare$

## A literal approaches the unattained supremum

Fix $n\geq2$ and $\varepsilon\gt0$. The affine ratio

$$ \phi_\varepsilon(x)=\frac{2x_0-1}{1+\varepsilon\sum_{i=0}^{n-1}x_i} $$

is a genuine original head. Its denominator has positive intercept and strictly positive slopes, so the existing `FracAtom.ofPositiveAffineRatio` constructor applies. One explicit parameter choice, with the attention constant denoted by $\gamma_\mathrm{att}$, is

$$ \alpha=1+2n\varepsilon,\qquad\rho_i=\frac1{2n},\qquad\gamma_\mathrm{att}=\frac12,\qquad\delta=0,\qquad m_0=\frac2\varepsilon,\qquad m_i=0\quad(i\neq0),\qquad\eta=-1-\frac1{n\varepsilon}. $$

Direct substitution gives exactly the displayed numerator and denominator. All parameters required to be positive are positive. For the literal $f(x)=2x_0-1$ and zero bias,

$$ \|\phi_\varepsilon\|_\infty=1,\qquad \min_x f(x)\phi_\varepsilon(x)=\frac1{1+n\varepsilon},\qquad \mathrm{margin}(f,\phi_\varepsilon,0)=\frac1{1+n\varepsilon}. $$

The all-zero vertex attains the norm; the all-one vertex attains the minimum signed score. Padding with zero-valued genuine heads preserves the margin at every fixed width $H\geq1$. As $\varepsilon\to0^+$ these margins approach one, while the preceding theorem excludes attaining one at any finite width. Hence the supremum is one and no maximum exists.

For one input bit the classification changes: an exact two-valued literal head is admissible. Constant truth tables can attain margin one in every dimension using bias alone. Neither exception affects the nonattainment statement for nonconstant literals on at least two bits.

## The endpoint in positive normal form

The kernel-checked declaration `HeadComplexity.PositiveLiteralNonattainment.relativeMargin_lt_third` in [`PositiveLiteralNonattainment.lean`](../../formalization/HeadComplexity/Research/PositiveLiteralNonattainment.lean) strengthens the canonical endpoint restriction for literals on at least two bits. At every finite width, a strict literal representation by nonnegative genuine heads and bias $-1$ has relative margin strictly below $1/3$. No minimum-zero or amplitude-budget hypothesis is required. The declaration `not_hasNormalizedMargin_third` states the corresponding exclusion for the positive normal-form predicate.

The proof first shows that margin at least $1/3$ would force the sum of head suprema to equal two. Translating each head by minus half its supremum then preserves the score with zero bias and leaves total amplitude at most one. This would yield an original literal certificate of margin at least one, contradicting the kernel-checked theorem above.

## Scope for the lower-bound program

This refutes an unconditional premise that an optimal relative-margin representation always exists at a fixed positive width in the original open parameter domain. An optimization argument must justify attainment, use a compactified class with separately controlled limits, or work with approximate maximizers.

In the compact closure of amplitude-one tuples of full-cube head values and bias, a best margin does exist by continuity. If this compactified optimum is positive, genuine heads of the same width approximate it with arbitrarily small loss. This is a written compactness argument, detailed in [normalized_head_boundary_faces.md](normalized_head_boundary_faces.md#a-best-margin-exists-in-the-compact-closure). It supplies no numerical lower bound on the optimum and no justification for applying interior stationarity identities at boundary maximizers.

It does not refute the required small-margin repair: these literals already have same-width representations at every prescribed margin strictly below one. It also does not supply a larger unrestricted lower bound for `HeadComplexity.worstCaseHeadComplexity`.
