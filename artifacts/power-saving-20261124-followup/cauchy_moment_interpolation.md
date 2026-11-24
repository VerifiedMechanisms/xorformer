# Exact reciprocal interpolation with ordinary moment cancellation

## Kernel-checked statement

Let $M\geq1$, let $t_1,\ldots,t_M$ be distinct positive real query values, and let $y_1,\ldots,y_M$ be arbitrary real scores. For any $D\geq0$ and any $M+D+1$ distinct positive poles $a_j$, there are real residues $c_j$ satisfying

$$ \sum_j c_j a_j^k=0\quad(0\leq k\leq D),\qquad \sum_j\frac{c_j}{t_i+a_j}=y_i\quad(1\leq i\leq M). $$

This is `HeadComplexity.CauchyMomentInterpolation.exists_residues` in `formalization/HeadComplexity/Research/CauchyMomentInterpolation.lean`.

The same module proves `exists_original_heads_with_moment_cancellation`. For every real score table on the full Boolean cube, there are exactly $2^n+D+1$ admissible original fractional heads, with a common strictly positive slope vector and positive denominator constants $b_j$, whose sum equals the score table exactly and whose constant numerator residues satisfy

$$ \sum_j c_j b_j^k=0\qquad(0\leq k\leq D). $$

The original head definitions are unchanged. Arbitrary signed residues are allowed. The theorem asserts exact scores, not a lower bound on relative margin.

## Proof

Write $L=M+D+1$ and $Q(t)=\prod_j(t+a_j)$. Interpolate the values $y_iQ(t_i)$ by a polynomial $P$ of degree at most $M-1$. Set

$$ c_j=\frac{P(-a_j)}{\prod_{h\neq j}(a_h-a_j)}. $$

Lagrange interpolation gives the partial fraction identity

$$ \frac{P(t)}{Q(t)}=\sum_j\frac{c_j}{t+a_j}. $$

For $k\leq D$, the polynomial $P(X)(-X)^k$ has degree at most $L-2$. Its coefficient of degree $L-1$, expressed by the same Lagrange weights, is $\sum_jc_ja_j^k$ and is zero. Thus all the stated moments vanish. Polynomial linearity also proves moment cancellation after any common translation of the poles.

For the original-model realization use the injective positive statistic

$$ t(x)=1+\sum_{i=0}^{n-1}2^i x_i. $$

The denominator of head $j$ is $1+a_j+\sum_i2^i x_i$, with constant numerator $c_j$. The existing positive-affine-ratio constructor supplies an admissible original head. Translating $a_j$ by $1$ gives the claimed moments of $b_j=1+a_j$.

## Scope of the obstruction

The all-kernel lifting counterexample in `unrestricted_capacity_all_kernel_lift_obstruction.md` requires preservation of every function of every Boolean projection. It does not rule out preserving one fixed reciprocal score table. In dimension two, the present theorem realizes any score table with $D+5$ heads and moments through $D$ zero, despite the all-kernel lower bound of order $H^{7/6}$ for a different preservation requirement.

At growing dimension the present construction uses $2^n+D+1$ heads. At the requested width $H$ of order $2^n/n^{3/2}$, this overhead is of order $n^{3/2}$, far larger than a constant. It therefore establishes no unrestricted power saving. The missing lemma is a score-specific or sign-specific version whose width depends on the original width rather than the total number of Boolean queries.

## Verification

The module build and transitive axiom audit are recorded in `cauchy-moment-build.txt` and `cauchy-moment-axioms.txt`. All six theorem declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
