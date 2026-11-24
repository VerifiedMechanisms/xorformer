# Affine Statistics And Collinear Denominators

## Statement

Let $t(x)=b+\sum_i w_i x_i$ be an arbitrary real affine statistic on the Boolean cube. The coefficients $w_i$ may have mixed signs or vanish. Let $p$ be a real univariate polynomial of degree at most $H$ such that

$$ f(x)=1\quad\Longleftrightarrow\quad p(t(x))\gt0. $$

Then the unchanged vanilla model computes $f$ with $H$ heads. This includes $H=0$ and $n=0$.

More generally, suppose a strict-positive classifier has a score

$$ S(x)=c+\sum_{h=1}^H\frac{N_h(x)}{d_h+e_h t(x)}, $$

where every $N_h$ is affine and every displayed denominator is positive on the cube. Then vanilla computes the same Boolean function with $H$ heads.

Consequently, a pure rotary representation whose denominator slope vectors are all collinear cannot improve the vanilla head count, at any $H$. This assertion does not require the pure numerator restriction and also applies to retained rotary scores with collinear denominator slopes.

These are Boolean sign equivalences. The constructions need not preserve the original real scores.

## Proof

### Theorem 1. Polynomial thresholds of an arbitrary affine statistic

First replace $p$ by $p-\delta$ for a sufficiently small $\delta\gt0$. There are finitely many inputs, so this preserves every positive label and makes every negative score strictly negative. Its degree remains at most $H$.

Choose distinct positive numbers $a_1,\ldots,a_H$ with

$$ a_h\gt |b|+\sum_i|w_i|+1. $$

For $0\lt\varepsilon\lt1$, set

$$ B_\varepsilon(x)=1+\varepsilon\sum_i x_i,\qquad y_\varepsilon(x)=\frac{t(x)}{B_\varepsilon(x)},\qquad E_h(x)=\varepsilon t(x)+a_h B_\varepsilon(x). $$

The denominator constant of $E_h$ is $a_h+\varepsilon b\gt0$, and its slope at coordinate $i$ is $\varepsilon(w_i+a_h)\gt0$. Thus every $E_h$ is a vanilla-admissible denominator. Also $B_\varepsilon(x)\gt0$.

The degree bound and distinctness of the poles give an ordinary partial-fraction decomposition

$$ \frac{p(y)}{\prod_{h=1}^H(\varepsilon y+a_h)}=A_\varepsilon+\sum_{h=1}^H\frac{r_{h,\varepsilon}}{\varepsilon y+a_h}. $$

Substitute $y=y_\varepsilon(x)$. The right side becomes

$$ R_\varepsilon(x)=A_\varepsilon+\sum_{h=1}^H\frac{r_{h,\varepsilon}B_\varepsilon(x)}{E_h(x)}. $$

Each numerator is affine. Hence the vanilla normal form realizes this score with $H$ heads. Its sign is the sign of $p(y_\varepsilon(x))$, because every factor $\varepsilon y_\varepsilon(x)+a_h=E_h(x)/B_\varepsilon(x)$ is positive.

As $\varepsilon\to0$, every $y_\varepsilon(x)$ tends to $t(x)$. Continuity of $p$, strictness, and finiteness of the cube therefore give one sufficiently small positive $\varepsilon$ preserving all labels. The selected parameters are finite real numbers. The proof does not use a limiting classifier. For $H=0$, the polynomial and score are constant and the partial-fraction sum is empty. For $n=0$, the same argument applies on the singleton cube. $\blacksquare$

### Theorem 2. Collinear denominator slopes

For $H=0$, the score is constant. Assume $H\geq1$. Decrease $c$ slightly to make $S$ strict without changing its Boolean classifier. Define

$$ q(y)=\prod_{h=1}^H(d_h+e_h y),\qquad q_h(y)=\prod_{j\neq h}(d_j+e_j y),\qquad P(x)=c q(t(x))+\sum_{h=1}^H N_h(x)q_h(t(x)). $$

The polynomial $P$ is the score multiplied by its positive denominator product, so $P$ has the same strict signs. We have $\deg q\leq H$ and $\deg q_h\leq H-1$ even if some $e_h$ vanish or some original poles coincide.

Choose $a_h$, $B_\varepsilon$, $y_\varepsilon$, and $E_h$ as in Theorem 1. Set

$$ P_\varepsilon(x)=c q(y_\varepsilon(x))+\sum_{h=1}^H\frac{N_h(x)}{B_\varepsilon(x)}q_h(y_\varepsilon(x)),\qquad Q_\varepsilon(y)=\prod_{j=1}^H(\varepsilon y+a_j). $$

For fixed $\varepsilon\gt0$, partial fractions provide finite real coefficients satisfying

$$ \frac{q(y)}{Q_\varepsilon(y)}=A_\varepsilon+\sum_{j=1}^H\frac{s_{j,\varepsilon}}{\varepsilon y+a_j},\qquad \frac{q_h(y)}{Q_\varepsilon(y)}=\sum_{j=1}^H\frac{r_{h,j,\varepsilon}}{\varepsilon y+a_j}. $$

The second expression has no polynomial part because its numerator degree is strictly smaller than $H$. Substitution gives

$$ \frac{P_\varepsilon(x)}{Q_\varepsilon(y_\varepsilon(x))}=c A_\varepsilon+\sum_{j=1}^H\frac{c s_{j,\varepsilon}B_\varepsilon(x)+\sum_{h=1}^H r_{h,j,\varepsilon}N_h(x)}{E_j(x)}. $$

Every numerator is affine, and all denominator slopes are strictly positive. The right side therefore has an $H$-head vanilla realization. Its sign is the sign of $P_\varepsilon(x)$. Since $P_\varepsilon(x)\to P(x)$ at each input, one sufficiently small positive $\varepsilon$ preserves the finite strict sign pattern. $\blacksquare$

## Scope and formalization

The result applies to either rotary frequency convention through the scalar normal form in Theorem 14. It does not establish the universal reverse implication for arbitrary pure rotary heads: in general their denominator slope vectors span more than one direction.

[Results/AffineStatisticUpperBound.lean](../../formalization/HeadComplexity/Results/AffineStatisticUpperBound.lean) proves Theorem 1 without changing the vanilla definitions:

- `exists_pos_lt_sign_preserving` verifies finite simultaneous strict-sign preservation under continuous perturbation.
- `AffineStatistic.computable_of_strict_polynomial` proves the construction for a strict sign polynomial.
- `AffineStatistic.computable_of_polynomial` handles the existing strict-positive threshold convention, including zero scores on negative inputs.

[Results/CollinearDenominatorUpperBound.lean](../../formalization/HeadComplexity/Results/CollinearDenominatorUpperBound.lean) proves Theorem 2:

- `AffineStatistic.computable_of_affine_polynomial_sum` handles finite sums of affine coefficients times univariate polynomials of degree strictly below the head count, evaluated at one arbitrary affine statistic.
- `AffineStatistic.computable_of_collinear_denominators` applies this construction to arbitrary positive affine ratios with collinear denominator slopes, with no numerator restriction.
- `pureRoPEFamily_vanilla_of_collinear_denominators` and `retainedRoPEFamily_vanilla_of_collinear_denominators` specialize it to the existing rotary scalar families.

All these Lean declarations cover zero inputs and zero heads and contain no additional axioms or unfinished proof placeholders.
