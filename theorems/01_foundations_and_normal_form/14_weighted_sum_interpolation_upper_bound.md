# Theorem 1.14. Weighted-sum interpolation upper bound

## Statement

Let $n\in\mathbb{Z}_{\geq1}$ and let a [positive weighted statistic (Definition 1.15)](../../definitions/15_positive_weighted_statistics.md) $t$ have image $T$ of size $M$. For every function $G:T\to\mathbb{R}$, the [score (Definition 1.2)](../../definitions/02_score.md) $\Phi$ given by

$$ \Phi(x)=G(t(x)) $$

is realizable with $M-1$ heads.

In particular, if $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$ satisfies $f(x)=F(t(x))$ for some $F:T\to\lbrace0,1\rbrace$, then its [head complexity (Definition 1.5)](../../definitions/05_head_complexity.md) $H^{\ast}(f)$ satisfies

$$ H^{\ast}(f)\leq M-1. $$

## Proof

All values in $T$ are nonnegative. The set contains zero and $t(1,\ldots,1)\gt0$, so $M\geq2$.

**Interpolation.** Choose distinct positive numbers $r_1,\ldots,r_{M-1}$. We show that the functions

$$ 1,\qquad \frac{1}{s+r_1},\qquad\ldots,\qquad\frac{1}{s+r_{M-1}} $$

form a basis of the real-valued functions on $T$. Suppose

$$ a_0+\sum_{j=1}^{M-1}\frac{a_j}{s+r_j}=0\qquad\text{for every }s\in T. $$

Every denominator is positive on $T$. Multiplying by their product shows that the polynomial

$$ Q(s)=a_0\prod_{j=1}^{M-1}(s+r_j)+\sum_{j=1}^{M-1}a_j\prod_{\substack{1\leq\ell\leq M-1\cr \ell\neq j}}(s+r_\ell) $$

vanishes at all $M$ distinct points of $T$. Its degree is at most $M-1$, so $Q$ is the zero polynomial. For each $j$, evaluating this polynomial identity at $s=-r_j$ gives

$$ a_j\prod_{\substack{1\leq\ell\leq M-1\cr \ell\neq j}}(r_\ell-r_j)=0. $$

The shifts are distinct, so every factor in the product is nonzero; an empty product equals one. Hence $a_j=0$ for all $j\geq1$. The original relation then gives $a_0=0$.

Thus the displayed functions are linearly independent. The space of real-valued functions on the $M$-point set $T$ has dimension $M$, so these $M$ functions form a basis. Therefore there are real coefficients $c_0,\ldots,c_{M-1}$ such that

$$ G(s)=c_0+\sum_{j=1}^{M-1}\frac{c_j}{s+r_j}\qquad\text{for every }s\in T. $$

**Realization.** Let $\lambda=(\lambda_1,\ldots,\lambda_n)$ be the weight vector of $t$. Each term $c_j/(t(x)+r_j)$ is an [admissible ratio (Definition 1.7)](../../definitions/07_admissible_ratios.md), with coefficient tuple $(0,c_j,\lambda,r_j)$. Its denominator is at least $r_j\gt0$ on the cube, and every denominator slope $\lambda_i$ is strictly positive. The numerator constant $c_j$ is unrestricted.

By [Theorem 1.4](04_exact_linear_fractional_normal_form.md), the score

$$ \Phi(x)=c_0+\sum_{j=1}^{M-1}\frac{c_j}{t(x)+r_j}=G(t(x)) $$

is realizable with $M-1$ heads, with equality of the full real-valued score on every input.

For the Boolean consequence, take $G(s)=2F(s)-1$. The realized score is one on true inputs and minus one on false inputs, so it [classifies (Definition 1.3)](../../definitions/03_classification.md) $f$. Thus $M-1$ is a feasible head count and $H^{\ast}(f)\leq M-1$. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.2. Score](../../definitions/02_score.md).
- [Definition 1.3. Classification](../../definitions/03_classification.md).
- [Definition 1.5. Head complexity](../../definitions/05_head_complexity.md).
- [Definition 1.7. Admissible ratios](../../definitions/07_admissible_ratios.md).
- [Definition 1.15. Positive weighted statistics](../../definitions/15_positive_weighted_statistics.md).

**Theorems**

- [Theorem 1.4. Exact linear-fractional normal form](04_exact_linear_fractional_normal_form.md).
