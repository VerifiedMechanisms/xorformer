# Theorem 1.15. Universal head bound

## Statement

Let $n\in\mathbb{Z}_{\geq1}$. Every Boolean function $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$ has finite [head complexity (Definition 1.5)](../../definitions/05_head_complexity.md) $H^{\ast}(f)$, with

$$ H^{\ast}(f)\leq2^n-1. $$

## Proof

Choose the [positive weighted statistic (Definition 1.15)](../../definitions/15_positive_weighted_statistics.md)

$$ t(x)=\sum_{i=1}^{n}2^{i-1}x_i. $$

This statistic is injective. Indeed, for distinct inputs $x,y$, let $k$ be their largest differing coordinate. In $t(x)-t(y)$, the term from coordinate $k$ has absolute value $2^{k-1}$, while the sum of all lower-coordinate terms has absolute value at most

$$ \sum_{i=1}^{k-1}2^{i-1}=2^{k-1}-1\lt2^{k-1}. $$

All higher-coordinate terms vanish, so $t(x)\neq t(y)$.

Consequently, the image $T$ has $2^n$ elements, and $F(t(x))=f(x)$ defines a function $F:T\to\lbrace0,1\rbrace$. Applying [Theorem 1.14](14_weighted_sum_interpolation_upper_bound.md) with $M=2^n$ gives a realization with $2^n-1$ heads. Hence the feasible head counts are nonempty and $H^{\ast}(f)\leq2^n-1$. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.5. Head complexity](../../definitions/05_head_complexity.md).
- [Definition 1.15. Positive weighted statistics](../../definitions/15_positive_weighted_statistics.md).

**Theorems**

- [Theorem 1.14. Weighted-sum interpolation upper bound](14_weighted_sum_interpolation_upper_bound.md).
