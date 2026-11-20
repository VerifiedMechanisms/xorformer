# Theorem 1.20. Exact-count complexity

## Statement

Let $n,k$ be integers with $n\geq1$ and $0\leq k\leq n$. The [exact-count predicate (Definition 1.20)](../../definitions/20_exact_count_predicates.md) $\mathrm{EXACT}_{n,k}$ has [head complexity (Definition 1.5)](../../definitions/05_head_complexity.md)

$$ H^{\ast}(\mathrm{EXACT}_{n,k})=\begin{cases} 2 & 1\leq k\leq n-1, \cr 1 & k\in\lbrace0,n\rbrace. \end{cases} $$

## Proof

### Sign-change proof

Write $\mathrm{EXACT}_{n,k}(x)=F(|x|)$, so $F(s)=1$ exactly when $s=k$. For an internal count, the weight sequence changes from zero to one between $k-1$ and $k$, and from one to zero between $k$ and $k+1$. There are no other changes, so its [sign-change count (Definition 1.17)](../../definitions/17_sign_change_count.md) is $C(F)=2$.

For $k=0$, the only change is between weights zero and one. For $k=n$, the only change is between weights $n-1$ and $n$. Thus $C(F)=1$ in either endpoint case. [Theorem 1.17](17_exact_symmetric_head_complexity.md) gives $H^{\ast}(\mathrm{EXACT}_{n,k})=C(F)$ in every case, including $n=1$, when both possible counts are endpoints.

### Checkerboard proof of the internal lower bound

Suppose $1\leq k\leq n-1$. Leave two coordinates free and fix exactly $k-1$ of the other $n-2$ coordinates to one, with all remaining coordinates zero. This is possible because $0\leq k-1\leq n-2$.

For free bits $a,b$, the total weight is $k-1+a+b$. Consequently, the restricted exact-count function $g$ satisfies

$$ g(0,0)=g(1,1)=0, \qquad g(0,1)=g(1,0)=1. $$

This is a [checkerboard restriction (Definition 1.11)](../../definitions/11_checkerboard_restrictions.md), so [Theorem 1.10](10_checkerboard_head_bound.md) gives $H^{\ast}(\mathrm{EXACT}_{n,k})\geq2$. This matches the upper bound from the sign-change proof. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.5. Head complexity](../../definitions/05_head_complexity.md).
- [Definition 1.11. Checkerboard restrictions](../../definitions/11_checkerboard_restrictions.md).
- [Definition 1.17. Sign-change count](../../definitions/17_sign_change_count.md).
- [Definition 1.20. Exact-count predicates](../../definitions/20_exact_count_predicates.md).

**Theorems**

- [Theorem 1.10. Checkerboard head bound](10_checkerboard_head_bound.md).
- [Theorem 1.17. Exact symmetric head complexity](17_exact_symmetric_head_complexity.md).
