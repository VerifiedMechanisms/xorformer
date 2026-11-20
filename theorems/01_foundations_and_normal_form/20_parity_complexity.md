# Theorem 1.20. Parity complexity

## Statement

Let $n\in\mathbb{Z}_{\geq1}$. The [parity function (Definition 1.20)](../../definitions/20_parity.md) $\mathrm{PARITY}_n$ has [threshold degree (Definition 1.14)](../../definitions/14_threshold_degree.md) $\deg _{\pm}(\mathrm{PARITY}_n)$ and [head complexity (Definition 1.5)](../../definitions/05_head_complexity.md) $H^{\ast}(\mathrm{PARITY}_n)$ given by

$$ \deg_{\pm}(\mathrm{PARITY}_n)=H^{\ast}(\mathrm{PARITY}_n)=n. $$

## Proof

### Sign-change proof

Write $\mathrm{PARITY}_n(x)=F(|x|)$. The label changes between every pair of adjacent weights, so the [sign-change count (Definition 1.18)](../../definitions/18_sign_change_count.md) is $C(F)=n$. [Theorem 1.17](17_symmetric_threshold_degree.md) gives threshold degree $n$, and [Theorem 1.18](18_exact_symmetric_head_complexity.md) gives head complexity $n$.

### Fourier proof of the lower bound

Suppose that a polynomial $P(x)$ of total degree $d\lt n$ [strictly sign-represents (Definition 1.13)](../../definitions/13_strict_sign_representation.md) parity. Change coordinates by $z_i=1-2x_i$ and put

$$ Q(z)=P\left(\frac{1-z_1}{2},\ldots,\frac{1-z_n}{2}\right), \qquad \pi(z)=-\prod_{i=1}^{n}z_i. $$

The polynomial $Q$ has degree at most $d$. As $x$ ranges over the Boolean cube, $z$ ranges over $\lbrace-1,1\rbrace^n$. Since $\pi(z)=-(-1)^{|x|}$, it is the target sign for parity. Thus $\pi(z)Q(z)\gt0$ at every such $z$. Let $\mathbb{E}$ denote uniform averaging over this cube; then

$$ \mathbb{E}[\pi Q]\gt0. $$

On this cube, the identities $z_i^2=1$ reduce each monomial of $Q$ to a squarefree monomial without increasing degree. Every resulting monomial uses fewer than $n$ coordinates. Hence, on the cube, there are real coefficients $a_S$ such that

$$ Q(z)=\sum_{S\subsetneq\lbrace1,\ldots,n\rbrace}a_S\chi_S(z), \qquad \chi_S(z)=\prod_{i\in S}z_i. $$

These products are the Walsh characters. For each proper subset $S$,

$$ \pi(z)\chi_S(z)=-\prod_{i\in\lbrace1,\ldots,n\rbrace\setminus S}z_i. $$

The complement of $S$ is nonempty. Flipping one coordinate in that complement pairs each value of this product with its negative, so its uniform average is zero. By linearity,

$$ \mathbb{E}[\pi Q]=\sum_{S\subsetneq\lbrace1,\ldots,n\rbrace}a_S\mathbb{E}[\pi\chi_S]=0, $$

contradicting strict positivity. Therefore parity has threshold degree at least $n$. The matching degree $n$ polynomial is

$$ P_{\mathrm{par}}(x)=-\prod_{i=1}^{n}(1-2x_i), $$

whose value is one on odd inputs and minus one on even inputs. [Theorem 1.12](12_threshold_degree_head_bound.md) then gives the head lower bound $H^{\ast}(\mathrm{PARITY}_n)\geq n$, matching the upper bound already obtained from Theorem 1.18.

### Checkerboard restriction

For $n\geq2$, leave the first two coordinates free and fix all others to zero. The restricted function $g$ satisfies

$$ g(0,0)=g(1,1)=0, \qquad g(0,1)=g(1,0)=1. $$

This is a [checkerboard restriction (Definition 1.12)](../../definitions/12_checkerboard_restrictions.md). [Theorem 1.10](10_checkerboard_head_bound.md) therefore also gives $H^{\ast}(\mathrm{PARITY}_n)\geq2$, exhibiting the obstruction to one head on a two-coordinate restriction. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.5. Head complexity](../../definitions/05_head_complexity.md).
- [Definition 1.12. Checkerboard restrictions](../../definitions/12_checkerboard_restrictions.md).
- [Definition 1.13. Strict sign representation](../../definitions/13_strict_sign_representation.md).
- [Definition 1.14. Threshold degree](../../definitions/14_threshold_degree.md).
- [Definition 1.18. Sign-change count](../../definitions/18_sign_change_count.md).
- [Definition 1.20. Parity](../../definitions/20_parity.md).

**Theorems**

- [Theorem 1.10. Checkerboard head bound](10_checkerboard_head_bound.md).
- [Theorem 1.12. Threshold-degree head bound](12_threshold_degree_head_bound.md).
- [Theorem 1.17. Symmetric threshold degree](17_symmetric_threshold_degree.md).
- [Theorem 1.18. Exact symmetric head complexity](18_exact_symmetric_head_complexity.md).
