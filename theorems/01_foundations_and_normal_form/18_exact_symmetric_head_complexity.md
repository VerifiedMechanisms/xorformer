# Theorem 1.18. Exact symmetric head complexity

## Statement

Let $n\in\mathbb{Z}_{\geq1}$ and let $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$ be a [symmetric function (Definition 1.17)](../../definitions/17_symmetric_functions.md), with $f(x)=F(|x|)$. Its [head complexity (Definition 1.5)](../../definitions/05_head_complexity.md) $H^{\ast}(f)$ equals its [sign-change count (Definition 1.18)](../../definitions/18_sign_change_count.md) $C(F)$:

$$ H^{\ast}(f)=C(F). $$

## Proof

Set $C=C(F)$. [Theorem 1.12](12_threshold_degree_head_bound.md) bounds head complexity below by [threshold degree (Definition 1.14)](../../definitions/14_threshold_degree.md). By [Theorem 1.17](17_symmetric_threshold_degree.md), this gives

$$ H^{\ast}(f)\geq\deg_{\pm}(f)=C. $$

If $C=0$, all adjacent values of $F$ agree, so $f$ is constant. [Theorem 1.6](06_zero_head_constants.md) gives $H^{\ast}(f)=0$.

Suppose now that $C\geq1$. Take the univariate polynomial $P$ of degree $C$ supplied by Theorem 1.17, so that $P(|x|)$ has the required strict signs. Choose distinct positive numbers $r_1,\ldots,r_C$ and define

$$ B(z)=\prod_{j=1}^{C}(z+r_j). $$

This polynomial is monic of degree $C$ and strictly positive for $z\geq0$. We express $P/B$ as a constant plus $C$ reciprocals.

Let $c$ be the leading coefficient of $P$. For $1\leq j\leq C$, set

$$ d_j=\frac{P(-r_j)}{\prod_{\substack{1\leq\ell\leq C\cr \ell\neq j}}(r_\ell-r_j)}. $$

The denominator is nonzero because the shifts are distinct; an empty product is one. The polynomial

$$ E(z)=P(z)-cB(z)-\sum_{j=1}^{C}d_j\prod_{\substack{1\leq\ell\leq C\cr \ell\neq j}}(z+r_\ell) $$

has degree at most $C-1$: the leading terms of $P$ and $cB$ cancel, and each remaining product has degree $C-1$. For every $i$, evaluation at $z=-r_i$ leaves only $P(-r_i)$ and the summand with $j=i$, which cancel by the definition of $d_i$. Thus $E$ has $C$ distinct roots and must be identically zero. Dividing by $B(z)$ for $z\geq0$ gives

$$ \frac{P(z)}{B(z)}=c+\sum_{j=1}^{C}\frac{d_j}{z+r_j}. $$

On the Boolean cube, each term $d_j/(|x|+r_j)$ is an [admissible ratio (Definition 1.8)](../../definitions/08_admissible_ratios.md): its denominator is positive, every denominator slope is one, and its numerator is constant. By [Theorem 1.4](04_exact_linear_fractional_normal_form.md), the [score (Definition 1.2)](../../definitions/02_score.md)

$$ \Phi(x)=c+\sum_{j=1}^{C}\frac{d_j}{|x|+r_j}=\frac{P(|x|)}{B(|x|)} $$

is realizable with $C$ heads. Since $B(|x|)\gt0$, this score has the same strict signs as $P(|x|)$ and therefore [classifies (Definition 1.3)](../../definitions/03_classification.md) $f$. Hence $H^{\ast}(f)\leq C$, completing the equality. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.2. Score](../../definitions/02_score.md).
- [Definition 1.3. Classification](../../definitions/03_classification.md).
- [Definition 1.5. Head complexity](../../definitions/05_head_complexity.md).
- [Definition 1.8. Admissible ratios](../../definitions/08_admissible_ratios.md).
- [Definition 1.14. Threshold degree](../../definitions/14_threshold_degree.md).
- [Definition 1.17. Symmetric functions](../../definitions/17_symmetric_functions.md).
- [Definition 1.18. Sign-change count](../../definitions/18_sign_change_count.md).

**Theorems**

- [Theorem 1.4. Exact linear-fractional normal form](04_exact_linear_fractional_normal_form.md).
- [Theorem 1.6. Zero-head constants](06_zero_head_constants.md).
- [Theorem 1.12. Threshold-degree head bound](12_threshold_degree_head_bound.md).
- [Theorem 1.17. Symmetric threshold degree](17_symmetric_threshold_degree.md).
