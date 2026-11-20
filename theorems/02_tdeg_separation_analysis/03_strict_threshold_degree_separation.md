# Theorem 2.3. Strict threshold-degree separation

## Statement

The [separation example (Definition 1.22)](../../definitions/22_separation_example.md) $f_{10}$ has [threshold degree (Definition 1.14)](../../definitions/14_threshold_degree.md) $\deg_{\pm}(f_{10})$ and [head complexity (Definition 1.5)](../../definitions/05_head_complexity.md) $H^{\ast}(f_{10})$ satisfying

$$ \deg_{\pm}(f_{10})=2\lt3\leq H^{\ast}(f_{10}). $$

The two-bit [parity function (Definition 1.20)](../../definitions/20_parity.md) $\mathrm{PARITY}_2$ has the same threshold degree and head complexity two. Thus threshold degree does not determine head complexity.

## Proof

By [Theorem 2.1](01_threshold_degree_of_the_separation_example.md), the threshold degree of $f_{10}$ is two. The lower bound in [Theorem 1.12](../01_foundations_and_normal_form/12_threshold_degree_head_bound.md) therefore excludes zero and one head.

Suppose $f_{10}$ is [computable (Definition 1.4)](../../definitions/04_computability.md) with two heads. By [Theorem 1.13](../01_foundations_and_normal_form/13_two_head_denominator_clearing.md), there is a polynomial [strict sign representation (Definition 1.13)](../../definitions/13_strict_sign_representation.md) $P$ that is a sum of two products of [real affine forms (Definition 1.7)](../../definitions/07_real_affine_forms.md).

Use the inverse encoding $z(x,y)$ from Definition 1.22 and set $g(x,y)=P(z(x,y))$. This affine change of variables preserves affine forms, so $g$ is also a sum of two affine products. Moreover, $g(x,y)$ has the same strict sign as $Q(x,y)$ at every pair of sign vectors.

For each $j\in\lbrace1,\ldots,5\rbrace$, let $s^{(j)}$ have its $j$-th coordinate equal to $-1$ and all other coordinates equal to $+1$. By [Theorem 2.2](02_mixed_rank_bound_for_two_affine_products.md), there is a matrix $M$ of rank at most four representing the [mixed antipodal differences (Definition 1.23)](../../definitions/23_mixed_antipodal_difference.md):

$$ \Delta g(x,s^{(j)})=\sum_{i=1}^{5}M_{ij}x_i. $$

**The target signs force diagonal dominance.** The coordinates of $s^{(j)}$ sum to three, and

$$ \sum_i x_i s_i^{(j)}=\sum_i x_i-2x_j. $$

Consequently,

$$ Q(x,s^{(j)})=3\sum_i x_i-3\left(\sum_i x_i-2x_j\right)=6x_j. $$

The polynomial $Q$ is bilinear, so negating either block reverses its sign and negating both preserves it. Since $g$ has the same strict signs, all four terms in the following expansion are positive:

$$ x_j\Delta g(x,s^{(j)})=x_jg(x,s^{(j)})-x_jg(x,-s^{(j)})-x_jg(-x,s^{(j)})+x_jg(-x,-s^{(j)})\gt0. $$

For a fixed column $j$, choose $x_j=1$ and choose each remaining sign so that $M_{ij}x_i=-\lvert M_{ij}\rvert$. Either sign works when $M_{ij}=0$. Substituting these choices into the matrix expression gives

$$ M_{jj}\gt\sum_{i\neq j}\lvert M_{ij}\rvert. $$

Thus $M$ is strictly column diagonally dominant, with positive diagonal entries.

**Diagonal dominance forces rank five.** If $M^\top v=0$ for a nonzero vector $v\in\mathbb{R}^5$, choose $j$ maximizing $\lvert v_j\rvert\gt0$. The $j$-th equation and the strict column inequality imply

$$ \begin{aligned} M_{jj}\lvert v_j\rvert&=\left\lvert\sum_{i\neq j}M_{ij}v_i\right\rvert \cr &\leq\sum_{i\neq j}\lvert M_{ij}\rvert\lvert v_i\rvert \cr &\leq\left(\sum_{i\neq j}\lvert M_{ij}\rvert\right)\lvert v_j\rvert \cr &\lt M_{jj}\lvert v_j\rvert. \end{aligned} $$

This contradiction shows that $M^\top$ has trivial kernel. Hence $\mathrm{rank}(M)=5$, contradicting Theorem 2.2. Two heads are therefore impossible. Together with the exclusion of zero and one head, this proves $H^{\ast}(f_{10})\geq3$.

Finally, [Theorem 1.20](../01_foundations_and_normal_form/20_parity_complexity.md) gives

$$ \deg _{\pm}(\mathrm{PARITY}_2)=H^{\ast}(\mathrm{PARITY}_2)=2. $$

Thus the two functions have equal threshold degree and different head complexities. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.4. Computability](../../definitions/04_computability.md).
- [Definition 1.5. Head complexity](../../definitions/05_head_complexity.md).
- [Definition 1.7. Real affine forms](../../definitions/07_real_affine_forms.md).
- [Definition 1.13. Strict sign representation](../../definitions/13_strict_sign_representation.md).
- [Definition 1.14. Threshold degree](../../definitions/14_threshold_degree.md).
- [Definition 1.20. Parity](../../definitions/20_parity.md).
- [Definition 1.22. Separation example](../../definitions/22_separation_example.md).
- [Definition 1.23. Mixed antipodal difference](../../definitions/23_mixed_antipodal_difference.md).

**Theorems**

- [Theorem 1.12. Threshold-degree head bound](../01_foundations_and_normal_form/12_threshold_degree_head_bound.md).
- [Theorem 1.13. Two-head denominator clearing](../01_foundations_and_normal_form/13_two_head_denominator_clearing.md).
- [Theorem 1.20. Parity complexity](../01_foundations_and_normal_form/20_parity_complexity.md).
- [Theorem 2.1. Threshold degree of the separation example](01_threshold_degree_of_the_separation_example.md).
- [Theorem 2.2. Mixed-rank bound for two affine products](02_mixed_rank_bound_for_two_affine_products.md).
