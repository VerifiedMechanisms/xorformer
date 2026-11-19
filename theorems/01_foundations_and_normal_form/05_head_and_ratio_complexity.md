# Theorem 1.5. Head and ratio complexity

## Statement

Let $n\in\mathbb{Z}_{\geq1}$ and $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$. Its [head complexity (Definition 1.5)](../../definitions/05_head_complexity.md) $H^{\ast}(f)$ and [ratio complexity (Definition 1.8)](../../definitions/08_ratio_complexity.md) $L(f)$ satisfy

$$ H^{\ast}(f)=L(f). $$

## Proof

Fix $H\in\mathbb{Z}_{\geq0}$. By [computability](../../definitions/04_computability.md), the function $f$ is computable with $H$ heads exactly when a score $\Phi$ realizable with $H$ heads [classifies](../../definitions/03_classification.md) $f$.

By [Theorem 1.4](04_exact_linear_fractional_normal_form.md), these scores are exactly the sums of $H$ admissible ratios plus a constant. Thus $H$ is feasible for head complexity exactly when it is feasible for ratio complexity.

The feasible sets coincide, including their possible zero element. Their minima agree when nonempty, and both definitions give $\infty$ when empty. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.3. Classification](../../definitions/03_classification.md).
- [Definition 1.4. Computability](../../definitions/04_computability.md).
- [Definition 1.5. Head complexity](../../definitions/05_head_complexity.md).
- [Definition 1.8. Ratio complexity](../../definitions/08_ratio_complexity.md).

**Theorems**

- [Theorem 1.4. Exact linear-fractional normal form](04_exact_linear_fractional_normal_form.md).
