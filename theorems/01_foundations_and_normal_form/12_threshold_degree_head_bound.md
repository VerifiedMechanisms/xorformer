# Theorem 1.12. Threshold-degree head bound

## Statement

Let $n\in\mathbb{Z}_{\geq1}$ and $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$. If $f$ is [computable (Definition 1.4)](../../definitions/04_computability.md) with $H\in\mathbb{Z} _{\geq0}$ heads, then it has a polynomial [strict sign representation (Definition 1.12)](../../definitions/12_strict_sign_representation.md) $P$ of total degree at most $H$.

Consequently, its [threshold degree (Definition 1.13)](../../definitions/13_threshold_degree.md) $\deg_{\pm}(f)$ and [head complexity (Definition 1.5)](../../definitions/05_head_complexity.md) $H^{\ast}(f)$ satisfy

$$ \deg_{\pm}(f)\leq H^{\ast}(f). $$

## Proof

Fix a feasible head count $H$. By [Theorem 1.4](04_exact_linear_fractional_normal_form.md), a [score (Definition 1.2)](../../definitions/02_score.md) $\Phi$ that [classifies (Definition 1.3)](../../definitions/03_classification.md) $f$ with $H$ heads has the form

$$ \Phi(x)=c+\sum_{h=1}^{H}\frac{N_h(x)}{D_h(x)}, $$

where each $N_h,D_h$ is affine and every $D_h$ is strictly positive on the Boolean cube. Define the polynomials

$$ B(x)=\prod_{h=1}^{H}D_h(x), \qquad P(x)=cB(x)+\sum_{h=1}^{H}N_h(x)\prod_{\substack{1\leq g\leq H\cr g\neq h}}D_g(x). $$

On every Boolean input, $B(x)\gt0$ and $P(x)=B(x)\Phi(x)$. Thus $P$ has the same strict signs as $\Phi$ and strictly sign-represents $f$.

For $H=0$, the empty product is one and the empty sum is zero, so $P=c$ is a nonzero constant. For $H\geq1$, each term defining $P$ is a constant multiple of a product of $H$ affine factors. In both cases, $P$ has total degree at most $H$.

It follows that $\deg_{\pm}(f)\leq H$ for every feasible head count. If $H^{\ast}(f)$ is finite, take $H=H^{\ast}(f)$. If the feasible set is empty, then $H^{\ast}(f)=\infty$, while [Theorem 1.11](11_boolean_polynomial_interpolation.md) gives $\deg_{\pm}(f)\leq n$. The asserted inequality therefore holds in either case. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.2. Score](../../definitions/02_score.md).
- [Definition 1.3. Classification](../../definitions/03_classification.md).
- [Definition 1.4. Computability](../../definitions/04_computability.md).
- [Definition 1.5. Head complexity](../../definitions/05_head_complexity.md).
- [Definition 1.12. Strict sign representation](../../definitions/12_strict_sign_representation.md).
- [Definition 1.13. Threshold degree](../../definitions/13_threshold_degree.md).

**Theorems**

- [Theorem 1.4. Exact linear-fractional normal form](04_exact_linear_fractional_normal_form.md).
- [Theorem 1.11. Boolean polynomial interpolation](11_boolean_polynomial_interpolation.md).
