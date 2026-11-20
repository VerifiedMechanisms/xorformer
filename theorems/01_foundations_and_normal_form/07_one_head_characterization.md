# Theorem 1.7. One-head characterization

## Statement

Let $n\in\mathbb{Z}_{\geq1}$ and $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$. Its [head complexity (Definition 1.5)](../../definitions/05_head_complexity.md) $H^{\ast}(f)$ satisfies

$$ H^{\ast}(f)=1\quad\Longleftrightarrow\quad f\text{ is a nonconstant linear threshold function}, $$

using the notion of a [linear threshold function (Definition 1.10)](../../definitions/10_linear_threshold_functions.md).

## Proof

**Necessity.** Suppose $H^{\ast}(f)=1$. By [Theorem 1.4](04_exact_linear_fractional_normal_form.md), a realizing [score](../../definitions/02_score.md) $\Phi$ has the form

$$ \Phi(x)=c+\frac{N(x)}{D(x)}, $$

where $N,D$ are affine and $D(x)\gt0$ on every input. The affine score $\ell(x)=cD(x)+N(x)$ satisfies

$$ \ell(x)=D(x)\Phi(x). $$

The positive factor $D(x)$ preserves both strict signs, so $\ell$ classifies $f$. Hence $f$ is a linear threshold function. It is nonconstant by [Theorem 1.6](06_zero_head_constants.md).

**Sufficiency.** Suppose $f$ is nonconstant and [classified](../../definitions/03_classification.md) by an affine score $\ell(x)=\beta_0+\beta^\top x$. Set

$$ D(x)=1+\sum_{i=1}^{n}x_i, \qquad \Phi(x)=\frac{\ell(x)}{D(x)}. $$

The denominator is at least one and all its slopes equal one. Thus this ratio is [admissible](../../definitions/08_admissible_ratios.md), with no restriction on its numerator coefficients. By Theorem 1.4, the score $\Phi$ is realizable with one head. Its positive denominator preserves the classification of $\ell$, so $H^{\ast}(f)\leq1$. Theorem 1.6 excludes zero because $f$ is nonconstant. Therefore $H^{\ast}(f)=1$. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.2. Score](../../definitions/02_score.md).
- [Definition 1.3. Classification](../../definitions/03_classification.md).
- [Definition 1.5. Head complexity](../../definitions/05_head_complexity.md).
- [Definition 1.8. Admissible ratios](../../definitions/08_admissible_ratios.md).
- [Definition 1.10. Linear threshold functions](../../definitions/10_linear_threshold_functions.md).

**Theorems**

- [Theorem 1.4. Exact linear-fractional normal form](04_exact_linear_fractional_normal_form.md).
- [Theorem 1.6. Zero-head constants](06_zero_head_constants.md).
