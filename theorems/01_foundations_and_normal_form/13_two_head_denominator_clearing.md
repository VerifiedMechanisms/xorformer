# Theorem 1.13. Two-head denominator clearing

## Statement

Let $n\in\mathbb{Z}_{\geq1}$ and $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$. If $f$ is [computable (Definition 1.4)](../../definitions/04_computability.md) with two heads, then it has a polynomial [strict sign representation (Definition 1.12)](../../definitions/12_strict_sign_representation.md) $P$ of the form

$$ P=L_1R_1+L_2R_2, $$

where $L_1,R_1,L_2,R_2$ are [real affine forms (Definition 1.14)](../../definitions/14_real_affine_forms.md) in the input coordinates.

## Proof

Choose a [score (Definition 1.2)](../../definitions/02_score.md) $\Phi$ realizable with two heads that [classifies (Definition 1.3)](../../definitions/03_classification.md) $f$. By [Theorem 1.4](04_exact_linear_fractional_normal_form.md), write

$$ \Phi(x)=c+\frac{N_1(x)}{D_1(x)}+\frac{N_2(x)}{D_2(x)}, $$

with affine numerators and denominators, where $D_1(x),D_2(x)\gt0$ on every Boolean input. Define

$$ L_1=cD_1+N_1, \qquad R_1=D_2, \qquad L_2=N_2, \qquad R_2=D_1. $$

All four forms are affine. The polynomial $P=L_1R_1+L_2R_2$ satisfies, on the Boolean cube,

$$ \begin{aligned} P(x)&=\bigl(cD_1(x)+N_1(x)\bigr)D_2(x)+N_2(x)D_1(x) \cr &=D_1(x)D_2(x)\Phi(x). \end{aligned} $$

The multiplier $D_1(x)D_2(x)$ is strictly positive, so $P$ has the same strict signs as $\Phi$. Hence $P$ strictly sign-represents $f$. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.2. Score](../../definitions/02_score.md).
- [Definition 1.3. Classification](../../definitions/03_classification.md).
- [Definition 1.4. Computability](../../definitions/04_computability.md).
- [Definition 1.12. Strict sign representation](../../definitions/12_strict_sign_representation.md).
- [Definition 1.14. Real affine forms](../../definitions/14_real_affine_forms.md).

**Theorems**

- [Theorem 1.4. Exact linear-fractional normal form](04_exact_linear_fractional_normal_form.md).
