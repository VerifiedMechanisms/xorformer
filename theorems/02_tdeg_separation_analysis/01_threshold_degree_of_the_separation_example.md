# Theorem 2.1. Threshold degree of the separation example

## Statement

Let $f_{10}$ and $Q$ be the [separation example (Definition 1.22)](../../definitions/22_separation_example.md) and its defining quadratic polynomial. Then $Q(x,y)\neq0$ for all $x,y\in\lbrace-1,+1\rbrace^5$.

In Boolean coordinates, $Q$ is a polynomial [strict sign representation (Definition 1.12)](../../definitions/12_strict_sign_representation.md) of $f_{10}$, whose [threshold degree (Definition 1.13)](../../definitions/13_threshold_degree.md) is

$$ \deg_{\pm}(f_{10})=2. $$

## Proof

Let $A$ count the negative coordinates of $x$, let $B$ count those of $y$, and let $C$ count the positions where both coordinates are negative. Then

$$ \sum_i x_i=5-2A, \qquad \sum_i y_i=5-2B, \qquad \sum_i x_i y_i=5-2A-2B+4C. $$

Consequently,

$$ \begin{aligned} Q(x,y)&=(5-2A)(5-2B)-3(5-2A-2B+4C) \cr &=10+4(-A-B+AB-3C). \end{aligned} $$

Thus $Q(x,y)\equiv2\pmod4$, so $Q$ never vanishes on the sign cube. Its sign therefore strictly represents the labels of $f_{10}$. Substituting $x_i=1-2z_i$ and $y_i=1-2z_{5+i}$ produces a polynomial of degree at most two in the Boolean coordinates. Hence $\deg_{\pm}(f_{10})\leq2$.

For the reverse bound, restrict the sign vectors to

$$ x=(a,1,1,-1,-1), \qquad y=(b,1,-1,1,-1), \qquad a,b\in\lbrace-1,+1\rbrace. $$

On this restriction,

$$ \sum_i x_i=a, \qquad \sum_i y_i=b, \qquad \sum_i x_i y_i=ab, \qquad Q(x,y)=-2ab. $$

The label is one exactly when $a$ and $b$ have opposite signs. In the two free Boolean coordinates this is the [checkerboard pattern (Definition 1.11)](../../definitions/11_checkerboard_restrictions.md) with labels zero on the equal-bit inputs and one on the unequal-bit inputs.

A polynomial of degree at most one is a [real affine form (Definition 1.14)](../../definitions/14_real_affine_forms.md). Fixing the other eight Boolean coordinates leaves an affine form in the two free bits. By [Theorem 1.8](../01_foundations_and_normal_form/08_affine_checkerboard_nonseparability.md), such a form cannot classify the checkerboard pattern. Therefore $\deg_{\pm}(f_{10})\geq2$, which proves equality. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.11. Checkerboard restrictions](../../definitions/11_checkerboard_restrictions.md).
- [Definition 1.12. Strict sign representation](../../definitions/12_strict_sign_representation.md).
- [Definition 1.13. Threshold degree](../../definitions/13_threshold_degree.md).
- [Definition 1.14. Real affine forms](../../definitions/14_real_affine_forms.md).
- [Definition 1.22. Separation example](../../definitions/22_separation_example.md).

**Theorems**

- [Theorem 1.8. Affine checkerboard nonseparability](../01_foundations_and_normal_form/08_affine_checkerboard_nonseparability.md).
