# Theorem 1.8. Affine checkerboard nonseparability

## Statement

Let $c\in\lbrace0,1\rbrace$ and $g:\lbrace0,1\rbrace^2\to\lbrace0,1\rbrace$ have the [checkerboard pattern](../../definitions/11_checkerboard_restrictions.md)

$$ g(0,0)=g(1,1)=c, \qquad g(0,1)=g(1,0)=1-c. $$

Then $g$ is not a [linear threshold function](../../definitions/09_linear_threshold_functions.md).

## Proof

Suppose an affine score $\ell(a,b)=\beta_0+\beta_1 a+\beta_2 b$ [classifies](../../definitions/03_classification.md) $g$. Its two diagonal sums agree:

$$ \ell(0,0)+\ell(1,1)=2\beta_0+\beta_1+\beta_2=\ell(0,1)+\ell(1,0). $$

One diagonal consists of true inputs, so its score sum is strictly positive. The other consists of false inputs, so its score sum is nonpositive. This contradicts their equality, for either choice of $c$. $\blacksquare$

## Dependencies

**Definitions**

- [Classification](../../definitions/03_classification.md).
- [Linear threshold functions](../../definitions/09_linear_threshold_functions.md).
- [Checkerboard restrictions](../../definitions/11_checkerboard_restrictions.md).

**Theorems**

None.
