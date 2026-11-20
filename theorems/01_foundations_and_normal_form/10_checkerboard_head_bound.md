# Theorem 1.10. Checkerboard head bound

## Statement

Let $n\in\mathbb{Z}_{\geq2}$ and $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$. If $f$ contains a [checkerboard restriction (Definition 1.11)](../../definitions/11_checkerboard_restrictions.md), then its [head complexity (Definition 1.5)](../../definitions/05_head_complexity.md) $H^{\ast}(f)$ satisfies

$$ H^{\ast}(f)\geq2. $$

## Proof

Fix a [two-coordinate restriction](../../definitions/10_two_coordinate_restrictions.md) $g(a,b)=f(x^{(a,b)})$ with the checkerboard pattern. It takes both Boolean values, so $f$ is nonconstant. [Theorem 1.6](06_zero_head_constants.md) rules out zero heads. Each of the following arguments rules out one head.

### Affine proof

If one head computed $f$, its head complexity would be one, since zero is already excluded. By [Theorem 1.7](07_one_head_characterization.md), the function $f$ would be a [linear threshold function](../../definitions/09_linear_threshold_functions.md), classified by an affine score $\ell(x)$.

Substituting the fixed coordinates into $\ell$ leaves an affine function of the two free bits $a,b$. It would classify $g$, contrary to [Theorem 1.8](08_affine_checkerboard_nonseparability.md).

### Geometric proof

Suppose instead that a one-head [model](../../definitions/01_model.md) computes $f$, and write $z(a,b)=y_1(x^{(a,b)})$ for its projected head output. By [Theorem 1.9](09_intersection_of_output_diagonals.md), the two output segments meet at a point $P$.

For the realizing readout $w,\tau$, the [score](../../definitions/02_score.md) $\Phi$ on the restriction is the affine function $\Lambda$ of the projected output given by

$$ \Phi(x^{(a,b)})=\Lambda(z(a,b)), \qquad \Lambda(z)=w^\top z+c, \qquad c=w^\top u_{=}-\tau. $$

By the [classification convention](../../definitions/03_classification.md), $\Lambda$ is strictly positive at both endpoints of the true diagonal and strictly negative at both endpoints of the false diagonal. An affine function preserves convex combinations, so these strict inequalities hold on the respective segments. At their common point $P$, this would give both $\Lambda(P)\gt0$ and $\Lambda(P)\lt0$, a contradiction.

Thus neither zero nor one is a feasible head count. The minimum is at least two if the feasible set is nonempty, and is $\infty$ otherwise. In either case, the claimed bound holds. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.1. Model](../../definitions/01_model.md).
- [Definition 1.2. Score](../../definitions/02_score.md).
- [Definition 1.3. Classification](../../definitions/03_classification.md).
- [Definition 1.5. Head complexity](../../definitions/05_head_complexity.md).
- [Definition 1.9. Linear threshold functions](../../definitions/09_linear_threshold_functions.md).
- [Definition 1.10. Two-coordinate restrictions](../../definitions/10_two_coordinate_restrictions.md).
- [Definition 1.11. Checkerboard restrictions](../../definitions/11_checkerboard_restrictions.md).

**Theorems**

- [Theorem 1.6. Zero-head constants](06_zero_head_constants.md).
- [Theorem 1.7. One-head characterization](07_one_head_characterization.md).
- [Theorem 1.8. Affine checkerboard nonseparability](08_affine_checkerboard_nonseparability.md).
- [Theorem 1.9. Intersection of output diagonals](09_intersection_of_output_diagonals.md).
