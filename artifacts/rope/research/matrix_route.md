# Arrowhead Matrix and Inertia Route Audit

This route studies an alternate representation of the reciprocal pure subclass. It supplies useful exact identities and a limitation of constant congruences. It does not establish a Boolean head-complexity separation or a general reverse inequality.

## Reciprocal scores as Schur complements

For positive denominators $D_h$ and constants $a_h$, the score $S=c+\sum_h a_h/D_h$ is a Schur complement of a symmetric arrowhead matrix. For nonzero $a_h$, put $\sigma_h=\mathrm{sign}(a_h)$ and $v_h=\sqrt{|a_h|}$. The matrix with query diagonal $-c$, leaf diagonal entries $\sigma_hD_h$, and query-to-leaf entries $v_h$ has Schur complement $-S$. Its leaf inertia is fixed throughout the cube because every $D_h$ is positive. Sylvester's inertia identity therefore isolates the sign of $S$ in the remaining one-dimensional Schur complement. Zero coefficients can be omitted.

The underlying completion of squares is

$$ c t^2+2t\sum_h a_h y_h+\sum_h d_hy_h^2=\left(c-\sum_h\frac{a_h^2}{d_h}\right)t^2+\sum_h d_h\left(y_h+\frac{a_ht}{d_h}\right)^2. $$

This identity, and the equivalence between a negative Schur complement and a negative quadratic value when all $d_h\gt0$, are Lean-checked in `Atoms/RoPEArrowhead.lean`. The handwritten inertia interpretation uses the invertible change of coordinates displayed in the identity.

## Constant congruences preserving the arrowhead form

Suppose the denominator directions are independent, so their separate coefficient matrices are diagonal matrix units on the leaf coordinates. Let $C$ be a constant invertible congruence matrix. Require that the transformed query diagonal remain constant and the transformed leaf block remain diagonal.

For the coefficient matrix of the original leaf $i$, the transformed query diagonal coefficient is $\sigma_i C_{i0}^2$. It vanishes only when $C_{i0}=0$. The transformed off-diagonal leaf coefficient at distinct columns $j,k$ is $\sigma_i C_{ij}C_{ik}$, so $C_{ij}C_{ik}=0$.

The resulting leaf block is invertible, and its distinct columns have coordinatewise disjoint supports. Every column must have a nonzero entry. There are equally many rows and columns, so the supports are singletons and define a permutation. Consequently, every new leaf direction is a positive scalar multiple of one original denominator direction. No orientation change is obtained.

The finite matrix assertion and the positive-scaling conclusion are Lean-checked as `monomial_of_coordinate_separated` and `diagonal_coefficients_permuted` in `Atoms/RoPEArrowhead.lean`. Applying these statements to an arrowhead pencil requires the independent-coefficient and preserved-structure hypotheses just described. They are restrictions on this method, not on all possible Boolean representations.

## Allowing a dense congruence does not immediately help

A dense congruence preserves inertia but usually creates affine interactions among the leaf coordinates. These interactions do not correspond to a sum of independent attention-head fractions. Eliminating them by an LDL decomposition produces rational pivots rather than affine denominators.

There is also a simple subspace obstruction to orienting the diagonals by constant mixing. If every original denominator slope vector has coordinate sum zero, every linear combination of those directions has coordinate sum zero. It cannot have strictly positive slopes or strictly negative slopes. Dense constant congruences still have diagonal coefficient directions in that same span.

Pivoting first on a nonzero constant query entry produces a diagonal affine matrix plus a constant rank-one update. This is another valid inertia representation, but a generic constant basis change does not simultaneously diagonalize all its coefficient matrices. In the special case where the denominators depend on a single affine statistic, the matrices reduce to a univariate pencil, consistent with the partial-fraction construction in Theorem 17. No corresponding simultaneous reduction was found for several independent statistics.

## Input-dependent congruences and strict margins

A diagonal congruence depending on the input can replace a positive leaf denominator $D_h$ by a chosen positive affine form $F_h$. It must scale the leaf coordinate by $\sqrt{F_h/D_h}$. The coupling changes by the same factor, so the induced scalar numerator becomes $a_hF_h/D_h$, which is generally not affine. Requiring it to be affine brings back the exact score-equivalence obstruction. This calculation therefore does not prove a Boolean comparison.

Strict margins permit sufficiently small matrix perturbations on the finite cube. They do not by themselves permit a perturbation large enough to change all denominator slope orientations. After a nearly singular congruence, the smallest nonzero eigenvalue can shrink along with the unwanted coefficients, so deleting the new interactions is not justified merely because those interactions are small in absolute size.

An inertia-based proof would need a new construction that both preserves the relevant sign at every cube point and returns to affine numerators with admissible affine denominators. The identities above do not provide that construction.
