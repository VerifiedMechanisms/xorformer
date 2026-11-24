# An exact obstruction to constant denominator balancing

## Kernel-checked statement

There is an actual affine basis of eleven vertices of the ten-dimensional Boolean cube, prescribed unit values on that basis, and a nonempty feasible sign branch such that every nonnegative affine denominator in this branch satisfies

$$ 8b_0\leq\sum_{i=0}^{10}b_i. $$

The branch contains a genuine original-model head with strictly positive denominator coefficients and full-cube absolute score at least one. The theorem is `HeadComplexity.FixedBasisBalanceObstruction.constant_mass_le_eighth` in [FixedBasisBalanceObstruction.lean](../../formalization/HeadComplexity/Research/FixedBasisBalanceObstruction.lean). The same file proves full-cube feasibility, admissibility, the unit observations, and injectivity of the actual affine evaluation basis.

This is a fixed-chart obstruction. It does not rule out an inverse-polynomial balancing theorem, changing the actual basis, or replacing the representation of the same truth table.

## Exact data and decisive inequality

Vertices are numbered by their ten binary coordinates, most significant coordinate first. The basis vertices and unit values are

$$ I=(8,60,62,84,275,492,495,519,545,578,793),\qquad g=(1,-1,1,1,-1,1,-1,-1,1,-1,1). $$

An admissible witness has denominator and numerator coefficient vectors, with the constant coefficient first,

$$ b=(1,1,1,32,1,1,1,1,1,1,1),\qquad a=(119,139,-389,1048,-273,-165,343,-117,-185,11,-89). $$

For every cube vertex, its affine values satisfy $|A(x)|\geq B(x)\gt0$. At the selected basis vertices, $A(x)=g(x)B(x)$. At vertex $91$, the label is negative.

For arbitrary coefficients satisfying the same basis equations, the additional unit-gap inequality at vertex $91$ implies

$$ b_3\geq7b_0+2b_1+b_4+3b_5+6b_6+4b_7+4b_8+3b_9+2b_{10}. $$

Nonnegativity of the remaining coefficients immediately gives the claimed factor eight. The Lean proof derives this consequence from the actual basis equations, without assuming an interpolating matrix is nonsingular. A separate declaration proves basis injectivity.

## Exact computations and their scope

The exploratory search used floating-point linear programming. Its output is not a proof. The separate script `check_boundary_balance_exact.py` reconstructs the Boolean basis matrix over the rationals and verifies the complete primal and dual certificates, including every cube inequality, with exact rational arithmetic.

For three ten-variable branches, the exact maxima of the normalized constant coefficient over the closed nonnegative coefficient cone are $1/6$, $1/7$, and $1/8$. Each branch also has a separately verified strictly positive coefficient witness. The exact certificates are in `boundary-balance-n10-exact.json`. The supremum statement is a finite exact computation; the Lean declaration above verifies the upper bound and a genuine positive witness for the last branch.

The searches `search_boundary_balance.py` and `search_triangular_balance.py` explore whether much stronger imbalance is possible. No asymptotic conclusion is justified by these finite searches.

## Verification

`lake build HeadComplexity.Research.FixedBasisBalanceObstruction` succeeded, with 3,226 build jobs. `AuditFixedBasisBalance.lean` prints the transitive axioms of all nine theorem declarations. They use only `propext`, `Classical.choice`, and `Quot.sound`. The original model and worst-case complexity definitions are unchanged.
