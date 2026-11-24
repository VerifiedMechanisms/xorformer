# The seven-variable feasible basis has exactly two continuations

## Statement

The previously checked seven-variable example has two open sets of admissible one-head parameters with the same eight actual unit-value sample contacts. Its nonuniqueness is exact, but its number of continuations is small: over all strictly positive denominator coefficient vectors, that fixed basis produces exactly two Boolean truth tables.

This statement is kernel checked as `HeadComplexity.GenericOneHeadBasisNonuniqueness.positiveBasisTables_card` in `formalization/HeadComplexity/Research/GenericOneHeadBranchCount.lean`.

## Exact finite argument

Use the integer matrix $T$, the eight sample points, and their prescribed signs from `GenericOneHeadBasisNonuniqueness.lean`. The unit sample equations force the numerator coefficient vector to be $a=Tb$. Here $b\in\mathbb R^8$ has strictly positive entries, and the affine denominator on the full cube is positive.

For a Boolean input $x\in\lbrace0,1\rbrace^7$, write $z(x)=(1,x_1,\ldots,x_7)$. Exact evaluation of all 128 integer rows $z(x)T$ shows that every row except one has coefficients of a single sign, with at least one nonzero coefficient. The exception is

$$ x^{\ast}=(0,0,1,0,0,0,1),\qquad z(x^{\ast})T=(1,0,0,-1,0,-2,2,-1). $$

Therefore the sign of $z(x)Tb$ is fixed whenever $x\neq x^{\ast}$ and $b\gt0$. At the exceptional input the sign can vary. The two previously checked positive vectors are

$$ b^{(0)}=(1,1,1,1,1,1,4,1),\qquad b^{(1)}=(1,1,1,1,1,3,1,1). $$

Their numerators have opposite signs at $x^{\ast}$. Both vectors lie in the previously proved open full-cube unit-gap feasible sets. Thus both tables occur, and no third table occurs. The Lean definition chooses the false label at a zero numerator; this convention creates no additional table. Restricting to strict full-cube representations or to the unit-gap feasible sets still gives exactly these two tables.

The proof `sign_fixed_outside_exceptional` checks the 128 rows and their inequalities over arbitrary positive real $b$, rather than relying on floating-point sampling. The declaration `positiveTable_eq_one_of_two_of_basis_values` also quantifies over arbitrary numerator refits satisfying the selected unit sample equations, using the checked full rank of the sample basis.

## What this resolves

The earlier example disproves uniqueness of continuation from a feasible actual basis. It does not disprove a small upper bound on the number of continuations. In particular, this example supplies only one bit of branching. A general bound for arbitrary bases, and its extension to many heads at the critical width, remain open.

The exploratory script `probe_one_head_feasible_branches.py` first suggested the two-table result by floating mixed-integer optimization. Its JSON output is retained as exploratory evidence only. The Lean proof is independent of the solver and its numerical infeasibility report.

## Verification

The module build completed successfully with 3227 jobs. The five declarations listed in `GenericBranchCountAudit.lean` use transitively only `propext`, `Classical.choice`, and `Quot.sound`. No original model definition was changed.
