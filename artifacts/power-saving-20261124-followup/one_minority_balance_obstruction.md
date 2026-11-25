# A one-minority unit basis forces denominator imbalance

## Exact finite statement

There is an actual affine basis of eleven vertices in the ten-dimensional Boolean cube, with ten prescribed values $+1$ and one prescribed value $-1$, for which a strictly positive original denominator and a full-cube unit gap exist, but every representation in the same fixed-label unit-basis branch satisfies

$$ 22b_0\leq\sum_{i=0}^{10}b_i. $$

Here the numerator and denominator are affine forms, all denominator coefficients are nonnegative for the upper bound, and $b_0$ is the constant coefficient. The supremum of $b_0/\sum_i b_i$ over strictly positive denominator coefficients in this branch is exactly $1/22$.

This is a fixed-basis statement. It does not bound the best margin after changing the unit contacts, and it does not contradict polynomial denominator balancing. It rules out a constant-denominator deformation even in the particularly simple case of one negative unit contact.

## Certificate

Index Boolean vertices by their ten-bit binary expansions, most significant bit first, and write $z(x)=(1,x_1,\ldots,x_{10})$. Define

$$ F(x)=(-5,-15,-2,-9,6,12,-14,-20,10,31,12)\cdot z(x),\qquad q=982. $$

The ten vertices

$$ 173,213,244,286,452,497,565,621,659,959 $$

have $F=0$, while $F(q)=2$. Together with $q$ their affine evaluation matrix has determinant $2$. The desired contact values are $+1$ at the first ten vertices and $-1$ at $q$.

For any affine denominator $B$, these contact equations uniquely force

$$ A(x)=B(x)-B(q)F(x). $$

Indeed this formula gives the prescribed values, and values on an affine basis determine an affine form uniquely. Set $f(x)=+1$ when $F(x)\leq0$, and $f(x)=-1$ when $F(x)\gt0$.

A strictly positive witness is

$$ b=(1,11,8,17,6,1,7,1,20,4,1),\qquad B(q)=74. $$

The resulting numerator is

$$ a=(371,1121,156,683,-438,-887,1043,1481,-720,-2290,-887). $$

Exact enumeration checks $f(x)A(x)\geq B(x)$ at all $1024$ cube vertices. The strictly positive constant and slopes give a genuine original `FracAtom` through `FracAtom.ofPositiveAffineRatio`.

## An exact dual upper bound

At a vertex with $F(x)=1$, negative unit feasibility gives

$$ B(q)-2B(x)\geq0. $$

Use the seven vertices

$$ (125,308,364,402,526,737,850) $$

with respective nonnegative multipliers

$$ (2,2,2,5,4,5,1). $$

All seven satisfy $F=1$. Adding these weighted inequalities and the nonnegativity terms $23b_5+17b_7+15b_{10}$ gives the exact identity

$$ \sum_x\lambda_x\bigl(B(q)-2B(x)\bigr)+23b_5+17b_7+15b_{10}=\sum_{i=0}^{10}b_i-22b_0\geq0. $$

No optimization solver or numerical tolerance is used in this conclusion.

The nonnegative boundary denominator

$$ b^{\ast}=(1,3,2,5,2,0,2,0,6,1,0) $$

has total mass $22$, constant coefficient $1$, and satisfies every full-cube unit inequality with the forced numerator. Convex combinations with the strictly positive witness retain all contact equations and inequalities. Their denominator coefficients are strictly positive and their normalized constant approaches $1/22$. Thus $1/22$ is the exact supremum for the original strictly positive branch. The endpoint itself has zero slopes and is used only in the closed cone, not claimed to be an admissible original head.

## Consequence for recursive constructions

The separately proved leaf-deletion lemma in `UnitGapLeafDeletion.lean` allows a denominator coefficient to be decreased when all contacts on its one-face have the same label. It explains why simply adjoining one coordinate and one new contact cannot create growing imbalance: the new coefficient is removable. The present example has only one negative contact, but that contact simultaneously uses enough coordinates to prevent this elementary simplification from reducing to a constant denominator.

A possible asymptotic obstruction would require a sequence of actual Boolean zero flats and minority vertices whose induced positive-weight inequalities force exponentially growing total weight. Arbitrary systems of inequalities with coefficients in $\lbrace-2,-1,0,1,2\rbrace$ are insufficient: the constraints must arise as the level-one set of a single affine form, and its zero set must contain an affine basis of a hyperplane. No such scalable construction is proved here.

## Verification status

`OneMinorityBalanceObstruction.lean` formalizes the original admissible witness, basis injectivity, full-cube inequalities, and the universal balance upper bound for every numerator and denominator satisfying the fixed contact equations. The exact standard-library checker `check_one_minority_balance.py` independently verifies the rational inverse matrix, all $1024$ inequalities, and the dual identity from `one-minority-balance-exact.json`.

The target build completed successfully with 3226 jobs. The transitive audit checked all 41 theorem declarations and found only `propext`, `Classical.choice`, and `Quot.sound`; six public `#print axioms` results are recorded in `one-minority-balance-public-axioms.txt`.

The initial search `search_rank_one_basis_balance.py` is floating exploration only. Its output is not used as a premise of the exact checker or Lean proofs. The supremum argument by convex combinations is written mathematics; the finite endpoint and upper inequality are kernel checked after the build recorded alongside this note.
