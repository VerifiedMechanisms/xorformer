# Mixed Binary Evaluation Fibers Can Have Full Parameter Rank

## Statement

For every $n\geq18$ there is a normalized three-head score

$$ S(x)=1+\sum_{h=1}^3\frac{u_h\cdot x}{1+b_h\cdot x},\qquad b_{hi}\gt0, $$

and $6n$ distinct nonzero Boolean vertices with the following properties. The score equals $+1$ on $6n-1$ selected vertices and $-1$ on the remaining vertex. The square Jacobian of these selected evaluations in all $6n$ numerator and denominator slopes is invertible.

This is an exact-model counterexample to a general rank-defect assertion for mixed binary evaluation targets. It is not a worst-case head lower bound. The retained point is not a numerator-norm minimum, and it does not satisfy unit-margin constraints on the whole cube.

## Eighteen-bit certificate

The explicit arrays in `integer-binary-fiber-18.json` specify $b_{hi}$ and integers $U_{hi}$, with $u_{hi}=U_{hi}/3$, together with 108 vertices and their labels. Vertices are encoded as $v=\sum_{i=0}^{17}2^i x_i$. The selected score in row 53, counting from zero, is $-1$; the other 107 selected scores are $+1$.

All denominator slopes are positive integers. Writing $B_h=1+b_h\cdot x$ and $A_h=u_h\cdot x$, the derivative entries are

$$ J_{x,u_{hi}}=\frac{x_i}{B_h(x)},\qquad J_{x,b_{hi}}=-\frac{x_iA_h(x)}{B_h(x)^2}. $$

Multiply row $x$ by $3\prod_{h=1}^3B_h(x)^2$, a positive integer, obtaining an integer matrix $M$. The independent Fraction-based verifier checks every score exactly and checks inverse matrices modulo two separately tested primes. It obtains

$$ \det M\equiv9\pmod{101},\qquad \det M\equiv5609\pmod{65537}. $$

Either nonzero reduction proves $\det M\neq0$ over the integers. The positive row scaling then proves $\det J\neq0$ over the rationals and the reals. The exact matrices and inverse modulo 101 are retained in `integer-binary-fiber-matrices.json`.

For the six vertices

$$ 217097,208981,67975,20555,32287,89157, $$

the old coordinate zero is one and the selected labels are all positive. Restrict $M$ to these rows and the six columns for the three numerator and three denominator coefficients of coordinate zero. The resulting matrix has determinant 86 modulo 101. Since its row scalings are nonzero, the corresponding six by six rational derivative matrix $C$ is invertible.

## Extension to all larger dimensions

For each new input coordinate, copy the three numerator and three denominator coefficients of the old coordinate zero. Extend every original selected vertex with zeros in the new coordinates.

For each new coordinate and each of the six displayed vertices, add the vertex obtained by changing old coordinate zero to zero, putting one in that new coordinate, and putting zero in every other new coordinate. Copying the coefficients preserves all three numerators and denominators at this vertex. Its score therefore remains $+1$.

All selected vertices are distinct. There are $108+6(n-18)=6n$ of them, and exactly one has score $-1$. Order old samples and old parameters first, followed by the six samples and six parameters for each new coordinate. The resulting Jacobian is block lower triangular, with diagonal blocks $J,C,\ldots,C$. Thus

$$ \det J_n=\pm\det J\cdot(\det C)^{n-18}\neq0. $$

This proves the theorem. $\blacksquare$

## Why this is not a minimum certificate

For the squared numerator norm $g=\sum_{h,i}u_{hi}^2$ and selected constraints $y_xS(x)\geq1$, an interior constrained local minimum would have nonnegative multipliers satisfying

$$ J^{\top}\mathrm{diag}(y)\lambda=\nabla g. $$

The selected constraint gradients are independent, so these multipliers, if they exist, are unique. Exact fraction-free elimination and a direct rational substitution check give 57 positive and 51 negative coordinates in the unique signed dual. None is zero. Consequently the retained point cannot be such a local minimum. Indeed, choose a negative coordinate of the signed dual and use the inverse evaluation map to increase only its signed constraint; the directional derivative of $g$ is negative while every selected constraint remains feasible for a sufficiently small positive displacement.

There is also an explicit failure of the full-cube unit-margin condition:

$$ S(1,0,\ldots,0)=-\frac7{30},\qquad |S(1,0,\ldots,0)|\lt1. $$

The dual computation and this exact vertex value are retained in `integer-binary-dual-checks.json`. Neither a failed numerical search for positive multipliers nor this particular negative dual proves that positive multipliers are impossible in general. The more restrictive norm-minimization route remains blocked at that unproved step.

## Verification scope

`verify_integer_binary_fiber.py` independently checks exact scores, both modular inverse identities, and the cloning minor. `verify_integer_binary_dual.py` checks the unique signed dual by exact arithmetic.

`IntegerBinaryData.lean`, `IntegerBinaryFinite.lean`, and `IntegerBinaryFiber.lean` encode the finite certificate and check its scores and nonsingular rational Jacobian. The analytic derivative interpretation, cloning extension, and local inverse-map argument are the written proofs above. No asymptotic head-complexity statement follows, and the original model and target are unchanged.
