# Full Parameter Rank at Coordinate Zeros

## Statement

For every $n\geq16$, there are three admissible heads with strictly positive denominator slopes and a set of $6n$ distinct Boolean inputs such that the normalized score is zero at every selected input and the Jacobian of these evaluations with respect to all $6n$ numerator and denominator slopes is invertible.

Consequently, these $6n$ inputs are shattered by three-head scores in an arbitrarily small parameter neighborhood of the construction. This auxiliary result does not imply the requested asymptotic lower bound. It rules out the proposed mechanism that sufficiently many common coordinate zeros always force a rank defect.

## An exact base certificate

Use

$$ S(x)=1+\sum_{h=1}^3\frac{u_h\cdot x}{1+b_h\cdot x}. $$

The file `integer-zero-fiber-16.json` specifies three positive integer denominator vectors, three integer numerator vectors divided by three, and 96 distinct nonzero vertices of the sixteen-bit cube. It is part of this theorem's explicit finite construction. Vertices use the encoding $v=\sum_{i=0}^{15}2^i x_i$.

The independent verifier `verify_integer_zero_fiber.py` checks every selected score using rational arithmetic. All 96 scores are exactly zero. It forms the rational Jacobian from

$$ \frac{\partial S(x)}{\partial u_{hi}}=\frac{x_i}{B_h(x)},\qquad \frac{\partial S(x)}{\partial b_{hi}}=-\frac{x_i A_h(x)}{B_h(x)^2},\qquad B_h(x)=1+b_h\cdot x,\quad A_h(x)=u_h\cdot x. $$

All matrix denominators are invertible modulo the prime 65521. The verifier checks primality and obtains

$$ \det J\equiv47539\pmod{65521}. $$

Therefore the rational determinant is nonzero, and hence so is the determinant over the reals. This inference uses reduction of rational numbers whose denominators are coprime to the prime; it does not identify a floating-point determinant with an exact value.

The six vertices

$$ 305,3479,997,1359,1429,1445 $$

all have coordinate zero equal to one. On these vertices form the six by six matrix whose row at $v$ is

$$ C_v=\left(\frac1{B_1(v)},\frac1{B_2(v)},\frac1{B_3(v)},-\frac{A_1(v)}{B_1(v)^2},-\frac{A_2(v)}{B_2(v)^2},-\frac{A_3(v)}{B_3(v)^2}\right). $$

The same independent verifier gives

$$ \det C\equiv20987\pmod{65521}, $$

so this matrix is also invertible over the reals. The retained report is `integer-zero-fiber-verification.json`.

## Extension by cloning one input coordinate

Let $n=16+m$. Retain the old coefficients. For each new coordinate $j$, set

$$ b_{hj}=b_{h0},\qquad u_{hj}=u_{h0}\qquad(1\leq h\leq3). $$

These new denominator slopes are strictly positive. Extend each of the 96 original sample vertices by zero in every new coordinate.

For each new coordinate $j$ and each of the six displayed vertices $v$, add a sample as follows: replace the old coordinate zero of $v$ by zero, set new coordinate $j$ to one, and set every other new coordinate to zero. The numerator and denominator values at this sample equal their old values at $v$. Hence the score is again exactly zero.

There are $96+6m=6n$ distinct samples. Order the old rows and old parameters first, then the six new rows and six new parameters for each new coordinate. The Jacobian is block lower triangular. Its first diagonal block is $J$, and every subsequent diagonal block is $C$. Indeed, the old samples have every new coordinate zero, and a new sample for coordinate $j$ has every other new coordinate zero. Its derivatives in the six parameters belonging to $j$ are exactly the row $C_v$.

Thus, up to the sign of the chosen row and column permutations,

$$ \det J_n=\det J\cdot(\det C)^m\neq0. $$

This proves the construction for every $n\geq16$. By the inverse function theorem, the selected evaluation map contains an open neighborhood of zero. Each of the finitely many strict sign vectors on the selected inputs occurs in that neighborhood. Positivity of all denominator slopes persists under sufficiently small parameter perturbations, so the representations remain admissible. $\blacksquare$

## Audit scope

The two modular nonvanishing computations and all base zero evaluations have been independently checked. The extension and local shattering argument are the written proof above. No Lean declaration for this theorem is asserted.

The construction supplies $6n$ sign tests for three heads, not all $2^n$ sign tests. It neither establishes nor refutes an upper bound of order $2^n/n^2$ for arbitrary Boolean functions. The selected research target remains open in this run.
