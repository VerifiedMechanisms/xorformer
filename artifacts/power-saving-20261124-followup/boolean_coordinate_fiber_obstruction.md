# Actual Boolean coordinate fibers can contain different strict truth tables

## Statement and status

For every $n\geq6$, a fixed list of $4n+1$ Boolean input coordinates has a common evaluation fiber containing at least $2^{n-5}$ distinct two-head representations, modulo global head permutation. Every denominator has strictly positive coefficients. Every displayed point of the parameter fiber is regular and isolated locally, and the representations yield $2^{n-5}$ different full truth tables. Each displayed representation has full-cube relative margin exactly $1/151$.

The score identities, label distinction, margin calculation, and extension to general $n$ below are written proofs. The base-case nonsingularity uses an explicitly recorded exact integer determinant computation in [the certificate](boolean_coordinate_fiber_certificate.json), reproduced by [the standalone checker](verify_boolean_coordinate_fiber.py). It is a finite computation, not a kernel-checked declaration.

This refutes uniqueness of positive interpolation from a number of actual Boolean samples equal to the parameter dimension. It also refutes the claim that all branches in an actual-coordinate fiber necessarily have the same sign table. It does not refute an upper bound of the form $\exp(O(nH\log n))$ on relevant branch or label counts, and it gives no universally small-margin target.

## Six-bit base case

Number input coordinates from zero through five. Set

$$ c=-\frac{31}{60},\qquad w_1=(1,2,1,3,4,5),\qquad w_2=(2,1,2,3,4,5),\qquad S(x)=c+\frac{1}{1+w_1\cdot x}+\frac{1}{1+w_2\cdot x}. $$

Let $S'$ be obtained by swapping only the first-coordinate weights: replace the two vectors by

$$ w'_1=(2,2,1,3,4,5),\qquad w'_2=(1,1,2,3,4,5). $$

The ratios have constant numerator one, positive constant denominator one, and all slopes positive. They are genuine original heads by `FracAtom.ofPositiveAffineRatio`.

If $x_0=0$, the two scores agree immediately. If $x_1=x_2$, the two denominator contributions from coordinates one through five agree before adding the zeroth coordinate. Swapping the zeroth-coordinate weights therefore only exchanges two reciprocal summands. Hence

$$ S(x)=S'(x)\quad\text{whenever }x_0=0\text{ or }x_1=x_2. $$

There are $48$ such vertices. In contrast,

$$ S(1,1,0,0,0,0)=-\frac1{60},\qquad S'(1,1,0,0,0,0)=\frac1{60}. $$

At $(1,0,1,0,0,0)$ the two signs are reversed.

## An actual-coordinate nonsingular square minor

Encode a Boolean vertex by its six-bit binary integer with $x_0$ most significant. Choose the following $25$ codes:

$$ 0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16,17,18,19,32,33,34,35,56,57. $$

All are in the $48$-point agreement set. Use the standard effective parameter chart

$$ F_{b,u,w}(x)=b+\sum_{h=1}^2\frac{u_h\cdot x}{1+w_h\cdot x}. $$

Its dimension is $1+4n$, which is $25$ in the base case. At the displayed representations, $b=c+2=89/60$ and $u_h=-w_h$. The original two reciprocal heads give this chart because $1/(1+w_h\cdot x)=1-(w_h\cdot x)/(1+w_h\cdot x)$.

Write $B_h=1+w_h\cdot x$. In the parameter order $b,u_1,w_1,u_2,w_2$, the Jacobian row is

$$ \left(1,\frac{x}{B_1},\frac{(B_1-1)x}{B_1^2},\frac{x}{B_2},\frac{(B_2-1)x}{B_2^2}\right). $$

Multiply this row by the positive integer $B_1^2B_2^2$. The resulting integer row is

$$ \left(B_1^2B_2^2,xB_1B_2^2,(B_1-1)xB_2^2,xB_2B_1^2,(B_2-1)xB_1^2\right). $$

For the selected rows, the determinant of this $25\times25$ integer matrix is, at each of the two displayed parameter points,

$$ 21707597330497142784000000000000\neq0. $$

The checker verifies this identity with exact fraction-free integer elimination, records every pivot and row swap, and also checks all $64$ scores with exact rational arithmetic. Since all row-scaling factors are positive, the original real Jacobian is nonsingular. The inverse function theorem gives locally isolated regular inverse branches. In fact, sufficiently small perturbations of the $25$ measured values retain both local branches, all denominator coefficients remain positive, and the two distinct full sign tables persist by their positive strict margins.

## Independent new selector coordinates

Keep the two fixed address coordinates $x_1,x_2$ and the three heavy coordinates $x_3,x_4,x_5$. Treat $x_0$ and each new coordinate $x_i$, $i\geq6$, as selectors. For each selector independently choose a bit $\sigma_i\in\lbrace0,1\rbrace$ and set its two weights to

$$ (w_{1,i},w_{2,i})=(1+\sigma_i,2-\sigma_i). $$

The address weights remain $(2,1)$ and $(1,2)$, while the heavy weights are $(3,3)$, $(4,4)$, and $(5,5)$. Keep $c=-31/60$ and both reciprocal numerators equal to one. There are $n-5$ selectors, hence $2^{n-5}$ parameter choices.

Embed the $25$ base sample vertices with all new coordinates zero. For each new selector $i$, add four sample vertices: turn on only that selector among all light coordinates, set $x_5=0$, and let $(x_3,x_4)$ take all four Boolean values. The common heavy contribution is then $z\in\lbrace0,3,4,7\rbrace$. At these samples the reciprocal sum is

$$ \frac1{z+2}+\frac1{z+3}, $$

independently of every selector bit. Thus the resulting $25+4(n-6)=4n+1$ actual coordinate values are identical for all $2^{n-5}$ branches.

Order the parameters and the observations with the base blocks first and each added selector block thereafter. The Jacobian is block lower triangular: a base row has zero derivatives in every new selector coordinate, and a row for selector $i$ has zero derivatives in all other new selector blocks. The base diagonal block is nonsingular by the certificate above.

Each new $4\times4$ diagonal block has rows at $z=0,3,4,7$. Column operations reduce it, up to exchanging the two head blocks, to the evaluation matrix of

$$ \frac1{z+2},\qquad \frac1{(z+2)^2},\qquad \frac1{z+3},\qquad \frac1{(z+3)^2}. $$

This matrix is nonsingular. Indeed, a linear combination vanishing at those four distinct points becomes a polynomial of degree at most three after multiplication by $(z+2)^2(z+3)^2$. That polynomial must vanish identically. Evaluating at $-2$ and $-3$ first removes the double-pole coefficients; after division by $(z+2)(z+3)$, evaluation at those same points removes the two simple-pole coefficients. All coefficients are zero.

Therefore the full Jacobian is nonsingular at every branch. No two displayed branches are global head permutations, because the weight of the first head at the fixed address coordinate $x_1$ is always two and that of the second head is always one.

## Distinct labels and a uniform relative margin

For any selector $i$, evaluate at the vertex $e_i+e_1$. If $\sigma_i=0$, the denominators are $4,4$ and the score is $-1/60$. If $\sigma_i=1$, they are $5,3$ and the score is $1/60$. Thus the label at this vertex reads exactly $\sigma_i$. All $2^{n-5}$ full truth tables are distinct.

The strictness and margin can be checked without enumerating the enlarged cube. If any heavy coordinate is on, both denominators are at least four, so the score is at most $-1/60$. Suppose all heavy coordinates are off, and let $r$ be the number of active light coordinates. For $r=0$ the reciprocal sum is two; for $r=1$ it is $5/6$. For $r=2$, the denominator pair is either $(3,5)$, $(4,4)$, or $(5,3)$, giving score $1/60$ or $-1/60$. For $r\geq3$, both denominators are at least four, again giving score at most $-1/60$.

Hence every absolute score is at least $1/60$, with equality attained. Each reciprocal head has full-cube norm exactly one, attained at the zero vertex. Consequently every displayed table has relative margin

$$ \frac{1/60}{31/60+1+1}=\frac1{151}. $$

The conclusion concerns different truth tables sharing selected exact score observations, with entirely admissible heads and a healthy margin. It supplies a genuine obstruction to uniqueness-based compression, while leaving the required quantitative branch bound and unrestricted head-complexity lower bound open.
