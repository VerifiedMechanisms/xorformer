# Boolean projection ghosts and their exact lattice ideal

## Scope

This note studies finite signed constant-residue collisions along a common denominator pencil. It is a written algebraic analysis, not an unrestricted capacity theorem. Numerator-dependent higher jets require further arguments. The final ideal theorem below also covers arbitrary real direction coordinates, without giving a quantitative decomposition.

Let $w_h\in\mathbb Z^n$ and $c_h\in\mathbb R$. A Boolean projection ghost satisfies

$$ \sum_h c_h \mathbf1_{\lbrace w_h\cdot x=t\rbrace}=0\qquad\text{for every }x\in\lbrace0,1\rbrace^n\text{ and every }t\in\mathbb Z. $$

Equivalently, for every Boolean $x$, the signed measure on projected values is zero. This implies

$$ \sum_h\frac{c_h}{a+s(w_h\cdot x)}=0 $$

whenever all denominators are defined. Conversely, the rational identity for all sufficiently small $s$, with $a\neq0$, implies the projection condition by partial fractions, or by the first finitely many power moments and Vandermonde invertibility.

After a common translation of all exponent vectors, assume they are nonnegative and form

$$ P(z)=\sum_h c_h\prod_i z_i^{w_{h,i}}. $$

The projection condition is equivalent to $P(z_i=t^{x_i})=0$ for every Boolean $x$ and every positive $t$. A common translation only multiplies each projected generating polynomial by a monomial, so it preserves the condition.

## Exact ideal theorem

Put $y_i=z_i-1$. The vanishing ideal over $\mathbb R$ of the union of Boolean diagonal lines

$$ \mathcal L_n=\lbrace t x:t\in\mathbb R,\ x\in\lbrace0,1\rbrace^n\rbrace $$

is

$$ I(\mathcal L_n)=\left\langle y_i y_j(y_i-y_j):i\lt j\right\rangle. $$

**Proof.** Every displayed generator vanishes on every such line. In the quotient by these generators, the relation $y_i^2y_j=y_i y_j^2$ moves one exponent between any two coordinates already present in a monomial. Hence a degree $D$ monomial with nonempty support $S$ is congruent to

$$ m_{D,S}=y_{\min S}^{D-|S|+1}\prod_{j\in S\setminus\lbrace\min S\rbrace}y_j. $$

For each degree, these monomials span the quotient. On a Boolean diagonal line indexed by a set $T$, their evaluations are

$$ m_{D,S}(t\mathbf1_T)=t^D\mathbf1_{\lbrace S\subseteq T\rbrace}. $$

Suppose a linear combination of these normal forms vanishes on all the lines. For each fixed $T$, its coefficients as a polynomial in $t$ vanish. At each degree, the resulting equations are $\sum_{S\subseteq T} a_{D,S}=0$. Induction on $|T|$, or Boolean zeta inversion, gives every $a_{D,S}=0$. The constant term vanishes by evaluating at the origin. Thus the spanning normal forms are linearly independent under evaluation, proving equality of the ideals. In particular the displayed ideal is radical. $\blacksquare$

The homogeneous degree $D$ quotient dimension is $1$ for $D=0$, and for $D\geq1$ it is

$$ \sum_{k=1}^{\min(n,D)}\binom nk. $$

This is a statement about the coordinate ring of the input-line arrangement. It does not say that the dual spaces spanned by $(w\cdot x)^D$ form a subalgebra of polynomials in $w$.

## Six-point generators

In the original variables each generator is

$$ g(z_i,z_j)=(z_i-1)(z_j-1)(z_i-z_j)=z_i^2z_j-z_i z_j^2-z_i^2+z_j^2+z_i-z_j. $$

Consequently every integer ghost is a polynomial linear combination of translates of this six-point two-coordinate ghost. The theorem includes signed coefficients and places no bound on their size.

This is an algebraic generation theorem. It does not bound the number of generator translates, the number of intermediate support points, or the coefficient mass. Those bounds are essential if this route is to supply constant head overhead.

## A sharp obstruction to unit-step sparse division

For any positive integer $M$, the six-term polynomial $g(z_1^M,z_2^M)$ is another ghost. Since the two-variable ghost ideal is principal, its quotient by the unit generator is uniquely

$$ Q_M(z_1,z_2)=\left(\sum_{a=0}^{M-1}z_1^a\right)\left(\sum_{b=0}^{M-1}z_2^b\right)\left(\sum_{c=0}^{M-1}z_1^{M-1-c}z_2^c\right). $$

All coefficients of $Q_M$ are nonnegative. Its coefficient sum is $M^3$, and its support is the lattice hexagon

$$ \lbrace(u,v):0\leq u,v\leq2M-2,\ M-1\leq u+v\leq3M-3\rbrace. $$

The two excluded corner triangles each contain $M(M-1)/2$ lattice points, so

$$ |\mathrm{supp}Q_M|=(2M-1)^2-M(M-1)=3M^2-3M+1. $$

Any expression of this ghost as a sum of scalar monomial translates of the unit generator must therefore contain at least $3M^2-3M+1$ nonzero translates after like terms are combined. The input has only six support points. Thus no bound in terms of input support alone holds for this fixed generator dictionary.

Allowing arbitrary step sizes removes this particular obstruction: $g(z_1^M,z_2^M)$ is itself a single enlarged six-point ghost. The calculation rules out only the unit-step division argument.

## Original-support peeling also fails

A second tempting claim is that every ghost contains a smaller six-point ghost on its own support. It is false. For distinct generic positive steps $a,b,c$, consider

$$ R=(z_1^a-1)(z_2^c-1)(z_1^b-z_2^b). $$

It has eight distinct terms and zero row, column, and diagonal sums. For example take $(a,b,c)=(1,3,7)$. Its row-column incidence graph consists of two four-cycles: rows $b,a+b$ with columns $0,c$, and rows $0,a$ with columns $b,b+c$. Any nonzero signed subconfiguration with zero row and column sums must contain an entire one of those cycles. Neither individual cycle has zero diagonal sums. Hence the full eight-point configuration is a circuit for the three projection maps and contains no six-point subghost.

Auxiliary points can repair this obstruction algebraically. If

$$ M(u,v)=(z_1^u-1)(z_2^v-1)-(z_1^v-1)(z_2^u-1), $$

then direct expansion gives

$$ R=M(b+c,a)-z_1^b M(c,a)-M(b,a). $$

Each summand is a translated generalized six-point ghost. Thus the example rules out support-preserving six-point peeling, but does not rule out a linear-size decomposition using new points.

## Extension to arbitrary real direction coordinates

The ideal statement extends beyond integer coordinates. Let $G\subseteq\mathbb R$ be the additive subgroup generated by the finitely many coordinates of the direction points. This is a finitely generated torsion-free abelian group, so choose a basis $\alpha_1,\ldots,\alpha_r$ over $\mathbb Z$. Write each direction coordinate as an integer combination of this basis. Introduce variables $z_{i,q}$, one for input coordinate $i$ and group-basis element $q$. A common monomial translation makes the resulting Laurent polynomial ordinary.

Equality of real projected values is equivalent to equality of the corresponding integer exponent vectors, because the group basis is independent over $\mathbb Z$. Thus the ghost condition is the polynomial vanishing condition under every substitution that sends row $i$ either to $(1,\ldots,1)$ or to one common vector of indeterminates.

With $y_{i,q}=z_{i,q}-1$, the relevant locus is the union of subspaces

$$ y_{i,q}=x_i t_q,\qquad x\in\lbrace0,1\rbrace^n,\quad t\in\mathbb R^r. $$

Its ideal is generated by the quadrics and cubics

$$ y_{i,q}y_{j,r}-y_{i,r}y_{j,q},\qquad y_{i,q}y_{j,r}(y_{i,s}-y_{j,s}). $$

**Proof.** Every displayed generator vanishes. The quadratic relations redistribute column labels among monomial factors while preserving their row multiplicities and column multidegrees. The cubic relations move an excess row factor from one present row to another present row. Hence a monomial of degree $D$ has a canonical representative determined only by its nonempty row support $S$ and column multidegree $\beta$ with $|\beta|=D$. Such a representative exists exactly when $|S|\leq D$.

On the subspace indexed by $T\subseteq[n]$, its evaluation is $\mathbf1_{\lbrace S\subseteq T\rbrace}t^\beta$. Polynomial coefficient comparison in $t$ followed by Boolean zeta inversion proves that all these canonical representatives are independent. The same spanning-and-independence argument as above proves the ideal equality. $\blacksquare$

After undoing $y=z-1$, a quadratic generator is a six-point exchange ghost and a cubic generator has at most eight points. Both change only two input coordinates. Therefore every finite real constant-residue ghost is an algebraic sum of translated two-coordinate ghosts with at most eight points each.

This assertion allows arbitrarily many translated generators. The translations and group basis can also produce auxiliary real direction vectors outside the positive orthant. The proof does not give a decomposition with admissible auxiliary heads, bounded support, bounded coefficients, or controlled jets.

## Hyperplane-cover hypotheses

For a ghost with distinct support points and nonzero coefficients, each point must have another point with the same projection in every Boolean direction. Its pair-difference hyperplanes therefore cover the Boolean cube. This does not satisfy the nondegeneracy hypothesis in the strong recent hyperplane-cover theorem: at a unit vertex $e_i$, every homogeneous hyperplane containing that vertex has zero coefficient in coordinate $i$.

The theorem of Sauermann and Xu requires, for each vertex and each coordinate, a containing hyperplane with a nonzero coefficient in that coordinate. Its linear lower bound cannot be imported into this homogeneous difference-cover argument. See [the primary paper, Theorem 1.1](https://arxiv.org/html/2507.00773v1).

Passing to a minimal essential cover also needs care. A minimal subcover may discard all hyperplanes involving some coordinates, even when the original point configuration depends on those coordinates. Moreover a support lower bound polynomial in $n$ would be vacuous at the exponentially large critical head widths unless coupled to a decomposition into small components.

## Remaining lemma

A usable repair route would need a decomposition of every relevant real, positive-direction collision into $O(H)$ controlled atoms, with admissible auxiliary directions and quantitative control of the first nonzero jets. The lattice ideal theorem does not prove this. The arbitrary-real extension uses an additive-group basis whose rank and coefficient sizes are uncontrolled; it supplies no replacement quantitative estimate.

Even a linear-size exact ghost decomposition alone would not establish a margin bound: exact zero relations and nearly vanishing nonzero scores must be distinguished, and the full truth table must survive the perturbation. These are the first additional requirements beyond the algebraic statement.

## Verification boundary

The ideal equalities and their arbitrary-real extension are written proofs. They are not Lean declarations. The accompanying script `ghost_ideal_finite_check.py` checks generator-span ranks over the prime field with 1000003 elements for dimensions $(n,r)=(2,1),(3,1),(2,2),(3,2)$ in the listed finite degree ranges. It also checks the scaled quotient formulas for $1\leq M\leq12$ and verifies the eight-point circuit and three-hexagon identity by exact rational arithmetic. These computations support the algebraic audit but do not replace its general proof.
