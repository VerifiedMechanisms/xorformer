# Many regular positive fibers of a full single-head table

## Statement

Let $d\geq3$, $k\geq1$, $n=d+k$, and $q=2^d-1$. Consider the full positive-denominator, arbitrary-affine-numerator single-head family

$$ F_{a,u,b}(z)=\frac{a+u\cdot z}{1+b\cdot z},\qquad b\in(0,\infty)^n. $$

There are $2n+1$ fixed real linear functionals of its Boolean table and one fixed vector of observation values whose fiber contains at least $q^k$ distinct isolated regular points in the full $2n+1$ dimensional parameter domain. Every resulting table is strictly positive on the entire cube and is an actual admissible head. The points also give distinct tables and locally embedded table images.

This is a complete written construction, with eight Lean-checked algebraic ingredients and an independent exact rational replay. It does not prove either requested asymptotic lower bound. The observations mix cube entries; they are not the manuscript's individual coordinate sign predicates.

## Rational interpolation functions

Put $m=2^d=q+1$ and define

$$ P(t)=\prod_{r=1}^q(t-r),\qquad D(t)=\prod_{j=1}^m(t+j),\qquad E(t)=\prod_{j=1}^q(t+j). $$

The proper rational functions

$$ R(t)=\frac{P(t)}{D(t)}=\sum_{j=1}^m\frac{\lambda_j}{t+j},\qquad Q(t)=\frac{E(t)-P(t)}{2E(t)}=\sum_{j=1}^q\frac{\mu_j}{t+j} $$

have explicit residues

$$ \lambda_j=\frac{P(-j)}{\prod_{\ell\neq j,1\leq\ell\leq m}(\ell-j)},\qquad \mu_j=-\frac{P(-j)}{2\prod_{\ell\neq j,1\leq\ell\leq q}(\ell-j)}. $$

Their partial-fraction identities follow by multiplying by the respective denominators and evaluating at every simple pole. The numerator of $Q$ has degree at most $q-1$ because the leading terms cancel. At each $r\in\lbrace1,\ldots,q\rbrace$,

$$ R(r)=0,\qquad R'(r)=P'(r)/D(r)\neq0,\qquad Q(r)=1/2. $$

## Anchor observations

Write $z=(y,x)$ with $d$ anchor bits and $k$ selector bits. At every constructed point prescribe anchor slopes $B_j=2^j$, indexed by $0\leq j\lt d$, numerator constant $a=1$, and anchor numerator coefficients zero.

Choose a connected graph on the anchor indices with exactly $d$ edges and an odd cycle: take the triangle on indices zero, one, and two, and join each remaining index to zero. Observe the table at the origin, every anchor singleton, and every anchor pair corresponding to an edge. Prescribe the values

$$ F(0)=1,\qquad F(e_j)=\frac1{1+B_j},\qquad F(e_i+e_j)=\frac1{1+B_i+B_j}. $$

There are $1+2d$ such observations. Their Jacobian in the $1+2d$ variables consisting of the numerator constant, anchor numerator coefficients, and anchor slopes is nonsingular at the prescribed anchor point.

**Proof.** A vector in the Jacobian kernel has $\delta a=0$ from the origin observation. Each singleton gives $\delta u_j=\delta b_j/(1+B_j)$. Substitute these identities into the pair differential. The zero pair differential becomes

$$ \frac{B_j}{1+B_i}\delta b_i+\frac{B_i}{1+B_j}\delta b_j=0. $$

Set $v_j=\delta b_j/(B_j(1+B_j))$. Each edge gives $v_i+v_j=0$. The odd cycle forces its vertex values to zero; connectivity forces all remaining values to zero. Thus every $\delta b_j$ and $\delta u_j$ is zero. The square Jacobian is injective, hence invertible. $\blacksquare$

These observations depend on no selector parameter. This fact will make the full Jacobian block triangular.

## Selector observations

For $1\leq j\leq m$, let $y(j)$ be the $d$-bit binary representation of $j-1$. The anchor denominator contribution is $1+\sum_a B_a y(j)_a=j$. For each selector index $i$ define two fixed linear functionals on arbitrary cube tables:

$$ L_i(V)=\sum_{j=1}^m\lambda_j V(y(j),e_i),\qquad M_i(V)=\sum_{j=1}^q\mu_j V(y(j),e_i). $$

Prescribe $L_i(F)=0$ and $M_i(F)=1$. Once the anchor parameters have their prescribed values, write $t_i$ for the selector slope and $v_i$ for its numerator coefficient. The observed values are exactly

$$ L_i(F)=(1+v_i)R(t_i),\qquad M_i(F)=(1+v_i)Q(t_i). $$

Consequently every choice

$$ t_i\in\lbrace1,\ldots,q\rbrace,\qquad v_i=1\quad(1\leq i\leq k) $$

satisfies the same full observation vector. Its two-by-two selector Jacobian, with columns ordered as $v_i,t_i$, is

$$ J_i=\begin{pmatrix}0&2R'(t_i)\cr 1/2&2Q'(t_i)\end{pmatrix},\qquad \det J_i=-R'(t_i)\neq0. $$

Different selector observations involve different selector parameters. Their derivatives in anchor parameters need not vanish, but the reverse derivatives do vanish. Therefore the full $2n+1$ square Jacobian is block lower triangular, with the invertible anchor Jacobian and these invertible two-by-two blocks on its diagonal. It is invertible at all $q^k$ parameter points. The inverse-function theorem makes each point isolated in this observation fiber and shows that the head-table map is locally an embedding there.

## Positivity, distinctness, and robustness

At the constructed points the complete score is

$$ F_t(y,x)=\frac{1+\sum_i x_i}{1+\sum_j2^j y_j+\sum_i t_i x_i}. $$

Its numerator and denominator are strictly positive on every Boolean input. Every slope is strictly positive, so the existing positive-affine-ratio realization gives an actual head with the manuscript's unrestricted real parameters and embedding dimensions. At a selector singleton with all anchors zero, the score is $2/(1+t_i)$, so different parameter tuples give different complete tables.

There are finitely many grid points. Choose disjoint parameter neighborhoods around them on which all slopes and cube scores stay positive. The inverse-function theorem gives an open observation neighborhood at each point; intersect these finitely many neighborhoods. Every observation vector in that common open set has a regular positive solution in every parameter neighborhood. Thus the multiplicity is not confined to one exceptional observation vector.

For $d=k$ and $n=2d$, the logarithm of this number is

$$ \log_2(q^k)=d\log_2(2^d-1)=(1/4+o(1))n^2. $$

This rules out a bound of $2^{O(n\log n)}$ for every regular positive fiber of arbitrary linear observations of the full single-head table. It strengthens the [earlier positive-grid construction](positive-functional-grid.md) by allowing all original numerator and denominator coordinates to vary and by certifying regularity of a square observation system and distinct full tables. It still gives only positive Boolean labels. It does not refute a bound specific to coordinate sign predicates or establish a lower bound for arbitrary Boolean functions.

## Verification scope

`FullHeadLinearFibers.lean` proves the pair differential factorization, the odd-cycle kernel argument, the selector determinant identity, the seven exact interpolation roots and their nonzero derivatives, a rational inverse for the anchor Jacobian, and positivity of the general displayed table. Its eight declarations use only standard foundational axioms. The general partial-fraction family, its block Jacobian, the inverse-function theorem, and the actual-head realization are written deductions above.

The independent script `verify_full_head_linear_fibers.py` checks all 343 points for three anchor bits and three selector bits. It verifies 21,952 positive cube values, distinctness of all 343 tables, 2,058 selector observation equalities, and nonsingularity of every block Jacobian. It computes every full observation Jacobian directly from the original head formula and checks the block structure; three additional full determinants agree with the factored values. The anchor Jacobian determinant is $1/1587600$. These finite checks support the stated construction; they are not evidence of an asymptotic Boolean lower bound.
