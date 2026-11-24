# Joint Quadrature Can Require Linearly Many Nodes

## Status and scope

This is a new obstruction to a proposed integral compiler. Even a score with two admissible original heads can force a common quadrature rule to use a number of nodes proportional to the input dimension. The nodes and weights may depend jointly on the entire score and on its target sign table. Arbitrary real weights, arbitrary real nodes, a new free bias, and an arbitrary recalibration of the second head do not remove the obstruction.

The rule must retain the first denominator direction and the original numerator functions. This result does not exclude choosing new product directions or jointly changing affine numerators. It is not a lower bound for unrestricted head complexity.

## Theorem

For every integer $m\geq1$, put $n=4m+2$. There are affine functions $B,r$ on $\lbrace0,1\rbrace^n$ such that all slopes of $B$ and $r$ are strictly positive, $B$ is strictly positive on the cube, and the two-head score

$$ S(x)=\frac1{B(x)}-r(x) $$

is strictly nonzero at every cube input. Nevertheless, whenever real numbers $d,\beta,w_1,\ldots,w_K,t_1,\ldots,t_K$ give a score

$$ Q(x)=d+\sum_{j=1}^K w_j e^{-t_jB(x)}-\beta r(x) $$

with the same strict signs as $S$ on the entire cube, one must have $K\geq m$.

The score $S$ is admissible in the exact original model. Its first atom has constant numerator and a denominator with strictly positive slopes. Its second atom has denominator $1$ and numerator $-r$, whose slopes are all strictly negative. No assumption about margin or bounded coefficients is used.

## Proof

### A nonsingular moment matrix

Index a square matrix of size $m+1$ by $0\leq i,j\leq m$, and define

$$ H_{ij}=\frac1{1+i+j}. $$

This matrix is positive definite. Indeed, for every nonzero real vector $v=(v_0,\ldots,v_m)$,

$$ v^\top H v=\int_0^1\left(\sum_{i=0}^m v_i u^i\right)^2du\gt0. $$

The polynomial inside the square is nonzero and hence is nonzero on some open subinterval. Thus $D_m=\det H\gt0$. An explicit alternative is the Cauchy determinant formula

$$ D_m=\frac{\prod_{0\leq i\lt j\leq m}(j-i)^2}{\prod_{i=0}^m\prod_{j=0}^m(1+i+j)}. $$

Choose a positive real number $\varepsilon$ such that

$$ \varepsilon\lt\min\left\lbrace\frac1{2(2m+1)},\frac{D_m}{2(m+1)!(m+1)2^m}\right\rbrace. $$

Every real matrix $M$ with $|M_{ij}-H_{ij}|\lt\varepsilon$ is nonsingular. To check this quantitatively, all entries of $H$ have absolute value at most one, and those of $M$ have absolute value at most two. Telescoping the product in each determinant term gives

$$ |\det M-\det H|\leq(m+1)!(m+1)2^m\varepsilon\lt D_m/2. $$

### Paired singleton queries

There are $2(2m+1)=n$ coordinates, indexed by pairs $(k,\sigma)$ with $0\leq k\leq2m$ and $\sigma\in\lbrace-1,+1\rbrace$. Let $e_{k,\sigma}$ denote the corresponding singleton input. Put

$$ s_k=1+k,\qquad r_{k,\sigma}=\frac1{1+k}+\sigma\varepsilon. $$

Choose $r_0$ in the open interval $(0,1/[2(2m+1)])$, subject to the finite exclusions specified below, and define

$$ B(x)=\frac12+\sum_{k=0}^{2m}\sum_{\sigma\in\lbrace-1,+1\rbrace}\left(k+\frac12\right)x_{k,\sigma},\qquad r(x)=r_0+\sum_{k=0}^{2m}\sum_{\sigma\in\lbrace-1,+1\rbrace}(r_{k,\sigma}-r_0)x_{k,\sigma}. $$

All slopes of $B$ are strictly positive, and $B(x)\geq1/2$ on the cube. Since $r_{k,\sigma}\gt1/[2(2m+1)]\gt r_0$, all slopes of $r$ are strictly positive as well.

At the paired singleton inputs,

$$ B(e_{k,\sigma})=1+k,\qquad S(e_{k,\sigma})=-\sigma\varepsilon. $$

It remains to choose $r_0$ so that $S$ never vanishes elsewhere. At an input with $q$ coordinates equal to one, the dependence of $r(x)$ on $r_0$ is affine with coefficient $1-q$. For $q\neq1$, the equation $S(x)=0$ therefore excludes at most one value of $r_0$. For $q=1$, the displayed singleton formula is already nonzero. The cube is finite, so deleting the finitely many forbidden values from the indicated open interval leaves an allowed choice. This proves the claimed strictness of $S$.

### Sign agreement forces a high-rank moment table

Suppose that $Q$ agrees with the strict signs of $S$, and write

$$ \phi(s)=\sum_{j=1}^K w_j e^{-t_js}. $$

The paired singleton signs require

$$ d+\phi(1+k)-\beta\left(\frac1{1+k}-\varepsilon\right)\gt0,\qquad d+\phi(1+k)-\beta\left(\frac1{1+k}+\varepsilon\right)\lt0. $$

Subtracting these inequalities shows $2\beta\varepsilon\gt0$, so $\beta\gt0$. Dividing by $\beta$ now gives

$$ \left|\frac{d+\phi(1+k)}{\beta}-\frac1{1+k}\right|\lt\varepsilon\qquad(0\leq k\leq2m). $$

Define $y_k=(d+\phi(1+k))/\beta$ and form the matrix $M_{ab}=y_{a+b}$ for $0\leq a,b\leq m$. By the preceding estimate and the determinant calculation, $M$ is nonsingular and has rank $m+1$.

On the other hand, set $z_j=e^{-t_j}$ and $a_j=w_je^{-t_j}/\beta$. Then

$$ y_k=\frac d\beta+\sum_{j=1}^K a_jz_j^k. $$

Consequently

$$ M=\frac d\beta\mathbf1\mathbf1^\top+\sum_{j=1}^K a_jv_jv_j^\top,\qquad v_j=(1,z_j,\ldots,z_j^m)^\top. $$

Its rank is at most $K+1$. Hence $m+1\leq K+1$, proving $K\geq m$. $\blacksquare$

## Consequence for joint Laplace quadrature

The reciprocal score has the integral representation

$$ S(x)=\int_0^\infty\left(e^{-tB(x)}-r(x)e^{-t}\right)dt. $$

Replacing this integral by any $K$ chosen nodes and weights, and even adding a new free bias, gives

$$ d+\sum_{j=1}^K w_j\left(e^{-t_jB(x)}-r(x)e^{-t_j}\right). $$

This is a special case of $Q$ with $\beta=\sum_jw_je^{-t_j}$. Therefore the theorem applies even when the nodes, weights, and bias are chosen jointly after seeing the entire target. Restricting nodes and weights to be nonnegative only makes the approximation class smaller.

The same obstruction permits different rules for the two integral terms, because the second rule changes only the scalar $\beta$. Thus the first reciprocal still needs at least $m=(n-2)/4$ exponential nodes in this fixed-direction compiler.

A compiler based on a sublinear number of such joint quadrature nodes per original head cannot establish the desired unrestricted exponent saving. The theorem leaves open transformations that change product directions, recalibrate the numerator functions, or use a different sign-sensitive representation.

The distinction is concrete for this example: its target has a sign representation by just four product atoms after changing directions. Indeed, as $t\to0$ through positive values,

$$ 1-\frac{(e^{tr(x)}-1)(e^{tB(x)}-1)}{t^2}\longrightarrow1-r(x)B(x)=B(x)S(x). $$

The right side is strictly nonzero on the finite cube and has the signs of $S$. Hence every sufficiently small positive $t$ gives the same signs. Expanding the left side uses the four affine exponential directions $0,r,B,r+B$. Thus the linear-node obstruction is a restriction on the fixed-direction quadrature compiler, not on general product sign rank.

## Verification status

This is a complete written argument, not a numerical experiment. The positive-definite moment matrix, determinant perturbation bound, finite exclusion of zero scores, and rank obstruction are justified above. No Lean formalization is claimed in this note.
