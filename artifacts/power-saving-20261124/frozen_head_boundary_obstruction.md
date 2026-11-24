# A Minimal-Width Representation with an Interior Frozen-Head Feasible Set

## Scope

This is an obstruction to a proposed single-head deformation argument. An exact three-head representation of three-bit parity has the following property: after fixing the other two heads, every feasible replacement of the first head has a normalized denominator bounded away from every coefficient-simplex face. Thus convexity of the feasible parameter block does not itself force a boundary point. Joint changes to several heads remain possible, and this example does not exclude a global degeneration argument. It is not the requested lower bound.

## Exact original-model family

Write $s=x_1+x_2+x_3$ and set

$$ A=s-1/2,\qquad D=2s-3,\qquad B=1+x_1+2x_2+3x_3. $$

For $0\lt t\lt1/3$, all three denominators below have strictly positive constant and slope coefficients. The affine numerators are unrestricted, as permitted for nonconstant denominators in the original model. Direct expansion gives

$$ S_t=\frac{A}{B}+\frac{D-A}{B+tD}-\frac{D}{B+t(D-A)}=\frac{t^2AD(D-A)}{B(B+tD)(B+t(D-A))}. $$

The product $AD(D-A)=2(s-1/2)(s-3/2)(s-5/2)$ has sign $f(x)=(-1)^{s+1}$ on the cube. Hence $S_t$ strictly represents odd parity. Three heads are minimal: clearing the positive denominator product of a two-head score gives a polynomial of degree at most two. Its correlation with three-bit parity is zero by Boolean Fourier orthogonality, whereas a sign-representing polynomial has strictly positive correlation. The argument also allows zero scores on false inputs.

Freeze the last two heads and write their sum as $R_t$. A replacement first head $A'/B'$ is feasible when $B'$ is positive on the cube and

$$ f(x)\bigl(A'(x)+R_t(x)B'(x)\bigr)\gt0\qquad\text{for every }x. $$

For fixed $R_t$ these are linear strict inequalities in the coefficients of $A'$ and $B'$. Thus this is indeed the convex parameter block contemplated by the proposed route.

## The block stays away from every denominator face

**Proposition.** There is $t_0\gt0$ such that, for every $0\lt t\lt t_0$ and every feasible affine replacement $A'/B'$, all four coefficients $b'_j$ of $B'$ are strictly positive and

$$ \frac{b'_j}{b'_0+b'_1+b'_2+b'_3}\geq\frac1{14}\qquad(0\leq j\leq3). $$

The hypothesis only requires $B'$ to be positive at cube vertices. Coherent slopes need not be imposed for this conclusion.

**Proof.** Order the vertices lexicographically and let $X$ be the matrix with rows $(1,x_1,x_2,x_3)$. Let $a,b$ be the coefficient vectors of $A,B$. Define the eight-by-eight matrix

$$ M_t=\mathrm{diag}(f)\bigl[X\mid\mathrm{diag}(R_t)X\bigr]. $$

At $t=0$ set $R_0=-A/B$. The first seven rows and first seven columns of $M_0$ have determinant $3/320$. Furthermore

$$ M_0(a,b)^{\top}=0,\qquad (B(x))_x^{\top}M_0=0. $$

The first identity follows directly from $R_0=-A/B$. For the second, each coordinate is the parity correlation of a polynomial of degree at most two, namely either $B(x)X_j(x)$ or $-A(x)X_j(x)$. Thus $M_0$ has rank seven, right kernel spanned by $(a,b)$, and a strictly positive left-kernel vector.

Suppose the proposition were false along a sequence $t_k\to0$. Scale each feasible coefficient vector $z_k=(a'_k,b'_k)$ to Euclidean norm one by a positive scalar. Passing to a subsequence gives $z_k\to z_0$ with norm one. The feasibility inequalities and continuity give $M_0z_0\geq0$ coordinatewise. Pairing with the positive left-kernel vector forces $M_0z_0=0$. Therefore $z_0=\lambda(a,b)$ for a nonzero scalar $\lambda$.

Positivity of the replacement denominators at the origin gives $b'_{k,0}\gt0$, hence the limit has $b' _{0,0}\geq0$. Since $b_0=1$, this forces $\lambda\gt0$. Consequently the normalized denominator coefficients converge to

$$ \frac{b}{b_0+b_1+b_2+b_3}=\frac17(1,1,2,3). $$

Every coordinate of this limit is at least $1/7$. For all sufficiently large $k$, all four replacement coefficients are positive and their normalized ratios exceed $1/14$, contradicting the selected failures. $\blacksquare$

## A finite exact certificate

The script `check_frozen_head_boundary.py` uses rational arithmetic to check the stronger explicit instance $t=1/10$. It checks the head identity, all eight strict target signs, original positive coefficient admissibility, the rank-seven minor and null vectors at zero, and the exact inverse of $M_{1/10}$.

Every entry in the bottom four rows $Z$ of this inverse is positive. For a feasible replacement, $y=M_{1/10}(a',b')^{\top}\gt0$ and $b'=Zy$. Therefore each normalized coefficient is a weighted average of the corresponding column ratios of $Z$. The exact common lower bound is

$$ \gamma=\min_{j,k}\frac{Z_{jk}}{\sum_{i=0}^3Z_{ik}}=\frac{111112039003108}{1031376329133247}\gt0. $$

The full rational matrices and checks are stored in `frozen_head_boundary_exact.json`. This finite computation is separate from the general written compactness proof. Neither has been Lean formalized.

## What remains possible

The example has a joint sign-preserving deformation: replacing the common positive base $B$ by another positive affine base keeps the displayed product numerator unchanged. Accordingly it does not exhibit a sign chamber whose joint closure excludes denominator boundary points or collisions. The outstanding issue is whether every minimal-width original-model sign representation admits some joint degeneration with useful uniform structure. The single-head convexity observation is insufficient to prove that assertion.
