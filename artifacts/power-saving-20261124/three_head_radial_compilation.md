# Three-head compilation and a second-order radial obstruction

## Status and scope

Every strict three-head affine-ratio score has a sign representation by seven affine-times-product atoms, by an explicit finite-difference identity. The simplest second-order radial version of this compiler cannot use six atoms for a generic cleared cubic. This lower statement concerns exact continuous leading polynomials, not arbitrary sign-equivalent scores on the Boolean cube.

All arguments here are written proofs. No Lean verification is claimed, and no improved lower bound for the original worst-case number of heads follows.

## Seven product atoms always suffice for three heads

Let $B_1,B_2,B_3$ be positive on a finite Boolean cube, and let $A_1,A_2,A_3$ be arbitrary affine forms. An output bias can be absorbed algebraically into $A_1$ by replacing it with $A_1+cB_1$. Multiplication by the positive product of denominators shows that the score signs are those of

$$ P=A_1B_2B_3+A_2B_1B_3+A_3B_1B_2. $$

For positive $t$, define

$$ G_t=\sum_{h=1}^3 A_h\prod_{g\neq h}(e^{tB_g}-1). $$

Then $t^{-2}G_t\to P$ pointwise. If the original score is strict, so is $P$, and finiteness of the cube implies that $G_t$ has the same signs for every sufficiently small positive $t$.

Expanding the products gives precisely seven possible directions:

$$ G_t=\sum_{S\subsetneq\lbrace1,2,3\rbrace}(-1)^{2-|S|}\left(\sum_{h\notin S}A_h\right)e^{t\sum_{g\in S}B_g}. $$

The empty subset supplies a constant product factor. Every other exponential of an affine form is a product of strictly positive one-bit factors on the cube. Its prefactor is affine. This proves a seven-atom sign compiler for arbitrary three-head scores, with arbitrary coefficients and cancellations. It imposes no restriction on the original denominators beyond their positivity; original coherent-slope representations are included.

## Essential dimension of a second-order leading cubic

The essential dimension of a homogeneous polynomial is the minimum dimension of a linear-form space in whose polynomial algebra it lies. Equivalently, it is the rank of the linear map sending a constant vector to the corresponding directional derivative of the polynomial.

### Theorem 1. The dimension bound

Let $L_1,\ldots,L_K$ and $C_1,\ldots,C_K$ be real linear forms on a finite-dimensional real vector space. Suppose

$$ \sum_{h=1}^K L_h=0,\qquad \sum_{h=1}^K L_hC_h=0. $$

Then the homogeneous cubic

$$ R=\sum_{h=1}^K L_hC_h^2 $$

has essential dimension at most $K-1$.

**Proof.** Replace every $C_h$ by $C_h-C_1$. The two assumed identities show that this leaves $R$ unchanged. We may therefore assume $C_1=0$. Let $D_1,\ldots,D_r$ be a basis of the span of $C_2,\ldots,C_K$, where $0\leq r\leq K-1$.

Write $C_h=\sum_a m_{ah}D_a$ for $2\leq h\leq K$, with the $r$ by $(K-1)$ coefficient matrix of rank $r$. The quadratic identity becomes

$$ \sum_{a=1}^r M_aD_a=0,\qquad M_a=\sum_{h=2}^K m_{ah}L_h. $$

Each $M_a$ lies in the span of the $D_b$. To see this, extend the $D_b$ to a basis of all linear forms. The coefficients of the distinct mixed monomials consisting of one complementary basis form and one $D_a$ must all vanish in the displayed quadratic identity. Thus the complementary components of every $M_a$ vanish. Within the $D$ span, the coefficient matrix of the $M_a$ is skew-symmetric, although this additional fact is not needed below.

Choose a right inverse of the coefficient matrix. Expressing the vector $(L_2,\ldots,L_K)$ as that right inverse applied to $(M_1,\ldots,M_r)$ plus a vector in the matrix kernel shows that all $L_h$ belong to the span of the $D_a$ and at most $K-1-r$ further linear forms. The form $L_1=-\sum_{h\geq2}L_h$ lies in the same span. Every $C_h$ also lies in that span. Its total dimension is at most $r+(K-1-r)=K-1$, and $R$ is a polynomial in it. $\blacksquare$

The proof also covers $r=0$, when the cubic is zero. It uses only linear algebra and the fact that polynomial monomials in independent linear coordinates are independent.

### Corollary 2. A generic three-head cubic needs seven terms in this ansatz

Let $A_1,A_2,A_3,B_1,B_2,B_3$ now be six independent linear forms. The cubic

$$ P=A_1B_2B_3+A_2B_1B_3+A_3B_1B_2 $$

has essential dimension six. Therefore it cannot equal a nonzero scalar multiple of a cubic in Theorem 1 with $K\leq6$.

**Proof.** Its three derivatives in the $A$ directions are $B_2B_3,B_1B_3,B_1B_2$. Its three derivatives in the $B$ directions are $A_2B_3+A_3B_2$, $A_1B_3+A_3B_1$, and $A_1B_2+A_2B_1$. These six quadratics are linearly independent: the first three have distinct monomials using only the $B$ variables, and each of the last three has an $A_iB_j$ monomial appearing in no other displayed derivative. The directional-derivative map therefore has rank six. Apply Theorem 1. $\blacksquare$

This algebraic independence is compatible with the original denominator orientation: in at least six input variables one can choose three independent strictly positive slope vectors for the $B$ forms, extend them by three numerator slope vectors, and add positive constants to the denominators. The highest homogeneous part of the cleared cubic has the stated six-dimensional dependence. This observation does not transfer the continuous polynomial identity obstruction to Boolean sign representation.

## Moving numerators and second-order curved directions

The homogeneous cubic obstruction survives the following precise extension. Suppose the affine numerator and exponent germs have expansions

$$ L_h(t,x)=L_{h,0}(x)+tL_{h,1}(x)+t^2L_{h,2}(x)+O(t^3),\qquad \phi_h(t,x)=tC_h(x)+t^2D_h(x)+O(t^3), $$

where every displayed coefficient is affine in $x$. Suppose the coefficients of $t^0$ and $t^1$ in $\sum_hL_h(t,x)e^{\phi_h(t,x)}$ vanish identically as polynomials in continuous $x$.

Let $\ell_h$ and $c_h$ be the homogeneous linear parts of $L_{h,0}$ and $C_h$. The degree-one part of the order-zero identity and the degree-two part of the order-one identity give

$$ \sum_h\ell_h=0,\qquad \sum_h\ell_hc_h=0. $$

The coefficient of $t^2$ is

$$ \sum_h\left(L_{h,2}+L_{h,1}C_h+L_{h,0}D_h+\frac12L_{h,0}C_h^2\right). $$

Its homogeneous cubic part is exactly $\frac12\sum_h\ell_hc_h^2$. Theorem 1 therefore bounds that cubic's essential dimension by $K-1$. Numerator motion and the displayed quadratic curvature contribute only degree at most two at this order.

This statement does not cover a first nonzero order greater than two, arbitrary meromorphic rescalings whose decisive order changes, different nonzero baseline exponent directions, or identities that hold only after Boolean reduction. In particular, it does not prove that every unrestricted six-atom product sign compiler fails. The seven-atom formula is a valid finite-cube compiler; the lower result only shows that its simplest exact second-order leading-cubic mechanism is sharp.
