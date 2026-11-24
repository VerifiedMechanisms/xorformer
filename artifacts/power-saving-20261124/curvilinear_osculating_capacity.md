# Weighted sign capacity of curvilinear osculating scores

## Status and scope

This note proves a new restricted sign-capacity theorem by applying the weighted-degree count in `weighted_degree_sign_capacity.md`. A complete numerator jet and a complete denominator jet have complementary parameter weights. Their factorial weight products remove the large degree penalty even when the jet length is exponential in the number of input bits.

The class contains exact reciprocal derivative scores along arbitrary affine denominator curves. It is broader than straight-pencil derivative scores, but no reduction of all original affine-ratio representations to this class is established. In particular, full rank of a limiting jet matrix gives a weak limiting sign representation, not automatically a strict one. The final section isolates this distinction.

This is a written proof. No Lean formalization is claimed.

## The osculating class

Let $X=\lbrace0,1\rbrace^n$, $N=2^n$, and $m\geq1$. Choose affine real forms $B_0,\ldots,B_{m-1}$ and $L_0,\ldots,L_{m-1}$, with $B_0(x)\gt0$ on $X$. Define formal reciprocal coefficients by

$$ f_r(x)=[s^r]\frac{1}{\sum_{j=0}^{m-1}B_j(x)s^j},\qquad 0\leq r\lt m. $$

The osculating score is

$$ S(x)=\sum_{r=0}^{m-1}L_r(x)f_r(x). $$

An arbitrary output bias is already included: replacing $L_0$ by $L_0+cB_0$ adds $c$ to the score. All denominator jets and numerator coefficients may depend on the desired target. No bound on coefficient sizes, cancellations, or margins is imposed. The forms $B_j$ for $j\geq1$ need not satisfy a sign condition.

### Theorem 1. Explicit sign count

Put $p=2(n+1)m$. If $p\leq N$, the number of strict Boolean sign tables of these scores is at most

$$ \left(\frac{16e^2N}{p}\right)^p. $$

Consequently, if $m\leq N/[64(n+1)]$, the number is at most $2^{13N/32}$. The worst-case osculating length is therefore greater than $\lfloor N/[64(n+1)]\rfloor$ whenever that integer is positive.

**Proof.** Define $Q_r=B_0^{r+1}f_r$. Formal multiplication gives

$$ Q_0=1,\qquad Q_r=-\sum_{j=1}^r B_j B_0^{j-1}Q_{r-j}. $$

Thus every $Q_r$ is a polynomial in the affine-form coefficients. Assign weight $j+1$ to each coefficient of $B_j$. Induction in this recurrence shows that $Q_r$ is weighted homogeneous of degree $2r$: each summand has degree $(j+1)+(j-1)+2(r-j)=2r$.

The strictly positive factor $B_0^m$ does not change score signs. Its product with the score is

$$ P(x)=\sum_{r=0}^{m-1}L_r(x)Q_r(x)B_0(x)^{m-r-1}. $$

Assign weight $m-r$ to each coefficient of $L_r$. Each summand now has weighted degree

$$ (m-r)+2r+(m-r-1)=2m-1. $$

For each fixed cube point, $P(x)$ is therefore a polynomial of weighted degree $D=2m-1$ in $p=2(n+1)m$ parameters. Every variable weight lies between one and $m$, hence is at most $D$. The product of all variable weights is

$$ \prod_{\ell=1}^p w_\ell=(m!)^{2(n+1)}. $$

The weighted-degree sign-count theorem yields

$$ T\leq\frac{1}{(m!)^{2(n+1)}}\left(\frac{8eDN}{p}\right)^p\leq\left(\frac{8e^2DN}{mp}\right)^p\leq\left(\frac{16e^2N}{p}\right)^p. $$

Here $m!\geq(m/e)^m$ and $D\leq2m$. Positivity of $B_0$ and any further coefficient restrictions only decrease the counted class.

If $m\leq N/[64(n+1)]$, then $p\leq N/32$. The function $u\log_2(16e^2N/u)$ is increasing for $0\lt u\leq N/32$. Therefore

$$ \log_2T\leq\frac{N}{32}\log_2(512e^2)\lt\frac{13N}{32}, $$

using $e\lt3$ and $512\cdot9\lt2^{13}$. This proves the result. $\blacksquare$

The conclusion is a restricted $\Omega(2^n/n)$ lower bound, not a bound on the original worst-case head complexity. An osculating length is the number of derivative orders in this definition; it must not silently be identified with the cost of an arbitrary finite-scale representation.

## What fixed curvilinear collisions do imply

Let $B(s,x)=\sum_{j\geq0}B_j(x)s^j$ be a convergent analytic germ in $s$, with every $B_j$ affine and $B_0\gt0$ on $X$. Let $\lambda_1,\ldots,\lambda_m$ be distinct real numbers. For sufficiently small positive $t$, define the score space

$$ V(t)=\mathrm{span}\left(\lbrace1\rbrace\cup\left\lbrace\frac{x_i}{B(\lambda_h t,x)}:1\leq h\leq m, 1\leq i\leq n\right\rbrace\right). $$

This contains every affine-numerator score at the displayed denominators. Indeed, writing $B(s,x)=b_0(s)+\sum_i b_i(s)x_i$, one has $b_0(s)\neq0$ for sufficiently small $s$ and

$$ \frac{1}{B(s,x)}=\frac{1}{b_0(s)}-\sum_i\frac{b_i(s)}{b_0(s)}\frac{x_i}{B(s,x)}. $$

Let $f_r=[s^r]\big(1/B(s,x)\big)$ and let

$$ V_0=\mathrm{span}\left(\lbrace1\rbrace\cup\lbrace x_i f_r:1\leq i\leq n, 0\leq r\lt m\rbrace\right). $$

This is a subspace of the osculating class with the fixed first $m$ denominator jets. The bias can be written as $B_0f_0$.

### Theorem 2. Full jet rank controls every bounded limit

Assume the $nm+1$ displayed generators of $V_0$ are linearly independent as real tables on $X$. If $t_\nu\to0$ through positive values and $g_\nu\in V(t_\nu)$ is bounded and converges to a table $g$, then $g\in V_0$. This allows arbitrary dependence of all numerator and bias coefficients on $t_\nu$.

**Proof.** Put $\psi_i(s,x)=x_i/B(s,x)$. Its Taylor expansion is $\psi_i(s)=\sum_{r\geq0}s^r x_i f_r$. Let $\Lambda$ be the invertible Vandermonde matrix with rows indexed by $h$ and columns by $r=0,\ldots,m-1$, with entries $\lambda_h^r$.

For each fixed $i$, use the inverse Vandermonde matrix to form linear combinations of the $m$ columns $\psi_i(\lambda_h t)$, and divide the combination corresponding to order $r$ by $t^r$. The resulting column has expansion

$$ x_i f_r+O(t^{m-r})=x_i f_r+O(t). $$

These are invertible column operations for every $t\neq0$. With the constant column retained, they produce a matrix $M(t)$ spanning $V(t)$ and converging to the full-rank matrix $M(0)$ of the displayed generators of $V_0$.

Choose $nm+1$ table rows on which $M(0)$ is invertible. The same square submatrix of $M(t)$ has a uniformly bounded inverse for all sufficiently small $t$. Write $g_\nu=M(t_\nu)a_\nu$. The selected rows of the bounded table $g_\nu$ force $a_\nu$ to be bounded. A convergent subsequence gives $g=M(0)a\in V_0$. Equivalently, a left inverse on those selected rows gives convergence directly. $\blacksquare$

If a strict Boolean target $F$ occurs in $V(t)$ for a sequence $t\to0$, normalize the score tables to maximum absolute value one. A subsequence converges to a nonzero $g\in V_0$ satisfying $F(x)g(x)\geq0$. This is a nonzero weak sign representation. If its coordinates are all nonzero, it is strict and Theorem 1 applies to that target. Without the latter condition, one must retain the weak conclusion.

## The two unresolved transfers

First, full jet rank alone does not imply that every eventual strict sign vector is a strict sign vector of the limiting space. For example, on three abstract coordinates let $V(t)=\mathrm{span}\lbrace(1,1,1),(t,-t,1)\rbrace$. The two limiting columns remain independent, but the strict sign table $(+,-,+)$ is realized for every $t\gt0$ and is absent from the limiting space, whose first two coordinates are equal. This example illustrates the linear-algebra gap; it is not asserted to be an original-model counterexample. A proof transferring arbitrary eventual labels must control vanishing coordinate minors or higher jets as well.

Second, even the weak inclusion in Theorem 2 assumes the full-rank jet condition. Singular parametrizations can skip derivative orders. For example, choose $B_0,C,D$ so the reciprocal table coefficients at orders zero, two, and three of $B(s)=B_0+s^2C+s^3D$ are independent. Three colliding samples with an invertible generalized Vandermonde matrix for those orders can detect all three directions, while the first three ordinary derivative orders omit the third. Degeneracy after evaluating on the Boolean cube can also occur for curves whose first derivative is nonzero.

There is a stronger reason that a weak sign conclusion cannot simply replace strictness in Theorem 1. The osculating class with $m=n+1$ already contains a point mass at the zero vertex. Take $B_0=1$, $B_1=w(x)=\sum_i x_i$, and all later denominator jets zero. Then $f_r=(-w)^r$. Constant choices of the $L_r$ can therefore form

$$ \prod_{k=1}^n\left(1-\frac{w(x)}{k}\right)=\boldsymbol{1}_{\lbrace x=0\rbrace}. $$

For every Boolean target $F$, multiplying this table by $F(0)$ gives a nonzero weak sign representation. Thus counting weak labels of the unrestricted osculating class gives no obstruction even at length $n+1$. This observation does not assert that this particular curve satisfies the full-rank hypothesis of Theorem 2. It shows why a general reduction producing only weak osculating signs would be insufficient.

No theorem here reduces arbitrary finite-scale admissible denominators, all rank-deficient curvilinear collisions, or general multivariate pole clusters to the osculating class with a controlled increase in length. Those are substantive missing steps. The weighted count supplies a positive cancellation-counting mechanism once an appropriate complete jet chart is available; it does not establish the requested unrestricted exponent improvement.
