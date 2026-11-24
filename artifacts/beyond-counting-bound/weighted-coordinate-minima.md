# Many strict minima of a full-head coordinate loss

## Statement and scope

Let $d\geq3$, $k\geq1$, and $n=d+k$. There is a fixed real target table on the Boolean cube and strictly positive weights on all its entries such that weighted squared distance from the full single-head family

$$ F_{a,u,b}(z)=\frac{a+u\cdot z}{1+b\cdot z},\qquad b\in(0,\infty)^n $$

has at least $(2^{d-1}-1)^k$ distinct nondegenerate strict local minima in its full $2n+1$ dimensional coefficient domain. Their complete tables are distinct. Every minimum strictly computes the same Boolean function: the output is positive exactly when at most one of the last $k$ bits is one. All these tables are actual admissible heads.

For $d=k$, the logarithm of the number of minima is $(1/4+o(1))n^2$. The loss is a sum of squared errors at individual cube entries, with a positive diagonal metric. No arbitrary linear mixing of observations is used.

This is a complete written auxiliary theorem. It is not a lower bound for Boolean head complexity. It makes no assertion that these minima are global, or that the weights can all be equal. Strictness refers to normalized coefficient coordinates, not redundant embeddings or projection matrices. The original lower-bound target remains unproved.

## A one-pole regression with many strict minima

Put $m=2^d$ and choose the $m-1$ rational roots

$$ r_s=1+\frac{s}{m}\quad(1\leq s\leq m-1),\qquad P(t)=\prod_{s=1}^{m-1}(t-r_s),\qquad D(t)=\prod_{j=1}^m(t+j). $$

Define $\lambda_j=P(-j)/\prod_{\ell\neq j}(\ell-j)$. The usual simple-pole identity gives

$$ R(t)=\sum_{j=1}^m\frac{\lambda_j}{t+j}=\frac{P(t)}{D(t)},\qquad W(t)=\sum_{j=1}^m\frac1{(t+j)^2},\qquad V(t)=D(t)^2W(t)=\sum_{j=1}^m\prod_{\ell\neq j}(t+\ell)^2. $$

Set $\phi=R^2/W=P^2/V$. On every interval $(r_s,r_{s+1})$, this function has exactly one critical point, and its second derivative there is strictly negative.

**Proof.** Write $V=\sum_j e^{g_j}$, where $g_j=2\sum_{\ell\neq j}\log(t+\ell)$, and let $\pi_j=e^{g_j}/V$. Direct differentiation yields

$$ (\log V)''=\sum_j\pi_j g_j''+\sum_j\pi_j(g_j')^2-\left(\sum_j\pi_jg_j'\right)^2\geq-2\sum_{j=1}^m\frac1{(t+j)^2}. $$

The inequality uses the nonnegative variance and $g_j''=-2\sum_{\ell\neq j}(t+\ell)^{-2}$. For $1\lt t\lt2$, every $|t-r_s|\lt1$, and

$$ \sum_{j=1}^m\frac1{(t+j)^2}\lt\sum_{j=1}^m\frac1{j(j+1)}\lt1. $$

Consequently, away from the roots,

$$ (\log\phi)''=-2\sum_{s=1}^{m-1}\frac1{(t-r_s)^2}-(\log V)''\lt-2(m-2)\lt0. $$

On the closed interval between consecutive roots, $\phi$ is continuous, positive inside, and zero at both endpoints. It attains a positive interior maximum. Strict concavity of its logarithm gives uniqueness of the critical point. At that point, $\phi''=\phi(\log\phi)''\lt0$. $\blacksquare$

For a fixed positive scale $\eta$, consider the two-parameter loss

$$ L(A,t)=\sum_{j=1}^m\left(\frac A{t+j}-\eta\lambda_j\right)^2=\eta^2\sum_j\lambda_j^2-\eta^2\phi(t)+W(t)\left(A-\frac{\eta R(t)}{W(t)}\right)^2. $$

Every critical point $t_s$ just constructed gives a nondegenerate strict local minimum at $A_s=\eta R(t_s)/W(t_s)$. Indeed, in the smooth local coordinates $e=A-\eta R(t)/W(t)$ and $t$, its Hessian is diagonal with entries $2W(t_s)\gt0$ and $-\eta^2\phi''(t_s)\gt0$.

Retain only the intervals with $R\gt0$. Since $m$ is even, these are exactly the intervals with odd index $s$, so there are $q=m/2-1$ retained minima. Choose $\eta=1/(36k)$. Throughout $(1,2)$ we have $|P|\lt1$, $D\gt1$, and $W\gt1/9$, whence every retained amplitude satisfies

$$ 0\lt A_s\lt\frac1{4k}. $$

## Anchoring all other head coordinates

Write the input as $(y,x)$ with $d$ anchor bits and $k$ selector bits. At the base anchor parameters take numerator constant one, anchor numerator coefficients zero, and anchor denominator slopes $B_j=2^j$ for $0\leq j\lt d$.

Let $\mathcal A$ contain the origin, all anchor singletons, and the anchor pairs on a triangle with all remaining vertices joined to its first vertex. Set all selector bits to zero on these inputs. There are $1+2d$ anchor samples. Prescribe the values $1$, $1/(1+B_j)$, and $1/(1+B_i+B_j)$ at their respective samples. Let $L_{\mathcal A}$ be the sum of their squared errors.

The anchor evaluation Jacobian is invertible. To verify this directly, a kernel vector has $\delta a=0$, and the singleton equations give $\delta u_j=\delta b_j/(1+B_j)$. The pair equation for an edge becomes

$$ \frac{B_j}{1+B_i}\delta b_i+\frac{B_i}{1+B_j}\delta b_j=0. $$

After putting $v_j=\delta b_j/[B_j(1+B_j)]$, this is $v_i+v_j=0$. The odd cycle forces its values to zero, and connectivity propagates zero to all vertices. Thus every variation is zero. This is the same general odd-cycle lemma checked in `FullHeadLinearFibers.lean`.

The anchor loss vanishes at the base point. Its Hessian in all $1+2d$ anchor variables is therefore $2J_{\mathcal A}^{\top}J_{\mathcal A}$, which is positive definite. It depends on no selector parameter.

## A diagonal loss on the complete cube

For every selector $i$, use all $m$ samples $(y(j),e_i)$, where $y(j)$ is the binary representation of $j-1$. Prescribe target value $\eta\lambda_j$. Let $L_{\mathcal S}$ be the sum of all these squared errors. At the base anchor parameters, put $A_i=1+u_{d+i}$ and $t_i=b_{d+i}$. Then

$$ L_{\mathcal S}=\sum_{i=1}^k L(A_i,t_i). $$

The anchor samples and selector samples are disjoint. Let $L_{\mathcal R}$ be the sum of squared values at every remaining cube entry, with target zero there. For sufficiently small $\varepsilon\gt0$, take the single fixed loss

$$ E_{\varepsilon}=L_{\mathcal A}+\varepsilon L_{\mathcal S}+\varepsilon^2L_{\mathcal R}. $$

Every cube entry occurs exactly once, with weight one, $\varepsilon$, or $\varepsilon^2$. The targets and weights do not depend on the choice of retained minima.

At zero perturbation there are $q^k$ candidate points: fix the base anchor parameters and independently choose one retained pair $(A_s,t_s)$ for every selector. Write the anchor variables as $p$ and the selector variables as $v$. Instead of the degenerately scaled gradient of $E_{\varepsilon}$, use the smooth equations

$$ G(p,v,\varepsilon)=\left(\partial_p L_{\mathcal A}+\varepsilon\partial_p L_{\mathcal S}+\varepsilon^2\partial_p L_{\mathcal R},\quad \partial_v L_{\mathcal S}+\varepsilon\partial_v L_{\mathcal R}\right)=0. $$

At each candidate and $\varepsilon=0$, their Jacobian in $(p,v)$ is block lower triangular. The first diagonal block is the positive definite anchor Hessian; the second is the direct sum of the positive definite two-variable regression Hessians. Both are invertible. The implicit-function theorem therefore supplies a stationary branch of $E_{\varepsilon}$ from each candidate for every sufficiently small positive $\varepsilon$.

Each stationary point is a nondegenerate strict local minimum. For clarity, its Hessian has the block form

$$ \begin{pmatrix} H_{\mathcal A}+O(\varepsilon)&O(\varepsilon)\cr O(\varepsilon)&\varepsilon H_{\mathcal S}+O(\varepsilon^2)\end{pmatrix},\qquad H_{\mathcal A}\succ0,\quad H_{\mathcal S}\succ0. $$

The upper block remains positive definite. Its Schur complement is $\varepsilon H_{\mathcal S}+O(\varepsilon^2)$, also positive definite for sufficiently small positive $\varepsilon$. This establishes strictness in every original coefficient direction, including all anchor denominators and numerator coefficients. There are finitely many candidates, so one common positive range of $\varepsilon$ works for all of them.

## Distinct tables, fixed signs, and admissibility

At a candidate point the numerator is

$$ 1+\sum_i(A_i-1)x_i. $$

It equals one when no selector is active, equals $A_i\gt0$ when exactly one is active, and is strictly negative when two or more are active: if their number is $r\geq2$, it is at most $1-r+r/(4k)\leq-3/4$. The denominator is strictly positive on the whole cube. These finitely many strict signs persist along every stationary branch for sufficiently small positive $\varepsilon$.

In fact all the minima lie in one convex coefficient region. For any fixed labels $y_z\in\lbrace-1,1\rbrace$, the one-head strict sign cell is exactly the intersection of $b_i\gt0$ and $y_z(a+u\cdot z)\gt0$ for all cube entries. These are strict linear inequalities in the normalized coefficients. Convex combinations preserve every inequality. Thus the many local minima do not even require many connected components of a sign cell.

Two candidates differing in a selector have different complete tables. On its selector slice their values are $A/(j+t)$. Equality at both $j=1$ and $j=2$, with nonzero amplitudes, forces equality of $t$ and then of $A$. Choose disjoint small table neighborhoods of the finitely many candidate tables. Continuity keeps the corresponding stationary tables in those neighborhoods, proving distinctness after perturbation.

Every denominator slope remains strictly positive. The existing positive-affine-ratio realization therefore gives actual heads in the unchanged architecture. The normalization fixes the denominator constant and absorbs an output bias into the affine numerator; it removes no permissible table direction in this positive chart.

Finally, with $d=k$,

$$ \log_2(q^k)=d\log_2(2^{d-1}-1)=(1/4+o(1))n^2. $$

The many minima all compute a linear threshold function. Thus their multiplicity cannot be used as a count of distinct Boolean functions. The construction specifically blocks a uniformly subquadratic logarithmic bound on local minima for all positive diagonal coordinate metrics. It does not block a bound on global minima, an unweighted bound, or a method counting sign patterns directly.

## Verification boundary

The analytic argument above includes the curvature estimate, critical-point existence, implicit-function step, and Schur-complement test. The accompanying exact rational verifier checks the partial fractions and brackets every regression maximum for $m=8$, including the three positive-amplitude choices. It checks the curvature identities at rational probes and reproduces the anchor Jacobian inverse. It does not numerically claim to certify a positive perturbation parameter for all 27 full six-bit minima.

`WeightedCoordinateMinima.lean` checks the regression completion of squares, a finite variance identity, the Hessian quadratic-form criterion, and the fixed-sign numerator estimate. These algebraic ingredients and the existing odd-cycle lemma support, but do not replace, the complete written analytic proof. No asymptotic head lower bound is claimed.
