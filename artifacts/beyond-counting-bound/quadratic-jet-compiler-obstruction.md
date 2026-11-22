# The Linear Cost of a Single Quadratic Jet

## Statement

**Theorem.** For every integer $k\geq24$, there is a quadratic polynomial $Q$ on $n=3k$ Boolean variables such that the predicate $Q\gt0$ requires more than $n/72$ heads in the unchanged attention model. Consequently, an arbitrary linear combination of second-order reciprocal jets at a single fixed positive affine denominator cannot be compiled into a bounded number of actual heads.

Conversely, for every positive affine denominator with strictly positive coefficients, every quadratic numerator gives a predicate computable with at most $2n+3$ heads. Thus the worst conversion cost for these single-center predicates is of linear order, at least along the dimensions $n=3k$.

This is an obstruction to a proposed compiler, not a proof of the research target. A lower bound linear in $n$ is far below the selected exponential scale. The theorem does not imply that costs add across multiple jet centers.

## An explicit family with cubic entropy

Split the input into three blocks $x,y,z\in\lbrace0,1\rbrace^k$, and define the integer address

$$ I(x)=\sum_{i=0}^{k-1}2^i x_i. $$

Choose an arbitrary matrix $T=(t_{j\ell})$ with $k^2$ entries in $\lbrace0,\ldots,2^k-1\rbrace$. Define

$$ Q_T(x,y,z)=I(x)\sum_{\ell=1}^k z_\ell-\sum_{j=1}^k\sum_{\ell=1}^k t_{j\ell}y_jz_\ell. $$

This is a polynomial of degree at most two. At the one-hot selectors $y=e_j$ and $z=e_\ell$, it satisfies

$$ Q_T(x,e_j,e_\ell)=I(x)-t_{j\ell}. $$

Thus the Boolean function $f_T=\mathbf1[Q_T\gt0]$ determines every matrix entry. Indeed, if $t_{j\ell}\lt u_{j\ell}$, choose the unique address $x$ with $I(x)=u_{j\ell}$. Then $Q_T(x,e_j,e_\ell)\gt0$ while $Q_U(x,e_j,e_\ell)=0$. The two Boolean functions differ. Reversing the two matrices covers the other inequality.

There are therefore exactly

$$ (2^k)^{k^2}=2^{k^3} $$

distinct functions in this family. If strict signs at every cube vertex are preferred, replace every $Q_T$ by $Q_T-1/2$. All original values are integers, so this preserves every label and eliminates all zeros. The degree remains at most two.

## Counting all admissible head representations

The normalized counting proof in `version-5.tex`, equation `normalized-sign-count`, applies to every admissible representation, including target-dependent denominators. If $H\geq1$ and $2nH\leq2^n-1$, it gives

$$ \lvert\lbrace f:H^{\ast}(f)\leq H\rbrace\rvert\leq2\left(\frac{2e(2^n-1)}{n}\right)^{2nH}. $$

For clarity, the score is strictified and normalized to a discrete constant sign plus $2nH$ real parameters. Clearing the positive denominators at the nonzero cube inputs produces polynomials of parameter degree $H$. Warren's strict-sign bound then gives the displayed inequality. The analytic bound is also stated as Theorem 2.1 in [Goldberg and Jerrum](https://www.cs.ox.ac.uk/people/paul.goldberg/papers/goldbergjerrum.pdf). No restriction on coefficient heights, margins, or denominator dependence is introduced.

Set $n=3k$ and $H=\lfloor k/24\rfloor$. Then $H\geq1$. The required sample-size condition holds: using $k\leq2^k$ gives

$$ 2nH\leq\frac{k^2}{4}\leq\frac{4^k}{4}\lt8^k-1=2^n-1. $$

Since $e\lt3$ and $n\geq3$, the base in the sign count is less than $2^{n+1}$. Hence

$$ \lvert\lbrace f:H^{\ast}(f)\leq H\rbrace\rvert\lt2^{1+2nH(n+1)}\leq2^{1+(3/4)k^3+(1/4)k^2}\lt2^{k^3}. $$

The final strict inequality follows from $k^2(k-1)\gt4$, which holds for $k\geq3$. Comparison with the injective family proves that some $f_T$ requires more than $\lfloor k/24\rfloor$ heads. Since head counts are integers, its complexity is strictly greater than $k/24=n/72$. This proves the head lower bound. $\blacksquare$

## Why this concerns a single jet center

Fix the affine denominator $B(x,y,z)=1+\sum_i x_i+\sum_j y_j+\sum_\ell z_\ell$. Every coefficient is strictly positive. The signs of $Q_T/B^3$ and $Q_T$ agree on every cube vertex. For the reciprocal map $b\mapsto1/(b_0+\sum_i b_i u_i)$, setting $u_0=1$ gives

$$ \frac{\partial^2}{\partial b_i\partial b_j}\frac{1}{b_0+\sum_a b_a u_a}=\frac{2u_i u_j}{(b_0+\sum_a b_a u_a)^3}. $$

Every quadratic numerator, including its constant and linear terms, is a linear combination of these second derivatives at the single point $b_0=b_1=\cdots=b_n=1$. Thus the lower bound applies even to one fixed jet center. It rules out a uniform constant cost for compiling arbitrary quadratic jet combinations, including compilation that may choose entirely different target-dependent denominators.

This does not prove a direct-sum theorem across the centers in the open-code interpolation construction. Such an assertion would be a separate substantive theorem, and none is established here.

## A matching linear upper bound

Let $B=b_0+\sum_{i=1}^n b_i x_i$, where every $b_i\gt0$, and let $Q$ be any real quadratic polynomial. Set $u=(1,x_1,\ldots,x_n)$. Write $Q=u^{\top}Mu$ for a real symmetric matrix $M$. The real spectral theorem gives

$$ Q(x)=\sum_{j=1}^r\lambda_j L_j(x)^2,\qquad r\leq n+1,\qquad L_j(x)=\sum_{i=0}^n\ell_{ji}u_i. $$

For a positive parameter $t$, define

$$ D_t(B,L)=\frac{1}{2t^2}\left(\frac{1}{B-tL}+\frac{1}{B+tL}-\frac{2}{B}\right). $$

Direct multiplication gives the exact identity and error formula

$$ D_t(B,L)=\frac{L^2}{B(B^2-t^2L^2)},\qquad D_t(B,L)-\frac{L^2}{B^3}=\frac{t^2L^4}{B^3(B^2-t^2L^2)}. $$

Choose $t\gt0$ small enough that $2t|\ell_{ji}|\leq b_i$ for every $i,j$. This is possible because the collection is finite and every $b_i$ is positive. Each coefficient of $B\pm tL_j$ is then at least $b_i/2\gt0$. On the cube, the triangle inequality also gives $2|tL_j(x)|\leq B(x)$. In particular all displayed denominators are nonzero, and the error formula implies

$$ \left|D_t(B(x),L_j(x))-\frac{L_j(x)^2}{B(x)^3}\right|\leq\frac{2t^2L_j(x)^4}{B(x)^5}. $$

Put $F=Q/B^3$. If $F$ has no positive value, its predicate is constant false and needs no heads. Otherwise define the finite positive margin and finite error bound

$$ \gamma=\min_{x:F(x)\gt0}F(x)\gt0,\qquad M_0=\max_x\sum_{j=1}^r\frac{|\lambda_j|L_j(x)^4}{B(x)^5}. $$

Decrease $t$ further to ensure $2t^2M_0\lt\gamma/4$. For $G_t=\sum_j\lambda_jD_t(B,L_j)$, the triangle inequality gives $|G_t(x)-F(x)|\lt\gamma/4$ at every vertex. Therefore $G_t-\gamma/2$ is strictly positive where $Q\gt0$, and strictly negative where $Q\leq0$. This also handles all zero values of $Q$ without assuming a preexisting strict polynomial representation.

Expanding $G_t$ displays the actual heads:

$$ G_t(x)=\sum_{j=1}^r\left(\frac{\lambda_j/(2t^2)}{B(x)-tL_j(x)}+\frac{\lambda_j/(2t^2)}{B(x)+tL_j(x)}\right)-\frac{(\sum_j\lambda_j)/t^2}{B(x)}. $$

There are at most $2r+1\leq2n+3$ affine-ratio terms, each with strictly positive denominator coefficients. Their constant numerators may have either sign, as permitted by the exact normal form. The final constant $-\gamma/2$ is the free readout bias. This proves the claimed upper bound. No coefficient-height or margin restriction has been imposed. $\blacksquare$

Applying this approximation simultaneously to a finite sum of jet blocks preserves a strict score after choosing sufficiently small parameters. Its cost is linear in the dimension per block. For the open-code construction this recovers an upper bound of order $2^n/n$, and does not establish an upper bound of order $2^n/n^2$ or the selected refutation.

## Formal boundary

`formalization/HeadComplexity/Atoms/QuadraticThresholdEncoding.lean` defines the quadratic family on three Boolean blocks. `polynomial_eval` and `polynomial_totalDegree_le` verify its explicit polynomial and degree bound. `score_units` proves the one-hot evaluation identity; `family_injective` and `family_card` prove the exact count $2^{k^3}$. `exists_outside` supplies the finite counting consequence, and `head_count_exponent_lt` checks the relevant integer exponent inequality.

`QuadraticJetApproximation.lean` proves the finite-difference identity, its exact error formula, positivity under coefficient perturbations, the quantitative error bound, and sign preservation under the final downward bias. The spectral decomposition, finite-margin choice, head assembly, identification with derivatives, and application of Warren's analytic theorem are written proofs above. No new Lean declaration is claimed to prove Warren's theorem, the full compiler, or the main asymptotic target.
