# Quadratically Exponential Critical Points of One Positive Head

## Statement and scope

For integers $d\geq2$ and $k\geq1$, put $n=d+k$, $N=2^d$, and $q=2^{d-1}-1$. There is an explicitly specified rational linear functional of the cube evaluations of

$$ K_{s,u}(a,t)=\frac{1}{1+\sum_{i=0}^{d-1}a_i s_i+\sum_{j=1}^k t_j u_j},\qquad (s,u)\in\lbrace0,1\rbrace^d\times\lbrace0,1\rbrace^k, $$

having at least $q^k$ distinct nondegenerate critical points in the full positive parameter domain $a_i,t_j\gt0$. All these denominators are admissible in the manuscript's exact model.

For $d=k=r$, the logarithm to base two of this count is $r\log_2(2^{r-1}-1)=r^2-r+o(1)$. Thus the count is $2^{n^2/4-O(n)}$ on even dimensions.

This is an obstruction to counting arbitrary linear sections or their critical points in the full denominator domain. The numerator is fixed at one; criticality is not asserted after adding free numerator coordinates. It is **not** a head-complexity lower bound: every head $K$ above is strictly positive on the entire Boolean cube and computes the same constant Boolean function.

## Scalar profile and transverse stabilizer

Set $a_i^0=2^i$. The values $c_s=1+\sum_i a_i^0s_i$ run through the distinct integers $1,\ldots,N$. Define

$$ Q(t)=\prod_{\ell=1}^q(t-\ell),\qquad D(t)=\prod_{v=1}^N(t+v),\qquad r_s=\frac{Q(-c_s)^2}{\prod_{v\neq c_s}(v-c_s)}. $$

Since $2q=N-2\lt N$, partial fractions give the exact identity

$$ f(a,t):=\sum_s\frac{r_s}{1+\sum_i a_i s_i+t},\qquad f(a^0,t)=\frac{Q(t)^2}{D(t)}. $$

At every integer $1\leq\ell\leq q$,

$$ f(a^0,\ell)=\partial_t f(a^0,\ell)=0,\qquad \alpha_\ell:=\partial_t^2 f(a^0,\ell)=\frac{2Q'(\ell)^2}{D(\ell)}\geq\frac{2}{D(q)}\gt0. $$

Here $|Q'(\ell)|=(\ell-1)!(q-\ell)!\geq1$, and $D$ increases on the positive real axis.

Write $A_i=1+a_i^0$ and define the stabilizer

$$ G(a)=\sum_{i=0}^{d-1}\frac{A_i^2}{1+a_i}-\frac{N^2}{1+\sum_i a_i}. $$

At $a^0$, each gradient entry is $-1+1=0$. Its Hessian and an explicit inverse are

$$ B_{ij}=2\left(\frac{\delta_{ij}}{A_i}-\frac1N\right),\qquad (B^{-1})_{ij}=\frac12\left(A_i\delta_{ij}+\frac{A_iA_j}{1-d}\right). $$

Direct multiplication verifies the inverse: use $\sum_iA_i=N+d-1$. In particular, $B$ is nonsingular. With the induced maximum-row-sum norm, the following explicit rational number bounds its inverse norm:

$$ g=\frac{1+2^{d-1}}2\left(1+\frac{N+d-1}{d-1}\right),\qquad \lVert B^{-1}\rVert_\infty\leq g. $$

## An explicit coefficient scale

All constants in this section are positive rational numbers. Define

$$ C_f=\sum_s|r_s|,\qquad C_G=\sum_i A_i^2+N^2,\qquad C=1+C_f+C_G. $$

Define the following bounds, radius, and scale:

$$ \begin{aligned} L&=1+g+\frac{D(q)}2(1+2dC_fg),& K&=6Cn^2,\cr A&=kC_f,& K_1&=2kC_fn,\cr \delta&=\frac{1}{4(1+LK)},& \varepsilon&=\min\left\lbrace\frac{\delta}{4L(1+A)},\frac{1}{8L(1+K_1)}\right\rbrace,& M&=\varepsilon^{-1}.\end{aligned} $$

The promised functional is

$$ F(a,t)=M G(a)+\sum_{j=1}^k f(a,t_j). $$

It is a linear functional of the displayed head evaluations with fixed rational coefficients. The stabilizer uses inputs $(e_i,0)$ and $(\mathbf1,0)$. Profile $j$ uses the inputs $(s,e_j)$. Coincident input coefficients, if any, are added. No coefficient depends on the variable parameters $(a,t)$.

## Quantitative persistence of every grid point

Let $z=(a,t)$. Introduce a rescaled gradient

$$ \Psi_\eta(z)=\left(\nabla G(a)+\eta\sum_{j=1}^k\nabla_a f(a,t_j),\quad (\partial_t f(a,t_j))_{j=1}^k\right),\qquad 0\leq\eta\leq\varepsilon. $$

For each $\ell=(\ell_1,\ldots,\ell_k)\in\lbrace1,\ldots,q\rbrace^k$, put $z_\ell=(a^0,\ell)$. At scale zero, $\Psi_0(z_\ell)=0$. Its Jacobian has the block form

$$ J_\ell=D\Psi_0(z_\ell)=\left(\begin{array}{cc}B&0\cr E_\ell&\mathrm{diag}(\alpha_{\ell_j})\end{array}\right),\qquad E_\ell[j,i]=\partial_t\partial_{a_i}f(a^0,\ell_j). $$

Every denominator is at least one on the positive parameter domain. Hence $|E_\ell[j,i]|\leq2C_f$. The inverse of this block triangular matrix is

$$ J_\ell^{-1}=\left(\begin{array}{cc}B^{-1}&0\cr -\mathrm{diag}(\alpha_{\ell_j}^{-1})E_\ell B^{-1}&\mathrm{diag}(\alpha_{\ell_j}^{-1})\end{array}\right). $$

The preceding estimates imply the uniform bound $\lVert J_\ell^{-1}\rVert_\infty\leq L$. This bound is independent of the grid choice $\ell$.

Let $\mathcal B_\ell$ be the closed maximum-norm ball of radius $\delta$ about $z_\ell$. Since $\delta\lt1/4$, all its coordinates are positive. All first, second, and third coordinate derivatives of an individual reciprocal have absolute values at most $1$, $2$, and $6$, respectively, on this ball. The numerator is constant and each denominator slope is zero or one, which proves these bounds by direct differentiation.

Each entry of $D\Psi_0$ changes by at most $6Cn\delta$ on the ball; summing at most $n$ entries in a row gives

$$ \lVert D\Psi_0(z)-J_\ell\rVert_\infty\leq K\delta,\qquad \lVert D\Psi_\eta(z)-D\Psi_0(z)\rVert_\infty\leq\eta K_1. $$

Also $\lVert\Psi_\eta(z_\ell)\rVert_\infty\leq\eta A$, because only the first block of the rescaled gradient can be nonzero at the center.

Consider $T_{\ell,\eta}(z)=z-J_\ell^{-1}\Psi_\eta(z)$. The explicit choices of constants give

$$ \begin{aligned}\lVert DT_{\ell,\eta}(z)\rVert_\infty&\leq L(K\delta+\eta K_1)\lt\frac14+\frac18=\frac38,\cr \lVert T_{\ell,\eta}(z_\ell)-z_\ell\rVert_\infty&\leq L\eta A\lt\frac\delta4.\end{aligned} $$

The line segment between any two points in the ball stays in the ball. Integrating the derivative along that segment proves that $T_{\ell,\eta}$ is Lipschitz with constant at most $3/8$. For any point of the ball, its image is at distance at most $\delta/4+3\delta/8=5\delta/8$ from the center. Thus $T_{\ell,\eta}$ maps the complete closed ball into itself and is a contraction.

Banach's fixed-point theorem gives a unique point $z_\ell(\eta)$ in this ball with $\Psi_\eta(z_\ell(\eta))=0$. At $\eta=\varepsilon\gt0$, this is exactly $\nabla F=0$: the first block of $\Psi_\varepsilon$ is $\varepsilon$ times the first block of $\nabla F$, and the second blocks agree.

The derivative estimate also proves that $D\Psi_\varepsilon$ is nonsingular at this point. Indeed, if it annihilated a vector $v$, then $v=(I-J_\ell^{-1}D\Psi_\varepsilon)v$ would imply $\lVert v\rVert_\infty\leq(3/8)\lVert v\rVert_\infty$, so $v=0$. Multiplying its first $d$ rows by $\varepsilon^{-1}$ gives the Hessian of $F$, which is consequently nonsingular.

Distinct grid centers differ by at least one in a selector coordinate. Their balls of radius $\delta$ are disjoint, since $2\delta\lt1$. The critical points therefore number at least $q^k$. This proves the theorem with the explicitly specified scale $M$. $\blacksquare$

## Consequence for the rejected counting route

Apply the same functional to a sum of $H$ independent reciprocal heads. The parameter function is a sum of $H$ copies of $F$, so its Hessian is block diagonal and there are at least $q^{kH}$ nondegenerate critical points. After quotienting by head permutations there remain at least $q^{kH}/H!$ parameter orbits.

For $n=2r$ and $H=\lfloor c2^n/n^2\rfloor$, where $c\gt0$ is fixed, the logarithm to base two of this last lower bound is at least $(c/4+o(1))2^n$. Thus a general bound of order $\exp(O(nH\log n))$ for these full-domain critical points is false, even in the critical width regime of the question.

Every underlying score is nevertheless a sum of strictly positive heads. All such scores have the same Boolean labels. The new construction closes the critical-point shortcut; it supplies no bound on the number of actual coordinate sign patterns and does not establish the requested unboundedness of $n^2W(n)/2^n$.

## The logarithmic stationarity formulation also fails

The same stabilization gives a separate counterexample for the logarithmic potential arising in stationarity equations. In this paragraph take $q=N-1$, let $Q(t)=\prod_{\ell=1}^q(t-\ell)$, keep $D(t)=\prod_{v=1}^N(t+v)$, and put

$$ \lambda_s=\frac{Q(-c_s)}{\prod_{v\neq c_s}(v-c_s)},\qquad f_{\log}(a,t)=\sum_s\lambda_s\log\left(1+\sum_i a_i s_i+t\right). $$

Partial fractions now give $\partial_t f_{\log}(a^0,t)=Q(t)/D(t)$. At each specified integer root its second derivative is $Q'(\ell)/D(\ell)$, whose absolute value is at least $1/D(q)$.

Use the logarithmic stabilizer

$$ G_{\log}(a)=\sum_i A_i\log(1+a_i)-N\log\left(1+\sum_i a_i\right). $$

Its gradient vanishes at $a^0$ and its Hessian is $-B/2$, so its inverse norm is at most $2g$. The mixed profile Hessian entries have absolute value at most $C_f=\sum_s|\lambda_s|$. The first three coordinate derivatives of a logarithm of any of these affine denominators have absolute values at most $1$, $1$, and $2$ on the positive domain.

Consequently all the contraction estimates above hold with $C_G=\sum_i A_i+N$, $C=1+C_f+C_G$, and

$$ L=1+2g+D(q)(1+2dC_fg). $$

Keep the same formulas for $K,A,K_1,\delta,\varepsilon,M$. The block inverse estimate uses $|\alpha_\ell|^{-1}\leq D(q)$; positivity of these second derivatives is unnecessary for the contraction or invertibility proof. Hence $M G_{\log}(a)+\sum_j f_{\log}(a,t_j)$ has at least $(2^d-1)^k$ distinct nondegenerate critical points in the full positive domain. It is a weighted sum of logarithms of cube denominators. A proposed bound $\exp(O(n\log n))$ for those critical points is therefore also false.

## Lifting to free numerator parameters

The logarithmic version gives a further, separate conclusion that includes every normalized numerator coordinate. Write its potential as

$$ \Phi(b)=\sum_{x\in\lbrace0,1\rbrace^n}\mu_x\log(1+b\cdot x),\qquad b\in\mathbb R_{\gt0}^n. $$

The preceding construction specifies all coefficients $\mu_x$ and proves at least $(2^d-1)^k$ distinct nondegenerate critical points. Adding a coefficient at the zero input changes neither the potential nor any of its derivatives, because $\log(1+b\cdot0)=0$. We may therefore require $\sum_x\mu_x=0$.

Consider all normalized numerator and denominator slopes in the genuine score family

$$ S_{u,b}(x)=1+\frac{u\cdot x}{1+b\cdot x},\qquad u\in\mathbb R^n,\quad b\in\mathbb R_{\gt0}^n. $$

The same fixed linear functional of its evaluation table is

$$ \mathcal F(u,b)=\sum_x\mu_x S_{u,b}(x)=u\cdot\nabla\Phi(b). $$

If $b^{\ast}$ is one of the nondegenerate critical points of $\Phi$, then $(0,b^{\ast})$ is a critical point of $\mathcal F$: its numerator gradient is $\nabla\Phi(b^{\ast})=0$, and its denominator gradient is $\nabla^2\Phi(b^{\ast})0=0$. Put $J=\nabla^2\Phi(b^{\ast})$. Its full Hessian is

$$ \nabla^2\mathcal F(0,b^{\ast})=\left(\begin{array}{cc}0&J\cr J&0\end{array}\right). $$

This matrix is nonsingular. An element $(v,w)$ of its kernel satisfies $Jw=Jv=0$, hence $v=w=0$. Thus there are at least $(2^d-1)^k$ nondegenerate critical points in all $2n$ normalized parameters. This conclusion uses the logarithmic lift, not the fixed-numerator reciprocal theorem alone.

For $H$ independent heads, use $S(x)=1+\sum_{h=1}^H(u_h\cdot x)/(1+b_h\cdot x)$. The functional is the sum of $H$ copies of $\mathcal F$, so the critical-point count is at least $(2^d-1)^{kH}$, with nonsingular block diagonal Hessian. Dividing this count by $H!$ still gives a lower bound for parameter orbits. At equal blocks and $H=\lfloor c2^n/n^2\rfloor$, its base-two logarithm is at least $(c/4+o(1))2^n$.

At every one of these full-parameter critical points, all numerator vectors vanish and the score is identically one. The construction therefore also refutes the proposed small count in the full normalized parameter domain, while still producing only one Boolean function. Counting distinct images or regular image points is a different question, not answered by this example.

## Audit status

The proof above is a written mathematical proof, including the explicit simultaneous contraction bounds. It is not claimed as an end-to-end Lean theorem. `HeadComplexity.StabilizedReciprocalSaddles.hessian_kernel_trivial`, `radius_budget`, `perturbation_budget`, and `total_contraction_budget` formalize the nonsingularity calculation and scalar budget inequalities. `cross_hessian_kernel_trivial` verifies the block nonsingularity used in the free-numerator lift. Their axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. `verify_stabilized_saddles.py` checks the rational scalar identities, inverse matrix, and numerical inequalities in dimensions $d=2,3,4,5$ for both the reciprocal and logarithmic constructions. It checks the ingredients of the proofs; it does not enumerate the perturbed algebraic critical points.
