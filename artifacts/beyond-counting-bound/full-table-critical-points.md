# Many Critical Points Under Full Table Normalization

## Statement and scope

Let $d,k\geq2$, $n=d+k$, and $q=2^{d-1}-1$. For positive denominator coefficients $b$, define the zero-origin head table and its full table norm by

$$ T_{c,b}(x)=\sum_{i=1}^n c_i\psi_i(b,x),\qquad \psi_i(b,x)=\frac{(1+b_i)x_i}{1+b\cdot x},\qquad \|T\|^2=\sum_{x\in\lbrace0,1\rbrace^n}T(x)^2. $$

There is a fixed real linear functional of these tables with at least $q^k$ distinct nondegenerate critical points on the image of the normalized family $\|T_{c,b}\|=1$. The image is a smooth embedded manifold near every constructed point. All denominator coefficients are strictly positive. Adding the same bias two to each resulting table gives strictly positive Boolean scores.

The normalization uses every cube entry, rather than just singleton entries. The zero-origin numerator is the usual reduced numerator after its constant component has been absorbed into the free bias. The statement concerns the normalized nonconstant head table, not an additional free-bias direction on the same unit sphere.

This is an obstruction to a uniform small critical-point count, not the requested asymptotic head lower bound. In particular, it does not count different Boolean labels or establish many minima of a classification objective. For $d=k$, the logarithm in base two of the critical-point count is $(1/4+o(1))n^2$.

## The Gram matrix

Write $b=(a,t)$ with $d$ anchor coordinates and $k$ data coordinates. Define

$$ G_{ij}(b)=\sum_x\psi_i(b,x)\psi_j(b,x). $$

The matrix is rational and analytic on the positive orthant. Since $\psi_i(b,e_j)=\delta_{ij}$, every vector $v$ satisfies

$$ v^\top G(b)v=\sum_x\left(\sum_i v_i\psi_i(b,x)\right)^2\geq\sum_i v_i^2. $$

In particular, $G$ and every principal block are positive definite. Write its anchor and data blocks as $G_{AA},G_{AT},G_{TA},G_{TT}$. Full table normalization is precisely $c^\top Gc=1$.

## A rational potential with double zeros

Set $N=2^d$, $a_i^0=2^i$ for $0\leq i\lt d$, and

$$ Q(t)=\prod_{\ell=1}^q(t-\ell),\qquad D_\ast(t)=\prod_{v=2}^{N}(t+v),\qquad W(t)=\frac{Q(t)^2}{D_\ast(t)}. $$

For a binary anchor vector $s$, put $c_s=1+\sum_i2^is_i$. These constants run once through the integers from one to $N$. The proper rational function below has distinct simple poles, so its partial fractions define fixed rational coefficients $\kappa_s$:

$$ \frac{W(t)}{1+t}=\sum_s\frac{\kappa_s}{c_s+t}. $$

Explicitly, $\kappa_s=Q(-c_s)^2/\prod_{v\neq c_s}(v-c_s)$, where the product uses $1\leq v\leq N$. Define

$$ f(a,t)=\sum_s\kappa_s\log(1+a\cdot s+t). $$

Then $(1+t)\partial_t f(a^0,t)=W(t)$. At every integer $\ell$ from one to $q$,

$$ W(\ell)=W'(\ell)=0,\qquad W''(\ell)=2C_\ell,\qquad C_\ell=\frac{Q'(\ell)^2}{D_\ast(\ell)}\gt0. $$

All derivatives of $f$ used below are rational functions. The logarithms are only a convenient way to specify one linear functional of head tables.

## Choosing common amplitudes

For a grid tuple $\ell\in\lbrace1,\ldots,q\rbrace^k$, let $J_\ell=G_{TT}(a^0,\ell)$. Choose one rational vector $\eta$ satisfying, simultaneously at every grid tuple,

$$ \eta_j\neq0,\qquad (J_\ell^{-1}\eta)_j\neq0\quad(1\leq j\leq k),\qquad (1+\ell_1)(J_\ell^{-1}\eta)_1+(1+\ell_2)(J_\ell^{-1}\eta)_2\neq0. $$

Here is an explicit finite choice procedure. Take $\eta=(1,B,\ldots,B^{k-1})$ with positive integer $B$. Each forbidden condition involving $J_\ell^{-1}$ is a nonzero polynomial in $B$ of degree at most $k-1$: its coefficient row is nonzero because $J_\ell$ is invertible. There are $(k+1)q^k$ such polynomials. Therefore at least one integer in

$$ 1\leq B\leq (k-1)(k+1)q^k+1 $$

avoids all of their roots. Test these integers with exact rational arithmetic and choose the first successful one. The entries of $\eta$ are then positive, while the entries of $J_\ell^{-1}\eta$ need only be nonzero.

## Anchor stabilization

Put $A_i=1+2^i$ and define

$$ g(a)=\sum_i A_i\log(1+a_i)-N\log\left(1+\sum_i a_i\right),\qquad h_i(a)=(1+a_i)\partial_i g(a)=A_i-\frac{N(1+a_i)}{1+\sum_i a_i}. $$

At $a^0$, $h=0$ and

$$ H_{ij}=\partial_jh_i(a^0)=-\delta_{ij}+\frac{A_i}{N},\qquad (H^{-1})_{ij}=-\delta_{ij}+\frac{A_i}{d-1}. $$

The displayed matrices multiply to the identity, using $\sum_i A_i=N+d-1$. Thus $H$ is invertible.

For a small positive parameter $\delta$, introduce the potential

$$ \Phi_\delta(a,t)=\delta^{-4}g(a)+\sum_{j=1}^k\eta_j\log(1+t_j)-\delta^{-1}\sum_{j=1}^k\eta_j f(a,t_j). $$

Every logarithm here is the denominator at a specified Boolean input. Consequently there are fixed real coefficients $\mu_x$, rational whenever $\delta$ is rational, such that

$$ \Phi_\delta(b)=\sum_x\mu_x\log(1+b\cdot x),\qquad L(T)=\sum_x\mu_xT(x). $$

Define the weighted gradient $K_i=(1+b_i)\partial_i\Phi_\delta$. To express it, put

$$ U_i(a,t)=(1+a_i)\sum_j\eta_j\partial_{a_i}f(a,t_j),\qquad V_j(a,t)=\eta_j(1+t_j)\partial_t f(a,t_j). $$

Then

$$ K_A=\delta^{-4}h-\delta^{-1}U,\qquad K_T=v=\eta-\delta^{-1}V,\qquad L(T_{c,b})=c^\top K(b). $$

For fixed $b$, the positive critical value on the ellipsoid $c^\top Gc=1$ is

$$ \sqrt{E(b)},\qquad E(b)=K(b)^\top G(b)^{-1}K(b),\qquad c(b)=\frac{G(b)^{-1}K(b)}{\sqrt{E(b)}}. $$

It remains to construct nondegenerate critical points of $E$ with $E\gt0$.

## A single rescaled analytic system

Fix a grid tuple $\ell$. Use variables $z\in\mathbb R^d$, $w\in\mathbb R^k$, and $\zeta\in\mathbb R^d$, and set

$$ a=a^0+\delta^3z,\qquad t=\ell+\delta w,\qquad r_A=\delta^3\zeta,\qquad r_T=G_{TT}^{-1}(v-\delta^3G_{TA}\zeta),\qquad r=(r_A,r_T). $$

All matrices and derivatives in the following system are evaluated at $(a,t)$. A subscript on $U$ or $V$ denotes a derivative matrix; $G_{a_i}$ and $G_{t_j}$ denote derivatives of the full Gram matrix. Define

$$ F^{(1)}=\delta^{-3}h-U-\delta G_{AT}r_T-\delta^4G_{AA}\zeta. $$

For each data coordinate and each anchor coordinate, respectively, define

$$ F^{(2)}_j=-\delta^2(\partial_{t_j}U)^\top\zeta-\delta^{-1}(\partial_{t_j}V)^\top r_T-\frac12r^\top G_{t_j}r, $$

$$ F^{(3)}_i=(\partial_{a_i}h)^\top\zeta-\delta^3(\partial_{a_i}U)^\top\zeta-(\partial_{a_i}V)^\top r_T-\frac\delta2r^\top G_{a_i}r. $$

These functions extend analytically to $\delta=0$. Indeed, $h(a^0)=0$ makes $h(a^0+\delta^3z)$ divisible by $\delta^3$ in its convergent local power series. Also $V(a^0,\ell)=0$ and $V_t(a^0,\ell)=0$. Substitution of $a-a^0=\delta^3z$ and $t-\ell=\delta w$ makes $V$ divisible by $\delta^2$ and every data derivative of $V$ divisible by $\delta$. The remaining denominators are positive at the limit, and $G_{TT}$ is invertible there. This proves analytic extension without assuming uniform compatibility of separately chosen offsets.

Put $r^0=J_\ell^{-1}\eta$. The limiting system is

$$ F^{(1)}(0)=Hz-U(a^0,\ell), $$

$$ F^{(2)}_j(0)=-2\eta_j C_{\ell_j}r_j^0w_j-\frac12(r^0)^\top(\partial_{t_j}G_{TT})(a^0,\ell)r^0, $$

$$ F^{(3)}(0)=H^\top\zeta-V_a(a^0,\ell)^\top r^0. $$

It has an explicit rational solution: solve the first and third displayed linear systems with $H^{-1}$ and $H^{-\top}$, and solve each middle equation by division by $-2\eta_jC_{\ell_j}r_j^0$. Every divisor is nonzero by the amplitude choice. Its Jacobian in $(z,w,\zeta)$ is block diagonal with blocks

$$ H,\qquad \mathrm{diag}(-2\eta_jC_{\ell_j}r_j^0),\qquad H^\top. $$

Thus this Jacobian is invertible. The analytic implicit-function theorem supplies one nearby solution for every sufficiently small $\delta$. There are finitely many grid tuples. A common positive interval therefore works for all of them, preserves positivity of every denominator coefficient, and keeps all these Jacobians invertible. Choose one rational $\delta$ in that interval. This fixes the same functional $L$ for every branch.

## Exact criticality and Hessian nondegeneracy

For $\delta\neq0$, the equation $F^{(1)}=0$ is exactly the anchor block of $K=Gr$ multiplied by $\delta$. The data block holds by the definition of $r_T$. Hence $r=G^{-1}K$ on this equation.

Differentiating $E=K^\top G^{-1}K$ gives

$$ \frac12\partial_iE=(\partial_iK)^\top r-\frac12r^\top(\partial_iG)r. $$

Substitution of the displayed formulas for $K$ and $r_A$ shows, exactly,

$$ F^{(2)}_j=\frac12\partial_{t_j}E,\qquad F^{(3)}_i=\frac\delta2\partial_{a_i}E. $$

Thus every constructed solution is a critical point of $E$. Its value tends to $\eta^\top J_\ell^{-1}\eta\gt0$, so it is positive after a common reduction of the interval.

For fixed $(a,t)$, the derivative of $F^{(1)}$ in $\zeta$ is

$$ -\delta^4\left(G_{AA}-G_{AT}G_{TT}^{-1}G_{TA}\right). $$

The matrix in parentheses is the positive definite Schur complement of $G_{TT}$ in $G$. It is invertible. Eliminate $\zeta$ using this block. The remaining equations are the components of $\nabla E$, with invertible row scalings $1/2$ and $\delta/2$, and with invertible coordinate scalings $\delta^3$ and $\delta$ from $(z,w)$ to $(a,t)$. Since the full system Jacobian is invertible, its Schur complement is invertible. Therefore the Hessian of $E$ is invertible.

## Transfer to the normalized image

For fixed $b$, the positive constrained critical point of $c^\top K$ on $c^\top Gc=1$ is $c(b)$ as displayed above. Its Hessian in the tangent space of this ellipsoid is negative definite: the Lagrange multiplier calculation gives $-\sqrt E$ times the positive metric $G$. A smooth local orthonormal frame for $G$ gives ordinary product coordinates on the ellipsoid bundle. The Schur complement in those coordinates is the Hessian of the optimized value $\sqrt E$. At a critical point of $E$ it equals $\nabla^2E/(2\sqrt E)$, which is invertible. Thus the corresponding critical point of $L$ on the normalized parameter family is nondegenerate.

It remains to verify image regularity and distinctness, rather than merely parameter-space criticality. Singleton entries recover $c_i$ exactly. Pair entries obey

$$ (T(e_i+e_j)-c_i)b_i+(T(e_i+e_j)-c_j)b_j=c_i+c_j-T(e_i+e_j). $$

At a limiting branch, $c_A=0$ and $c_T=r^0/\sqrt{\eta^\top r^0}$. Use the pairs consisting of the first anchor and every data coordinate, every other anchor and the first data coordinate, and the first two data coordinates. These are $n$ linear equations for $b$.

To check their coefficient matrix, let $(\Delta a,\Delta t)$ be in its kernel. The anchor-data equations, with nonzero data coefficients, give

$$ a_i^0\Delta t_j=(1+\ell_j)\Delta a_i $$

on the selected pairs. Consequently, for one scalar $\lambda$,

$$ \Delta a_i=a_i^0\lambda,\qquad \Delta t_j=(1+\ell_j)\lambda. $$

The last pair equation becomes

$$ \frac{c_1(1+\ell_1)+c_2(1+\ell_2)}{1+\ell_1+\ell_2}\lambda=0. $$

Its coefficient is nonzero by the common amplitude choice. Hence the kernel is zero. Invertibility persists on each sufficiently small branch neighborhood, so these entries recover $b$ rationally and recover $c$ from singleton entries. The normalized table image is therefore smoothly embedded there, and critical-point nondegeneracy transfers to that image.

Two limiting images with different grid tuples are different. If their singleton entries differ this is immediate. Otherwise each common nonzero data singleton and its pair with the first anchor recover its data parameter from the strictly increasing ratio

$$ \frac{T(e_0+e_j)}{c_j}=\frac{1+\ell_j}{1+a_0^0+\ell_j}. $$

Thus equal tables would force equal grid tuples. Finitely many distinct limiting tables have positive minimum pairwise distance, so a further common reduction of $\delta$ keeps all resulting image points distinct.

Finally $\|T\|=1$ implies $|T(x)|\leq1$ at every cube vertex. The scores $2+T$ are all strictly positive, and each uses one admissible positive-denominator head and a free bias. This proves the theorem and its sign-count limitation. $\blacksquare$

## The critical points are saddles

The construction does not obstruct a bound that counts only local maxima. In fact its Hessian signature can be computed. For a grid tuple, put $m_\ell=|\lbrace j:r_j^0\gt0\rbrace|$. For all sufficiently small positive $\delta$, the Hessian of the height functional on the normalized image has exactly

$$ n-1+m_\ell\text{ negative eigenvalues},\qquad d+k-m_\ell\text{ positive eigenvalues}. $$

Both counts are positive. In particular every constructed critical point is a saddle.

**Proof.** Put $J=G_{TT}$ and $S=G_{AA}-G_{AT}J^{-1}G_{TA}$. These matrices are positive definite. Replace the anchor coordinates locally by

$$ p=K_A-G_{AT}J^{-1}v. $$

Completing the square in the block inverse of $G$ gives the exact identity

$$ E=p^\top S^{-1}p+v^\top J^{-1}v. $$

At the constructed critical point, $p=Sr_A=\delta^3S\zeta$. Also $p_a=\delta^{-4}H+O(\delta^{-1})$ there, with the same invertible limiting matrix $H$. Hence $(a,t)\mapsto(p,t)$ is a local diffeomorphism. All estimates below are at the constructed branch, with constants depending on its fixed grid tuple. The finitely many tuples allow one common sufficiently small interval.

Implicit differentiation of this coordinate change gives

$$ a_p=O(\delta^4),\qquad a_t=O(\delta^3),\qquad a_{pp}=O(\delta^8),\qquad a_{pt}=O(\delta^7),\qquad a_{tt}=O(\delta^3). $$

To check these orders directly, in the original coordinates $p_a=\delta^{-4}H+O(\delta^{-1})$, $p_t=O(\delta^{-1})$, $p_{aa}=O(\delta^{-4})$, and $p_{at},p_{tt}=O(\delta^{-1})$. Substitute these in the first and second derivatives of the identity $p(a(p,t),t)=p$. The inverse of $p_a$ is $O(\delta^4)$, proving each displayed estimate.

In the new coordinates, derivatives of $J$ and $S$ with respect to $t$ through order two stay bounded. Their first $p$ derivatives are $O(\delta^4)$ and their second $p$ derivatives are $O(\delta^8)$. The formula $v=\eta-\delta^{-1}V$ gives

$$ v_p=O(\delta^3),\qquad v_{pp}=O(\delta^7),\qquad v_{pt}=O(\delta^3),\qquad v_t=O(1),\qquad \delta v_{t_jt_l}\to-2\eta_jC_{\ell_j}\delta_{jl}e_j. $$

Here the last limit uses $V_{t_jt_j}(a^0,\ell)=2\eta_jC_{\ell_j}e_j$ and the vanishing of mixed original data derivatives. The terms introduced by differentiating $a(p,t)$ tend to zero after multiplication by $\delta$.

Differentiate the completed-square formula, using $p=O(\delta^3)$ and $v\to\eta$. If $\widetilde E(p,t)$ denotes the energy in these coordinates, the Hessian blocks satisfy

$$ \widetilde E_{pp}\to2S_\ell^{-1},\qquad \widetilde E_{pt}=O(\delta^3),\qquad \delta\widetilde E_{tt}\to-4\mathrm{diag}(\eta_jC_{\ell_j}r_j^0), $$

where $S_\ell$ is the limiting Schur complement. In the last block, only the two terms containing second derivatives of $v$ contribute to the limit; $J^{-1}\eta=r^0$. Congruence by $\mathrm{diag}(I_d,\sqrt\delta I_k)$ therefore makes the Hessian tend to the nonsingular block diagonal matrix

$$ \mathrm{diag}\left(2S_\ell^{-1},-4\mathrm{diag}(\eta_jC_{\ell_j}r_j^0)\right). $$

Its inertia is stable under sufficiently small perturbations. Since $\eta_j$ and $C_{\ell_j}$ are positive, the energy has $m_\ell$ negative and $d+k-m_\ell$ positive directions. At a critical point coordinate changes act on the Hessian by congruence, so this is also its inertia in the original denominator coordinates.

The numerator ellipsoid contributes $n-1$ negative directions. Its Schur complement is the Hessian of $\sqrt E$, which has the same inertia as the energy Hessian because $E\gt0$ and $\nabla E=0$. Sylvester's law of inertia gives the stated signature on the normalized parameter family. The local inverse from table entries already proved above transfers it to the image. $\blacksquare$

## Audit status

The preceding text is a complete written argument using the analytic implicit-function theorem. Its new ingredients are the full Gram metric, the common rational amplitude selection, and the single rescaled system with an explicit invertible limiting Jacobian. It does not assume that derivative offsets chosen at different grid points can be realized independently.

`FullTableCriticalPoints.lean` checks five algebraic ingredients: the Gram lower bound from singleton rows, the first and second energy differential identities, the weighted pair-reconstruction kernel, and the diagonal sharp-well kernel. Its declarations are `singleton_energy_bound`, `energy_differential_identity`, `energy_second_differential_identity`, `weighted_pair_kernel`, and `sharp_well_kernel`, in `HeadComplexity.FullTableCriticalPoints`. All use only standard foundational axioms. The complete analytic theorem above is not claimed as a Lean declaration.

`verify_full_table_critical_points.py` checks 654 limiting grid systems with exact rational arithmetic, including the common amplitude choices and all pair-reconstruction determinants. The tested dimensions are four through seven. These limiting checks are separate from existence of perturbed roots.

For a concrete perturbed instance, `certify_full_table_critical_points.py` certifies all nine branches with $d=3$ and $k=2$. It fixes $\delta=10^{-50}$ and uses boxes of radius $10^{-20}$ about the displayed rational limiting centers in the rescaled variables. Every interval operation rounds outwards using integer arithmetic at 1024 binary fractional digits. Let $A$ be the exact inverse limiting Jacobian. On each box the verifier checks

$$ \|I-A DF\|_\infty\lt\frac14,\qquad \|AF(\text{center})\|_\infty\lt\frac{10^{-20}}4. $$

The first inequality makes the Newton map a contraction; together they make it map the box strictly into itself. Banach's theorem gives a unique zero in each box, and the same derivative estimate proves Jacobian invertibility. The verifier also certifies positive coefficients, nonzero data entries, invertible pair-reconstruction matrices, and disjoint table-ratio intervals for different branches. Thus these are genuine distinct critical image points for one specified rational functional. This interval certificate is a checked arithmetic computation, not a Lean kernel certificate.

An additional interval calculation certifies positive anchor curvature at all nine actual roots. With $r=G^{-1}K$, direct differentiation gives

$$ E_{a_0a_0}=2(K_{a_0}-G_{a_0}r)^\top G^{-1}(K_{a_0}-G_{a_0}r)+2K_{a_0a_0}^\top r-r^\top G_{a_0a_0}r. $$

The verifier evaluates $\delta^8$ times this expression, using explicit first and second derivatives, and obtains a strictly positive lower endpoint on every certified root box. Combined with the negative numerator-fiber Hessian, this certifies that these nine concrete critical points are saddles. The general signature formula is a written analytic proof, not an additional Lean declaration or a claim that every eigenvalue of these concrete instances was interval enclosed.

The result still supplies no asymptotic head-count conclusion, and the scores obtained by adding bias two all have the same Boolean labels.
