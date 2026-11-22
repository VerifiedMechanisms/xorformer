# Many Regular Critical Points After Projective Normalization

## Statement and scope

Fix integers $d\geq2$ and $k\geq2$, and put $n=d+k$ and $q=2^{d-1}-1$. Consider the one-head tables

$$ T_{r,b}(x)=\frac{\sum_{i=1}^n r_i(1+b_i)x_i}{1+\sum_{i=1}^n b_ix_i},\qquad b_i\gt0,\qquad \sum_i r_i^2=1. $$

There is a fixed real linear functional of these tables having at least $q^k$ distinct nondegenerate critical points on their normalized image. Every point is in a neighborhood where the parameters have a rational inverse from the table entries. The corresponding one-head scores $1+T_{r,b}$ are strictly positive on the entire Boolean cube.

The normalization has an intrinsic meaning: $T_{r,b}(e_i)=r_i$, so it is precisely $\sum_iT(e_i)^2=1$. Every nonzero numerator direction has a unique positive radial rescaling satisfying it. This is a cross-section of the one-head direction family, not an additional assumption in the definition of head complexity.

This strengthens the earlier critical-point obstruction by producing distinct nonconstant tables at regular image points. It does not count distinct Boolean sign tables: all scores constructed here have the same sign. It also does not assert a result for normalization by the full truth-table Euclidean norm, or an independent-head product count on the summed image. Neither the requested lower bound nor an intermediate exponent follows.

## The scalar rational function

Use anchor coordinates $a_i$ indexed by $0\leq i\lt d$, and data coordinates $t_j$ indexed by $1\leq j\leq k$. Put

$$ N=2^d,\qquad a_i^0=2^i,\qquad A_i=1+2^i,\qquad Q(t)=\prod_{\ell=1}^q(t-\ell),\qquad D_{\ast}(t)=\prod_{v=2}^N(t+v). $$

The function

$$ R(t)=\frac{1-Q(t)^2/D_{\ast}(t)}{1+t} $$

is a proper rational function with distinct poles among $-1,\ldots,-N$. Its rational partial-fraction coefficients $\kappa_s$, indexed by $s\in\lbrace0,1\rbrace^d$, are uniquely specified by

$$ R(t)=\sum_s\frac{\kappa_s}{c_s+t},\qquad c_s=1+\sum_i2^is_i. $$

Explicitly, with $D(t)=(1+t)D_{\ast}(t)$ and $P(t)=D_{\ast}(t)-Q(t)^2$, the coefficient is $\kappa_s=P(-c_s)/D'(-c_s)$. The numbers $c_s$ run once through $1,\ldots,N$. Define

$$ f(a,t)=\sum_s\kappa_s\log\left(1+\sum_i a_is_i+t\right),\qquad v(a,t)=(1+t)\partial_t f(a,t). $$

At the anchor point, $v(a^0,t)=1-Q(t)^2/D_{\ast}(t)$. Hence for every $\ell\in\lbrace1,\ldots,q\rbrace$,

$$ v(a^0,\ell)=1,\qquad \partial_t v(a^0,\ell)=0,\qquad \partial_t^2v(a^0,\ell)=-\frac{2Q'(\ell)^2}{D_{\ast}(\ell)}\lt0. $$

These are exact rational identities, not approximate extrema.

## Transverse stabilization

Set

$$ G(a)=\sum_i A_i\log(1+a_i)-N\log\left(1+\sum_i a_i\right),\qquad h_i(a)=(1+a_i)\partial_iG(a). $$

Then $h(a^0)=0$. Its Jacobian $H=Dh(a^0)$ and inverse are

$$ H_{ij}=-\delta_{ij}+\frac{A_i}{N},\qquad (H^{-1})_{ij}=-\delta_{ij}+\frac{A_i}{d-1},\qquad \det H=(-1)^{d+1}\frac{d-1}{N}\neq0. $$

Indeed, $\sum_iA_i=N+d-1$, and multiplying the two displayed matrices gives the identity. For $\varepsilon\gt0$, define the logarithmic potential

$$ \Phi_\varepsilon(a,t)=\varepsilon^{-1}G(a)+\sum_{j=1}^k f(a,t_j). $$

Every term is a logarithm of the affine denominator at a specified Boolean input. Therefore there are fixed rational coefficients $\mu_x$ whenever $\varepsilon$ is rational such that $\Phi_\varepsilon(b)=\sum_x\mu_x\log(1+b\cdot x)$.

Define the weighted gradient and its squared norm by

$$ K_i(b)=(1+b_i)\partial_i\Phi_\varepsilon(b),\qquad E_\varepsilon(b)=\frac12\sum_iK_i(b)^2. $$

Write $r^{\mathrm{aux}}_i(a,t)=(1+a_i)\sum_j\partial_i f(a,t_j)$ and $v_j(a,t)=v(a,t_j)$. Thus the anchor part of $K$ is $\varepsilon^{-1}h+r^{\mathrm{aux}}$, and its data part is $v$.

For an auxiliary vector $z\in\mathbb R^d$, introduce the following analytic system, including at $\varepsilon=0$:

$$ \begin{aligned} \Psi^{(1)}(\varepsilon) &=h+\varepsilon r^{\mathrm{aux}}-\varepsilon^2z,\cr \Psi^{(2)}(\varepsilon) &=\varepsilon(D_t r^{\mathrm{aux}})^\top z+(D_tv)^\top v,\cr \Psi^{(3)}(\varepsilon) &=(Dh+\varepsilon D_a r^{\mathrm{aux}})^\top z+(D_av)^\top v.\end{aligned} $$

For each grid tuple $\ell\in\lbrace1,\ldots,q\rbrace^k$, at $\varepsilon=0$ this system has the solution

$$ a=a^0,\qquad t=\ell,\qquad z=-H^{-\top}(D_av(a^0,\ell))^\top\mathbf1. $$

Order the variables as $(a,t,z)$ and the equations as displayed. The Jacobian is block lower triangular with diagonal blocks $H$, $\mathrm{diag}(\partial_t^2v(a^0,\ell_j))$, and $H^\top$. In particular its determinant is

$$ (\det H)^2\prod_{j=1}^k\left(-\frac{2Q'(\ell_j)^2}{D_{\ast}(\ell_j)}\right)\neq0. $$

The analytic implicit-function theorem therefore gives one solution branch near each grid point for all sufficiently small positive $\varepsilon$. The grid is finite, so a single positive interval works for every branch. Choose disjoint neighborhoods of its distinct data tuples. Shrinking this interval keeps the solutions inside these neighborhoods and keeps every denominator coefficient positive.

For $\varepsilon\neq0$, the first equation uniquely eliminates $z$. On that equation the anchor part of $K$ equals $\varepsilon z$. Substitution into the other two equations gives exactly $\nabla_t E_\varepsilon=0$ and $\nabla_a E_\varepsilon=0$. The full Jacobian remains invertible on every branch. The eliminated block is $-\varepsilon^2I_d$, so the Schur-complement identity implies that $\nabla^2E_\varepsilon$ is invertible. Thus all the resulting critical points of $E_\varepsilon$ are nondegenerate. Moreover, their weighted gradients tend to $(0,\mathbf1)$ and hence are nonzero.

This use of the implicit-function theorem does not assume compatibility of a collection of prescribed offsets. The complete equations and their invertible Jacobian are displayed above. They are rational functions after differentiation. If a specified rational scale is desired, use disjoint rational boxes about the rational grid solutions, interval bounds for these Jacobians, and the contraction map $w\mapsto w-J_0^{-1}\Psi_\varepsilon(w)$. Repeatedly shrink the boxes and the dyadic positive scale until the derivative norm is at most $1/4$ and the center displacement is at most half the box radius. Continuity and the displayed invertibility ensure termination. Every bound in this search is a rational inequality.

## From squared norm to a linear height

For the fixed coefficients $\mu_x$ above, the linear functional of tables is

$$ L(T)=\sum_x\mu_xT(x),\qquad L(T_{r,b})=r\cdot K(b). $$

Let $b$ be one of the constructed critical points, let $\lambda=\|K(b)\|\gt0$, and put $r=K(b)/\lambda$. The sphere constraint on $r$ is satisfied. Its tangent derivative of $L$ vanishes, and its derivative with respect to $b$ is $\lambda^{-1}\nabla E_\varepsilon(b)=0$.

Here is the nondegeneracy calculation. Write $J=DK(b)$ and let $\Pi$ be orthogonal projection onto $r^\perp$. In tangent coordinates for the sphere, the constrained Hessian has upper-left block $-\lambda I$, off-diagonal block $\Pi J$, and lower-right block $\lambda^{-1}\sum_iK_i\nabla^2K_i$. Since $J^\top K=0$, its Schur complement is

$$ \frac1\lambda\left(\sum_iK_i\nabla^2K_i+J^\top\Pi J\right)=\frac1\lambda\left(\sum_iK_i\nabla^2K_i+J^\top J\right)=\frac1\lambda\nabla^2E_\varepsilon(b). $$

Both diagonal block and Schur complement are invertible. Hence these are nondegenerate critical points of the fixed linear functional on the normalized parameter family.

## Regularity and distinctness of the image points

Singleton values recover $r$ exactly. For a pair $i,j$, write $T_{ij}=T(e_i+e_j)$. The denominator parameters satisfy the linear equation

$$ (T_{ij}-r_i)b_i+(T_{ij}-r_j)b_j=r_i+r_j-T_{ij}. $$

At a limiting grid point, the anchor entries of $r$ are zero and all data entries equal $c=1/\sqrt{k}$. Use all pairs consisting of the first anchor and one data coordinate, all pairs consisting of any other anchor and the first data coordinate, and the pair of the first two data coordinates. There are exactly $k+(d-1)+1=n$ such equations.

Their coefficient matrix is invertible. To verify this directly, let $\delta a,\delta t$ belong to its homogeneous kernel. The anchor-data equations give

$$ a_i^0\delta t_j=(1+\ell_j)\delta a_i $$

for the selected pairs. The data-data equation gives $\delta t_1+\delta t_2=0$. Using the first anchor in both equations forces

$$ (2+\ell_1+\ell_2)\delta a_0=0. $$

All factors are positive. Thus $\delta a_0=0$, then all $\delta t_j=0$, and finally all other $\delta a_i=0$. Invertibility persists on sufficiently small neighborhoods of the finite set of grid points. The displayed linear system consequently recovers $b$ rationally from $r$ and the selected pair values there. This proves that the normalized table image is an embedded smooth manifold near each of the constructed points, and transfers the critical-point nondegeneracy to that image.

The limiting tables are distinct: their first-anchor/data values are

$$ T(e_0+e_j)=c\frac{1+\ell_j}{1+a_0^0+\ell_j}, $$

which are strictly increasing in $\ell_j$. Finitely many distinct limiting tables have a positive minimum pairwise distance. A further common reduction of $\varepsilon$ therefore keeps all the constructed image points distinct.

At the limits every numerator coefficient is nonnegative, so $1+T\geq1$ at every cube input. Continuity on the finite set of inputs and branches makes all the perturbed scores strictly positive as well. This proves the stated theorem. $\blacksquare$

## Growth and audit boundary

For $d=k$ the logarithm of the number of regular critical points is $(1/4+o(1))n^2$. This is a statement about one fixed linear functional on a specified projective cross-section. The branch count is not a count of distinct Boolean labels and does not prove the research target.

The general analytic construction, use of the implicit-function theorem, and image regularity argument are the written proof above. The accompanying exact verifier checks the partial fractions, scalar critical-point identities, transverse inverse and Jacobian determinants in finite instances. It checks 88 grid instances, including 37 full rescaled Jacobian determinants. It does not enumerate perturbed roots.

In `ProjectiveCriticalPoints.lean`, the declarations `transverse_kernel`, `selected_pair_kernel`, `schur_kernel`, and `projection_term_vanishes` verify the corresponding algebraic ingredients. Their namespace is `HeadComplexity.ProjectiveCriticalPoints`, and their axiom audit contains only the standard Lean foundational axioms. The entire analytic theorem is not a Lean declaration.
