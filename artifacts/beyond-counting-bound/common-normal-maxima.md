# Two Strict Maxima for a Positive Table Functional

## Statement and scope

For $a\in\mathbb R^5$ and $b\in(0,\infty)^4$, let $F(a,b)$ be the entire sixteen-entry table

$$ F(a,b)_x=\frac{a_0+\sum_{i=0}^3 a_{i+1}x_i}{1+\sum_{i=0}^3 b_ix_i},\qquad x\in\lbrace0,1\rbrace^4. $$

There is an explicit vector $\mu\in(0,\infty)^{16}$ for which the linear functional $T\mapsto\mu^\top T$ has two distinct nondegenerate strict local maxima on the image of this family intersected with the full table unit sphere. The image is a smooth embedded eight-dimensional manifold near both points. Both tables are strictly positive at every cube input, and all denominator slopes are strictly positive. These affine ratios are admissible heads in the manuscript by its orientation proposition.

This refutes uniqueness of normalized height maxima, even for positive functional coefficients. It does not refute an asymptotic upper bound on their number, impose classification multiplier complementarity, or count different Boolean functions. The requested unboundedness of $n^2W(n)/2^n$ remains unproved.

## Explicit data

Take

$$ a=(4,2,3,8,4),\qquad b=(5,6,7,5),\qquad Q=23526481698720000. $$

Index cube inputs by $v=x_0+2x_1+4x_2+8x_3$. Let $s$ swap bits zero and one, and define $\mu_v=U_{\min(v,s(v))}/Q$ using this table.

| Orbit key | Integer numerator |
| --- | --- |
| 0 | 94039434467854061 |
| 1 | 24248710662032514 |
| 3 | 17735246144042184 |
| 4 | 38509282661611760 |
| 5 | 23039190515429166 |
| 7 | 16575541315683085 |
| 8 | 33885622517574840 |
| 9 | 18532006378272984 |
| 11 | 16772855163801190 |
| 12 | 20416280818149216 |
| 13 | 27438935605217136 |
| 15 | 30142128352400064 |

The second parameter point is

$$ a'=(4,3,2,8,4),\qquad b'=(6,5,7,5). $$

Write $T=F(a,b)$ and $T'=F(a',b')$. Then $T'_v=T _{s(v)}$. In particular, the functional is invariant under this swap, and

$$ \|T\|^2=\|T'\|^2=\frac{1940717578931993}{60213751101504},\qquad T_5=\frac{14}{13}\neq\frac{15}{14}=T'_5. $$

## Rational stationarity and curvature certificate

Put $Y_x=(1,x_0,x_1,x_2,x_3)$, $X_x=(x_0,x_1,x_2,x_3)$, $A_x=Y_xa$, and $D_x=1+X_xb$. Parameter coordinates are ordered as the five numerator coefficients followed by the four denominator coefficients. The derivative matrix is

$$ J_x=\left(\frac{Y_x}{D_x},-\frac{T_xX_x}{D_x}\right). $$

Direct exact rational evaluation gives

$$ J^\top(\mu-T)=0,\qquad \mu^\top T=\|T\|^2. $$

For $E(a,b)=\frac12\|\mu-F(a,b)\|^2$, its Hessian at the specified point has the following blocks:

$$ H_{aa}=\sum_x\frac{Y_x^\top Y_x}{D_x^2},\qquad H_{ab}=\sum_x\frac{(\mu_x-2T_x)Y_x^\top X_x}{D_x^2},\qquad H_{bb}=\sum_x\frac{(3T_x^2-2\mu_xT_x)X_x^\top X_x}{D_x^2}. $$

The off-diagonal block $H_{ba}$ is $H_{ab}^\top$. To check the formula, differentiate $F_x=A_x/D_x$: its numerator-numerator second derivatives vanish, its mixed second derivatives are $-Y_{xi}X_{xj}/D_x^2$, and its denominator-denominator second derivatives are $2T_xX_{xi}X_{xj}/D_x^2$. Thus the displayed matrix is exactly $J^\top J-\sum_x(\mu_x-T_x)\nabla^2F_x$.

The files [rational certificate](common-normal-maxima-certificate.json) and [factorization certificate](common-normal-maxima-rational-audit.json) give a unit lower triangular rational matrix $L$, its inverse, and a rational vector $p$ satisfying

$$ H=L\mathrm{diag}(p)L^\top,\qquad L^{-1}L=I,\qquad p_i\gt0\quad(0\leq i\lt9). $$

These are finite exact identities, rather than eigenvalue estimates. The Lean declarations `stationarity`, `hessian_factorization`, `lower_inverse_mul`, and `pivots_positive` check them by kernel computation from the explicit rational data. The declaration `realHessian_posDef` transports the factorization to the real numbers and deduces positive definiteness. The independent Python verifier reconstructs the derivative matrix and Hessian from the head formula, performs rational elimination, and checks the factorization entry by entry.

Consequently $E$ has a nondegenerate strict local minimum at $(a,b)$. The input-swap symmetry preserves $\mu$, the Euclidean norm, and the positive-slope domain, so the same holds at $(a',b')$.

## The image has a rational local inverse

The origin entry recovers $a_0=T_0$. Singleton and pair entries obey

$$ a_{i+1}=(1+b_i)T_{e_i}-T_0, $$

$$ (T_{e_i+e_j}-T_{e_i})b_i+(T_{e_i+e_j}-T_{e_j})b_j=T_{e_i}+T_{e_j}-T_0-T_{e_i+e_j}. $$

Use the four pairs $(0,1),(0,2),(0,3),(1,2)$. At the displayed table, the determinant of the four-by-four coefficient matrix for $b$ is $-23/3432$, as checked by `reconstruction_det`. It stays nonzero in an ambient table neighborhood. Solve those four linear equations for $b$, recover $a_0$ from the origin, and recover the other numerator coefficients from the singleton equations. This gives a rational inverse defined on that neighborhood for every table belonging to the head image.

In particular, there is no second local parameter branch converging to this table. Differentiating the inverse identity proves that $F$ has rank nine. The rank theorem and the inverse show that its image is a smooth embedded nine-dimensional manifold locally. The same reasoning applies at the swapped point.

## Restriction to the sphere

Let $r=\|T\|\gt0$. Scaling all numerator coefficients scales the entire table, so the derivative of $\|F\|^2$ along that parameter direction is $2r^2\gt0$. Thus $\|F\|=r$ is a regular hypersurface of the local nine-dimensional image.

On this hypersurface,

$$ E=\frac12\|\mu\|^2+\frac12r^2-\mu^\top F. $$

The ambient parameter gradient of $E$ vanishes, and its Hessian is positive definite. Its restriction to the eight-dimensional hypersurface therefore has a positive definite Hessian and a strict local minimum. The displayed identity gives a negative definite Hessian and a strict local maximum of $\mu^\top F$ on that hypersurface. Division by the same positive radius $r$ transports both points to the full table unit sphere and preserves these properties. The two normalized tables are distinct because their norms agree and their entries at vertex five differ. This proves the theorem. $\blacksquare$

## Audit boundary

The finite rational identities, real positive definiteness, symmetry, and reconstruction determinant are kernel checked in `formalization/HeadComplexity/Atoms/CommonNormalMaxima.lean`. The derivative formulas, rank theorem, second derivative test, and sphere restriction are the written analytic deduction above; the complete local-maximum theorem is not claimed as a Lean declaration.

The search used a common normal invariant under an input swap and linear matrix inequalities for the least-squares Hessian. Floating point search produced a candidate only. Rational projection onto the stationarity equations and an exact positive factorization supplied the certificate. A separate random multistart search that found no multiple maxima supplied no nonexistence evidence and is not used in the proof.
