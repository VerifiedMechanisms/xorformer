# An Elliptic Identity for Normalized Head Tables

## Statement

Fix any real table $a_x$, not identically zero, on the Boolean cube. In particular, $a_x$ can be any nonzero affine numerator allowed by the manuscript. For positive denominator slopes $b_i$, put

$$ D_x=1+\sum_i b_ix_i,\qquad T_x=\frac{a_x}{D_x},\qquad G=\sum_xT_x^2,\qquad \rho=\sqrt G,\qquad U_x=\frac{T_x}{\rho}. $$

Only the denominator parameters vary in this statement. Set $B=\sum_i b_i$ and define

$$ A=\mathrm{diag}(b)+bb^\top,\qquad v_{xi}=\frac{x_i}{D_x},\qquad p_x=U_x^2,\qquad m_i=\sum_xp_xv_{xi}. $$

The matrix $A$ is positive definite. Every coordinate of $U$, and therefore every fixed linear functional $h=\sum_x\mu_xU_x$, satisfies the same elliptic equation

$$ \sum_{i,j}A_{ij}\partial_{ij}h+(2b-2Am)^\top\nabla h+Vh=0. $$

Its potential is the total denominator-parameter energy of the normalized table and obeys an exact dimension-independent bound:

$$ V=\sum_x(\nabla U_x)^\top A\nabla U_x=b^\top m-m^\top Am,\qquad 0\leq V\leq\frac{B}{4(1+B)}\lt\frac14. $$

Neither a norm bound on the numerator nor a lower bound on denominator conditioning is assumed. The assertion also applies to the negative-slope orientation after complementing every input bit and rescaling the denominator by its positive minimum.

This is an analytic identity for the allowed denominator family, not a head-count bound. It gives no bound here on the number of extrema or Boolean sign patterns.

## The unnormalized equation

Write $s_x=b^\top x$, so $D_x=1+s_x$. Since the numerator is fixed,

$$ \partial_iT_x=-\frac{a_xx_i}{D_x^2},\qquad \partial_{ij}T_x=\frac{2a_xx_ix_j}{D_x^3}. $$

Booleanity gives $x^\top A x=s_x+s_x^2=s_xD_x$. Therefore, for the operator $\mathcal L=\sum_{i,j}A_{ij}\partial_{ij}+2b^\top\nabla$,

$$ \mathcal LT_x=\frac{2a_x(s_x+s_x^2)}{D_x^3}-\frac{2a_xs_x}{D_x^2}=0. $$

For any nonzero vector $z$, the sum $z^\top Az=\sum_i b_iz_i^2+(b^\top z)^2$ is positive. Thus this is an elliptic operator in the interior. No assertion of uniform ellipticity up to the boundary is needed.

## Differentiating the full table normalization

The denominator is positive, $G\gt0$, and all functions are smooth. Direct differentiation gives

$$ \partial_i\log\rho=-m_i,\qquad \partial_iU_x=U_x(m_i-v_{xi}). $$

The second identity remains valid when $T_x=0$; it follows by the product rule, without taking a logarithm of that table entry. Consequently

$$ \begin{aligned} \sum_x(\nabla U_x)^\top A\nabla U_x &=\sum_xp_x(v_x-m)^\top A(v_x-m)\cr &=\sum_xp_xv_x^\top Av_x-m^\top Am. \end{aligned} $$

The product rule for $\mathcal L$, followed by $\mathcal LT_x=0$, gives

$$ \mathcal LG=2\sum_x(\nabla T_x)^\top A\nabla T_x,\qquad \frac{\mathcal L\rho}{\rho}=\sum_xp_xv_x^\top Av_x-m^\top Am=V. $$

Now apply the same product rule to $T_x=\rho U_x$:

$$ 0=\mathcal L(\rho U_x)=\rho\mathcal LU_x+U_x\mathcal L\rho+2(\nabla\rho)^\top A\nabla U_x. $$

Division by $\rho$ and substitution of $\nabla\log\rho=-m$ prove the claimed equation, first for each $U_x$ and then for every linear combination $h$.

## The Boolean sphere identity

The special bound on $V$ follows from a spherical identity that uses every input coordinate's idempotence:

$$ v_x^\top Av_x=\frac{s_x+s_x^2}{D_x^2}=\frac{s_x}{D_x}=b^\top v_x. $$

Thus $\sum_xp_xv_x^\top Av_x=b^\top m$. Nonnegativity of $V$ follows from its weighted variance expression above. To obtain the upper bound, set $c=1/(2(1+B))$ and let $\mathbf1$ denote the all-one vector. Expanding both sides gives the exact completion of squares

$$ b^\top m-m^\top Am=\frac{B}{4(1+B)}-(m-c\mathbf1)^\top A(m-c\mathbf1). $$

The subtracted term is nonnegative. Since $B\geq0$, the radius squared $B/(4(1+B))$ is strictly less than $1/4$. This proves all the bounds.

Equivalently, every $v_x$ lies on the same ellipsoid

$$ (v_x-c\mathbf1)^\top A(v_x-c\mathbf1)=\frac{B}{4(1+B)}. $$

The potential is the variance of these points under the probability weights $p_x$, measured in the positive metric $A$. This also proves that the bound does not depend on the signs of the numerator. $\blacksquare$

## What the equation does and does not imply

At a critical point of a normalized height $h$,

$$ \sum_{i,j}A_{ij}\partial_{ij}h=-Vh. $$

For positive $h$, this is compatible with a strict local maximum. The maximum principle for the unnormalized harmonic function therefore does not exclude the normalized maxima. In particular, the [two-maxima certificate](common-normal-maxima.md) is consistent with this identity.

No estimate counting extrema follows merely from the bounded potential. The parameter domain is noncompact, its ellipticity degenerates at the boundary, and the numerator and functional coefficients remain unrestricted. A theorem connecting this identity to a uniform count of coordinate sign patterns has not been established. That missing statement is not being treated as a routine analytic step or as completion of the asymptotic target.

There is also an exact obstruction to using this equation alone as a sign invariant. Fix any Boolean sign table $f_x\in\lbrace-1,1\rbrace$, set $b_i^0=1$, and choose the fixed numerator table

$$ a_x=f_x\left(1+\sum_i x_i\right). $$

Then $T(b^0)=f$, while the entire family still satisfies every elliptic and potential identity proved above. This numerator table is generally not affine, so it is not an allowed one-head representation. It proves that the differential identity and the bound $V\lt1/4$, by themselves, permit every Boolean sign table. Any useful continuation must combine them with an additional mechanism retaining the affine-numerator restriction and its behavior under sums of heads. This route is blocked at that specific missing mechanism.

## Verification scope

`formalization/HeadComplexity/Atoms/HeadEllipticEnergy.lean` proves the Boolean sphere identity, the general weighted energy variance identity, the exact square completion, and the potential bounds. Its declaration `spherical_variance_bounds` includes nonnegativity and the radius upper bound. The differentiation of actual normalized tables and the elliptic equation are the complete written calculation above, not a claimed Lean calculus theorem.

The independent exact-rational verifier computes first and second derivatives from the reciprocal formula at specified full-cube instances. It checks the unnormalized equation, normalized equation after multiplication by the positive norm, covariance identity, and upper bound. These finite checks supplement the general proof; they are not evidence for a sign-counting theorem.
