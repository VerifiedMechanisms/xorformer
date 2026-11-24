# An all-orders sparse lift with one Boolean coordinate

## Exact three-for-one lift

Let $\mu=\sum_{h=1}^H c_h\delta_{(a_h,b_h)}$ be a signed finite measure of affine direction coefficients. Its two Boolean projections are $a_h$ and $a_h+b_h$. Suppose their moments vanish through an arbitrary order $q$:

$$ \sum_h c_h a_h^k=\sum_h c_h(a_h+b_h)^k=0\qquad(0\leq k\leq q). $$

Define

$$ \nu=\sum_h c_h\bigl(\delta_{(a_h,0)}+\delta_{(0,a_h+b_h)}-\delta_{(0,a_h)}\bigr). $$

The support of $\nu$ has at most $3H$ points, independently of $q$. For every scalar function $F$ and both Boolean inputs,

$$ \sum_h c_h F(a_h+b_hx)=\int F(u+vx) d\nu(u,v). $$

At $x=0$, the second and third terms cancel. At $x=1$, the first and third terms cancel. Thus $\mu-\nu$ is an exact universal projection ghost, not merely a finite-order moment correction.

Every ordinary monomial moment of $\nu$ through degree $q$ vanishes. A mixed monomial $u^rv^s$ with $r,s\gt0$ vanishes on both axes. A pure $u$ moment is the corresponding moment of $a_h$. A pure $v$ moment is the difference of the moments of $a_h+b_h$ and $a_h$. The constant moment vanishes by the order-zero hypothesis.

The declarations `scalar_kernel_identity`, `finite_kernel_identity`, and `ordinary_moment_zero` in `HeadComplexity/Research/OneCoordinateMomentLift.lean` check these statements for arbitrary real coefficients and arbitrary order.

## Positivity and the original heads

If $a_h,b_h\gt0$, choose $t\gt0$ smaller than every $a_h$. The translated-axis version replaces each direction by

$$ (a_h,t),\qquad(t,a_h+b_h-t),\qquad(t,a_h), $$

with signs $+,+,-$. All coordinates are strictly positive, and the same two direct cancellations prove exact projection equivalence. These assertions are kernel checked as `positive_axis_kernel_identity` and `positive_axis_coordinates`.

For the ordinary-moment conclusion, subtract $(t,t)$ from the original directions. The two projected values are shifted by $t$ and $2t$, so their moments through $q$ still vanish by the binomial theorem. Apply the axis construction and translate back. Translation preserves vanishing of all ordinary moments through a fixed total degree, again by the binomial theorem. This last translation argument is a written proof; the kernel-checked moment declaration uses the unshifted axes.

The direction variable can depend on one selected Boolean coordinate in a larger cube, while the common positive base denominator depends on all coordinates. Every scalar-kernel identity then applies pointwise after including the remaining coordinates in $F$. For reciprocal heads, a strictly positive common affine base and sufficiently small direction scale keep all constructed denominator coefficients strictly positive. No rescaling claim about relative margin is made.

## First failure of the coordinate-axis extension

Two independent Boolean coordinates already invalidate the direct axis argument. Let

$$ \lambda=\delta_{(0,0)}-\delta_{(1,0)}-\delta_{(0,1)}+\delta_{(1,1)}. $$

Its coordinate projections are both zero measures and its total mass is zero, but its projection along $(1,1)$ is $\delta_0-2\delta_1+\delta_2$, which is nonzero. Every signed measure supported on the two coordinate axes satisfies

$$ \pi_{(1,1)}\nu=\pi_{(1,0)}\nu+\pi_{(0,1)}\nu-\nu(\mathbb R^2)\delta_0. $$

Hence no axis-supported measure, of any support size, has all three projection measures of $\lambda$. Tensor finite differences give the same obstruction while annihilating arbitrarily many initial moments. This rules out only the proposed axis reduction. Such examples already have ordinary low-order moment cancellation themselves, so they do not refute sparse lifting onto arbitrary new support.

## Remaining unrestricted access lemma

The open version allows arbitrary direction clouds in $\mathbb R^{n+1}$, all anchored Boolean projections $(1,x)$, arbitrary affine numerator residues, and order as large as the margin argument requires. It asks for an exact projection-equivalent measure with ordinary moment cancellation and at most a constant multiple of the original support. The finite positive-grid construction proves an additive $\binom{n+1+q}{q}$ bound, while the present special case removes dependence on $q$ only with one effective Boolean coordinate.

Even a general sparse lift would still need a truth-table-preserving access theorem for the original model. Exact ghost removal alone does not improve the relative margin, and straight common-base collisions already have the separate exponential transfer proved in the inherited `RadialMomentTransfer` module. Curved paths, several bases, and collective signed cancellation remain outside the present result.
