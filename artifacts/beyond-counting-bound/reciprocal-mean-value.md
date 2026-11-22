# An Exact Mean Value Identity in Denominator Parameters

## Statement and scope

For $b\in\mathbb R_{\gt0}^n$ and $x\in\lbrace0,1\rbrace^n$, put $K_x(b)=(1+b\cdot x)^{-1}$ and $s=\sum_i b_i$. For every $a\gt0$,

$$ K_x(b)=\frac{1}{1+s}K_x\left(\frac{b}{1+a}\right)+\sum_{i=1}^n\frac{b_i}{1+s}K_x(b+ae_i). $$

The coefficients are strictly positive and sum to one. They do not depend on $x$. Consequently the same identity holds for every fixed linear combination of cube evaluations. It also holds with any fixed numerator table multiplying the evaluations.

This identity concerns the full positive orthant of denominator coefficients. It does not hold after arbitrarily fixing some coefficients. It gives a new constraint to investigate, but no head-complexity lower bound is inferred from it.

## Proof of the identity

Write $B=1+b\cdot x$. The Boolean identity $x_i^2=x_i$ gives

$$ K_x\left(\frac{b}{1+a}\right)=\frac{1+a}{B+a},\qquad K_x(b+ae_i)=\frac1B-\frac{a x_i}{B(B+a)}. $$

Substitute these expressions into the claimed average. Its numerator over the common denominator $(1+s)B(B+a)$ is

$$ (1+a)B+s(B+a)-a(B-1)=(1+s)(B+a). $$

Division proves the identity. $\blacksquare$

## No nonconstant interior local extrema

Let $F(b)=\sum_x\lambda_x K_x(b)$, with arbitrary real coefficients. If $F$ has a local maximum or local minimum in the positive orthant, then $F$ is constant throughout that orthant.

**Proof.** It suffices to consider a local maximum at $b$. Choose an open ball around $b$ contained in the positive orthant, on which $F\leq F(b)$. For all sufficiently small $a\gt0$, every point in the averaging identity lies in this ball. Equality with a strictly positive weighted average then forces

$$ F(b+ae_i)=F(b) $$

for every coordinate $i$ and every sufficiently small $a\gt0$.

Each resulting point inside the ball is also a local maximum with the same value. Apply the identity again there. Repeating through the finitely many coordinate directions proves that $F$ is constant on a nonempty open box inside the ball. More explicitly, choose the side length of the box sufficiently small that all intermediate points and all rescaled points used by the identity stay in the original ball; compactness of a smaller closed ball and continuity of the finitely many transformations provide such a choice.

Multiplying $F-F(b)$ by the positive polynomial $\prod_x(1+b\cdot x)$ gives a polynomial vanishing on an open box. That polynomial is identically zero. Thus $F=F(b)$ on the full positive orthant. Applying the argument to $-F$ proves the minimum case. $\blacksquare$

The argument applies to fixed-numerator heads because their numerators can be absorbed into the coefficients $\lambda_x$. It applies to sums with independently varying denominator blocks as well: fix the other blocks, use the conclusion for one block, and continue through the finitely many blocks. This excludes local extrema in the full denominator parameter domain unless the functional is constant there.

## Differential form

Expanding the exact averaging identity at $a=0$, or differentiating directly, gives

$$ \mathrm{tr}\left((\mathrm{diag}(b)+bb^{\top})\nabla^2F(b)\right)+2b\cdot\nabla F(b)=0. $$

For a single kernel, $\partial_iK_x=-x_i/B^2$ and $\partial_{ij}K_x=2x_ix_j/B^3$. The contracted second derivative is therefore

$$ \frac{2\left(b\cdot x+(b\cdot x)^2\right)}{B^3}=\frac{2b\cdot x}{B^2}, $$

which cancels the drift term. Linearity proves the equation for $F$.

For every nonzero $v\in\mathbb R^n$,

$$ v^{\top}(\mathrm{diag}(b)+bb^{\top})v=\sum_i b_i v_i^2+(b\cdot v)^2\gt0. $$

Thus the equation is elliptic on the open positive orthant. The elementary proof above does not require invoking a general maximum-principle theorem.

Under $y_i=b_i/(1+\sum_jb_j)$, let $y_0=1-\sum_i y_i$. The second-order coefficient matrix becomes $y_0(\mathrm{diag}(y)-yy^{\top})$, and the transformed first-order terms cancel. Up to a positive scalar, this is the neutral Wright-Fisher diffusion operator on the simplex. The corresponding generator is described in the primary treatment by [Steinruecken, Wang, and Song, Section 2](https://pmc.ncbi.nlm.nih.gov/articles/PMC3568258/). This connection identifies the operator; no result about Boolean classification is imported from population genetics.

## Limitation for the selected target

The absence of local extrema does not bound the number of saddle points, nor the number of sign patterns of a vector-valued evaluation map. A mean of vectors lying outside an orthant can lie inside that orthant: $(2,-1)$ and $(-1,2)$ average to $(1/2,1/2)$. Consequently the averaging identity does not allow replacing a head by one of the averaged heads while preserving all labels.

The earlier positive zero grids fix the address coefficients and vary only selector coefficients. Such affine slices need not satisfy this elliptic equation in their free coordinates. There is no conflict between their isolated minima and the full-domain result proved here.

No theorem converting this identity into the required unbounded improvement over $2^n/n^2$ has been proved. That conversion remains a substantive gap, rather than an implicit consequence of the averaging formula.

## Formal audit

`HeadComplexity.ReciprocalMeanValue.reciprocal_mean_value`, in `formalization/HeadComplexity/Atoms/ReciprocalMeanValue.lean`, proves the exact finite averaging identity for every Boolean input, every dimension, and all strictly positive coefficients and increments. The local-extremum theorem, the differential equation, and the coordinate change are proved above in ordinary mathematics and are not asserted to be Lean declarations.
