# Independent audit of the log product duality calculation

## Verdict and scope

The radial/global subagent independently checked `log_product_tangents_and_duality.md`, including its final extension to every dimension. The statements are correct as written. This is a written mathematical audit, not Lean verification, and it supplies no unrestricted exponent improvement.

## Checks

The original score is the derivative of the logarithm of a product after absorbing its bias into one numerator. Positivity persists on the continuous cube because it is enough to check affine factors at the finitely many vertices. Strict denominator slope signs persist under sufficiently small perturbations. In the constant-denominator case, the original coherent numerator slopes give an admissible perturbation in either time direction. The note correctly declines to assert the converse for arbitrary paths through a constant denominator.

For fixed positive denominators and unrestricted affine numerators, strict Gordan duality gives exactly the displayed common nonnegative certificate. There is no missing bias equation: contracting any head equation with its denominator coefficient vector gives the signed total weight. The caveat about enlarging the numerator class at constant denominators is necessary and is present.

The gradient and Hessian of the signed logarithmic potential have the stated signs. The two-bit Hessian has eigenvalues $-1/18$ and $4/9$ at the indicated normalized coefficient vector.

For the stronger all-dimensional example, the weights are fixed at $lambda_x=1+|x|$ before differentiating the denominator parameters. At the all-ones denominator coefficient vector, the gradient is the parity sum against each affine coordinate, hence zero for $n\geq2$. Expanding the other Boolean coordinates under the elementary integral for the reciprocal gives diagonal and off-diagonal entries

$$ d=\int_0^1t(1-t)^{n-1}dt=\frac1{n(n+1)},\qquad o=-\int_0^1t^2(1-t)^{n-2}dt=-\frac2{(n-1)n(n+1)}. $$

Thus the normalized slope Hessian is $(d-o)I+oJ$. Its eigenvalues are $-1/[n(n+1)]$ on the all-ones direction and $1/[n(n-1)]$ on its perpendicular space. Both subspaces are nontrivial for $n\geq2$, so this is an actual interior critical-point saddle, not merely an indefinite Hessian away from criticality.

The note correctly separates this obstruction to a direct convexity argument from the still unresolved problem of controlling all simultaneous critical configurations or counting their Boolean labels.

## Exact vertex indicators and forced zero weights

The later indicator proposition also passes independent audit. If two values $(a+b)/(1+\varepsilon(r+a-b))$ coincide, irrationality of $\varepsilon$ forces the two integer numerators to agree. If this common numerator is nonzero, the integer expressions $r+a-b$ agree as well, determining the same pair. The only zero value occurs at the prescribed vertex.

Distinct positive parameters $\beta_h\lt\varepsilon$ give distinct simple denominator factors in the univariate rational interpolant. Its numerator degree is strictly smaller than its denominator degree, so its partial fractions have constant real residues and no polynomial part. Substitution gives exactly the stated indicator as a sum of affine ratios. Each denominator slope is $\varepsilon+\beta_h$ or $\varepsilon-\beta_h$, hence strictly positive.

Orthogonality to this exact table forces $\lambda_vF(v)=0$ and therefore $\lambda_v=0$ for every dual certificate. This is a statement about the fixed numerator span, not a claim that indicator sign labels themselves need polynomial width.
