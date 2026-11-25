# Joint approximate repair on Hamming layers

## Statement and status

Let $f$ be a sign table on $n\geq64$ Boolean coordinates. Suppose that, on every Hamming layer, $f$ is the strict sign of an affine function of the coordinates. This includes every original xorformer score whose denominators are affine functions of the common Hamming statistic $t(x)=\sum_i x_i$, with arbitrary head count, arbitrary affine numerators, both admissible denominator orientations, and arbitrary signed cancellation.

Set

$$ a=\left\lceil\frac n2-4\sqrt n\right\rceil,\qquad b=\left\lfloor\frac n2+4\sqrt n\right\rfloor,\qquad q=b-a+1\leq8\sqrt n+1. $$

There is a truth table $\widehat f$ agreeing with $f$ on at least $63/64$ of the full Boolean cube, represented by $q$ original admissible heads, with full-cube relative margin at least

$$ \gamma\geq\left[1+2(q-1)!q^2(n+1)(n+1)!(n+q)^{3q-1}\right]^{-1}=\exp(-O(n\log n)). $$

This is a written proof. Its bounded integer affine separator is kernel checked as `HeadComplexity.IntegerSeparatorMarginRepair.exists_bounded_integer_affine`; the Cauchy partial-fraction interpolation identities are kernel checked in `HeadComplexity.CauchyMomentInterpolation`. The selection of central layers, interpolation estimates, and final joint assembly below are not new Lean declarations.

The proof refits all affine layer scores jointly. It does not approximate each original head to the unknown original margin.

## Integer separators on the selected layers

For each integer $j\in[a,b]$, choose an affine function whose strict signs agree with $f$ on the layer $t=j$. Perturb its constant term by a sufficiently small amount to preserve all these strict signs and avoid zero on the entire finite cube. Extend the layer labels by the signs of this perturbed affine function. The integer affine separator theorem gives integers $c_{ji}$, for $0\leq i\leq n$, satisfying

$$ |c_{ji}|\leq M:=(n+1)!,\qquad f(x)\left(c_{j0}+\sum_{i=1}^n c_{ji}x_i\right)\geq1\quad\text{when }t(x)=j. $$

The perturbation and extension only select the integer coefficients. No labels outside the chosen layer are imposed by this step.

## One common positive pole bank

Put

$$ Q(t)=\prod_{h=1}^q(t+h),\qquad Q_{\max}=Q(n)\leq(n+q)^q,\qquad F=(q-1)!. $$

For each $0\leq i\leq n$, let $P_i$ be the unique polynomial of degree at most $q-1$ with

$$ P_i(j)=c_{ji}Q(j)\qquad(a\leq j\leq b). $$

All interpolation nodes are consecutive integers. The Lagrange denominator at node $j$ is, up to sign, $(j-a)!(b-j)!$, which divides $F$. Consequently $FP_i$ has integer coefficients. Define

$$ R(x)=\frac{P_0(t(x))+\sum_{i=1}^n x_iP_i(t(x))}{Q(t(x))}. $$

On every selected layer, $R$ is the bounded integer affine separator from the preceding section. Thus $f(x)R(x)\geq1$ there. On every vertex of the full cube, either $R(x)=0$ or

$$ |R(x)|\geq\frac1{FQ_{\max}}. $$

Set $\delta=1/(2FQ_{\max})$ and $S=R+\delta$. Then $S$ has absolute value at least $\delta$ everywhere, and retains the signs of $f$ on all selected layers. This is a full-cube gap for the eventual table $\widehat f=\mathrm{sgn}S$, including the unprescribed layers.

The partial-fraction identity gives

$$ R(x)=\sum_{h=1}^q\frac{r_{h0}+\sum_{i=1}^n r_{hi}x_i}{t(x)+h},\qquad r_{hi}=\frac{P_i(-h)}{\prod_{\ell\neq h}(\ell-h)}. $$

Every denominator is positive with all coordinate slopes equal to one. Every term is therefore an original admissible head, and $\delta$ is the free bias.

## Full-cube norm and accuracy bounds

Lagrange interpolation, $|c_{ji}|\leq M$, and the integer separation of the nodes give

$$ |P_i(-h)|\leq qM(n+q)^{2q-1},\qquad |r_{hi}|\leq qM(n+q)^{2q-1}. $$

Since $t+h\geq1$ throughout the cube, the total head norm is at most

$$ L=q^2(n+1)M(n+q)^{2q-1}. $$

The relative margin is at least

$$ \frac{\delta}{\delta+L}=\frac1{1+2FQ_{\max}L}\geq\left[1+2Fq^2(n+1)M(n+q)^{3q-1}\right]^{-1}. $$

For a uniform Boolean input, $t$ has mean $n/2$ and variance $n/4$. Chebyshev's inequality bounds the probability of lying outside the selected integer interval by $1/64$. Hence $\widehat f$ and $f$ agree on at least $63/64$ of the cube. Finally, $q=O(\sqrt n)$ and $\log((n+1)!)=O(n\log n)$ imply the asserted margin estimate.

## Exact limitation

The common statistic has only $n+1$ integer values, and almost all inputs occupy $O(\sqrt n)$ of them. An arbitrary weighted affine statistic can have $2^n$ distinct values on the cube, including throughout its typical range. Grouping nearby values is insufficient when arbitrary signed cancellation can place many sign changes inside one group. Thus this proof establishes a positive joint repair mechanism for the stated layer-affine class, without a repair theorem for unrestricted direction families.
