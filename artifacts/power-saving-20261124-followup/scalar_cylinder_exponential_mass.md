# Scalar cylinder compilation with exponential amplitude

## Statement and scope

Let $C$ be a Boolean cylinder fixing $a$ coordinates to one and $b$ coordinates to zero, and put $r=\min(a,b)$. Its scalar indicator is uniformly approximable on the full cube, to every positive tolerance, by $\max(1,r)$ genuine original heads with zero bias and total full-cube amplitude at most

$$ M_r=\begin{cases}1&r=0,\cr(r+1)32^r&r\geq1.\end{cases} $$

The width assertion was already kernel checked in `HeadComplexity.ScalarCylinderCompiler.uniformlyAtomsApproximable_cylinder_min`. This note supplies a written quantitative amplitude bound that is independent of the approximation tolerance and the number of unused coordinates. The exact coefficient calculation and admissibility argument below are written proofs, not a new Lean declaration.

This is a scalar compiler. Multiplying its absorbed affine numerator by an additional arbitrary affine score can make that numerator quadratic; the width $r$ statement therefore does not automatically extend to affine-cylinder blocks.

## Exact integer-level profile

By simultaneously complementing all coordinates when necessary, assume that the cylinder has $r\geq1$ positive literals. Let $t$ count these literals, and set

$$ c_r=\binom{2r}{r},\qquad F_r(t)=c_r\frac{\prod_{\ell=0}^{r-1}(t-\ell)}{\prod_{j=1}^r(t+j)}. $$

At the integer levels $0,\ldots,r$, the function $F_r$ is exactly the indicator of $t=r$. The numerator vanishes at all smaller levels, while

$$ F_r(r)=\binom{2r}{r}\frac{r!}{(2r)!/r!}=1. $$

The simple, distinct positive poles give the partial-fraction identity

$$ F_r(t)=c_r+\sum_{j=1}^r\frac{d_j}{t+j},\qquad d_j=c_r\frac{\prod_{\ell=0}^{r-1}(-j-\ell)}{\prod_{h\neq j}(h-j)}. $$

In the denominator product, $h$ ranges over $1,\ldots,r$. The constant polynomial part is $c_r$ because numerator and denominator have equal degree and that leading-coefficient ratio.

The residues satisfy the exact factorial identity

$$ \frac{|d_j|}{j}=\binom{2r}{r}\frac{(r+j-1)!}{j!(j-1)!(r-j)!}=\binom{2r}{r}\binom{r+j-1}{j}\binom{r-1}{j-1}. $$

Using $\binom uv\leq2^u$ and $j\leq r$ gives

$$ \frac{|d_j|}{j}\leq2^{2r}2^{r+j-1}2^{r-1}\leq2^{5r-2}\leq32^r. $$

Also $c_r\leq4^r\leq32^r$. Consequently

$$ c_r+\sum_{j=1}^r\frac{|d_j|}{j}\leq(r+1)32^r. $$

The factorial denominators are essential for this estimate. Replacing every pole difference merely by its lower bound one would give the weaker $\exp(O(r\log(r+1)))$ estimate.

## Absorption and genuine-head gating

Let $z$ count the coordinates that the cylinder fixes to zero, and let $u$ count the unused coordinates. Absorb $c_r$ into the first reciprocal numerator, then use the $r$ ratios

$$ \Phi_1(x)=\frac{c_r(t(x)+1)+d_1}{t(x)+1+Rz(x)+\eta u(x)},\qquad \Phi_j(x)=\frac{d_j}{t(x)+j+Rz(x)+\eta u(x)}\quad(2\leq j\leq r). $$

Here $R,\eta\gt0$. Every denominator has a positive intercept and strictly positive slope in every coordinate. Each numerator is affine. Thus every ratio is an admissible original head, by `FracAtom.ofPositiveAffineRatio`.

On the face $z=0$, first let $\eta\to0^+$; the sum converges to $F_r(t)$. Outside that face, let $R\to\infty$; every numerator remains uniformly bounded on the finite cube while its denominator grows at least as $R$. Choosing sufficiently small $\eta$ and sufficiently large $R$ therefore approximates the cylinder uniformly to any prescribed positive tolerance.

The added denominator terms are nonnegative. Since $t\geq0$ everywhere, the individual norm estimates hold on the entire cube for every such $R,\eta$:

$$ \|\Phi_1\|_\infty\leq c_r+|d_1|,\qquad \|\Phi_j\|_\infty\leq\frac{|d_j|}{j}\quad(2\leq j\leq r). $$

Their total is at most $M_r$. No amplitude is hidden in a free bias. Simultaneously complementing every coordinate preserves the norms and exchanges the two allowed denominator orientations, proving the smaller-literal-count claim.

If $r=0$, the cylinder is an anchored face. The usual positive or negative coherent face approximation uses one constant-numerator head of norm at most one. The empty cylinder is handled by the same construction with the constrained coordinate set empty.

## Joint scalar scores and matching obstruction

Suppose $b+\sum_j a_j\mathbf1_{C_j}$ has signed gap at least one on the entire cube. Applying the construction to each scalar block with sufficiently small individual errors gives a genuine score of width

$$ K=\sum_j\max(1,r_j) $$

and relative margin at least

$$ \frac1{2\left(|b|+\sum_j|a_j|M_{r_j}\right)}. $$

Indeed the joint approximation error can be made less than $1/2$, and the complete original amplitude is bounded by the denominator in parentheses. Arbitrary signs of the coefficients and arbitrary signed cancellation are permitted. This is a positive construction for an explicitly given scalar-cylinder score, not an access theorem for arbitrary narrow original scores.

The lower bound in `mixed_point_high_order_amplitude.md` shows that the exponential dependence cannot in general be replaced by a polynomial independent of approximation tolerance. For a balanced mixed point with $r=s=m$, every arbitrarily accurate approximation at any width requires amplitude at least

$$ \frac{2^m}{(m+1)(4m+1)}. $$

The present upper bound $(m+1)32^m$ is therefore of the correct exponential order. Both bounds remain compatible with the $\exp(-\mathrm{poly}(n))$ margin scale sought by the comparison-counting route.

## Independent audit

The author of the kernel-checked scalar width compiler independently checked the central-binomial normalization, constant absorption, monotone denominator increase under gating, and strictly positive perturbation of unused-coordinate slopes. The quantitative construction passed that audit.
