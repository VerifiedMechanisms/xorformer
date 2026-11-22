# Positive Zero Grids of Score Functionals

## Statement and scope

Let $d\geq2$, $k\geq1$, $H\geq1$, and $q=2^{d-1}-1$. There is a family of admissible $H$-head scores on $n=d+k$ bits, with $kH$ free positive denominator coefficients, and a fixed linear functional of their cube evaluations whose zero set consists of exactly

$$ q^{kH} $$

isolated points in the positive parameter domain. Every point is a nondegenerate minimum. All these scores represent the constant-true Boolean function.

The linear functional mixes different input evaluations. It is not an individual classification predicate. The construction refutes small bounds on section complexity in parameter space that allow arbitrary linear functionals of the evaluation vector. It does not establish or refute the requested asymptotic bound on $W(n)$.

## A nonnegative rational function

Put $m=2q+1=2^d-1$ and define

$$ P(t)=\prod_{r=1}^q(t-r),\qquad D(t)=\prod_{j=1}^m(t+j),\qquad R(t)=\frac{P(t)^2}{D(t)}. $$

Since the poles are distinct and the numerator has degree $m-1$, partial fractions give the explicit identity

$$ R(t)=\sum_{j=1}^m\frac{\lambda_j}{t+j},\qquad \lambda_j=\frac{P(-j)^2}{\prod_{\ell\neq j}(\ell-j)}. $$

**Proof of the identity.** Multiplying by $D$ gives two polynomials of degree at most $m-1$. They agree at the $m$ distinct points $-1,\ldots,-m$, by the displayed residue formula. Their difference is therefore zero.

For $t\gt0$, the denominator is positive and the numerator is a square. Consequently,

$$ R(t)\geq0,\qquad R(t)=0\iff t\in\lbrace1,\ldots,q\rbrace. $$

At each such root, differentiation gives

$$ R'(r)=0,\qquad R''(r)=\frac{2P'(r)^2}{D(r)}\gt0. $$

The last inequality follows from distinctness of the roots of $P$.

## Admissible heads and the fixed functional

Write the input as $(x,y)\in\lbrace0,1\rbrace^k\times\lbrace0,1\rbrace^d$. For each head $h$, choose free parameters $t_{h,i}\gt0$ and set

$$ B_h(x,y)=1+\sum_{i=1}^k t_{h,i}x_i+\sum_{a=0}^{d-1}2^a y_a,\qquad S_t(x,y)=\sum_{h=1}^H\frac{1}{B_h(x,y)}. $$

Every denominator has strictly positive constant term and strictly positive slopes. The numerator is the constant one. Thus every summand is admissible in the manuscript's exact model, and $S_t$ is strictly positive on the whole cube.

Let $y(j)$ be the binary encoding of $j-1$, for $1\leq j\leq m$, and let $e_i$ be the $i$-th unit vector in the selector coordinates. Define a linear functional on real cube tables by

$$ \Lambda(v)=\sum_{i=1}^k\sum_{j=1}^m\lambda_j v(e_i,y(j)). $$

The binary representation gives $B_h(e_i,y(j))=t_{h,i}+j$, so the partial-fraction identity proves

$$ \Lambda(S_t)=\sum_{h=1}^H\sum_{i=1}^k R(t_{h,i}). $$

Every term on the right is nonnegative. Therefore the zero set in the positive parameter domain is exactly

$$ \lbrace t:\Lambda(S_t)=0\rbrace=\lbrace1,\ldots,q\rbrace^{H\times k}. $$

This finite Cartesian grid has $q^{kH}$ points. Its Hessian is diagonal, with strictly positive diagonal entries $R''(t_{h,i})$, at every zero. Hence all these zeros are isolated nondegenerate minima.

## Regular sections also have many components

Let $p=kH$. Around each grid point choose a small closed Euclidean ball lying inside the positive orthant. Because the grid is finite and the Hessian is positive definite at each point, continuity permits choosing these balls pairwise disjoint and the Hessian positive definite throughout each ball. The value of $\Lambda(S_t)$ is strictly positive on their boundaries. Choose $\varepsilon\gt0$ smaller than all these boundary minima.

On each ray from the center of any ball, the value starts at zero and increases strictly until it exceeds $\varepsilon$ at the boundary. Strict increase follows by integrating the positive second directional derivative, since the first derivative vanishes at the center. Thus the level $\Lambda(S_t)=\varepsilon$ inside each ball is a radial graph over the unit sphere. Its gradient is nonzero there. For $p\geq2$ it is a connected compact regular hypersurface; for $p=1$ it consists of two points. A connected component cannot leave its ball, since the level does not meet the boundary. There are therefore at least $q^p$ distinct components of this regular part of the affine section.

This persists on an open set of coefficients of the evaluation functional. To see this concretely, first decrease $\varepsilon$ if necessary so that every boundary value exceeds $3\varepsilon$. A sufficiently small coefficient perturbation changes the values and Hessians uniformly on the finite union of balls. Require the perturbed values at the old centers to be below $\varepsilon/2$, the boundary values to remain above $2\varepsilon$, and the Hessians to remain positive definite. Each ball then has a unique interior minimum, by compactness and strict convexity. The same ray argument from that minimum gives a compact regular level component at height $\varepsilon$ in each ball. Thus the obstruction is not removed by generic perturbation of the functional.

## Removing head permutations

There are $q^k$ possible parameter vectors for one head. Head-permutation orbits of the grid are multisets of $H$ such vectors, so their number is

$$ \binom{q^k+H-1}{H}\geq\frac{q^{kH}}{H!}. $$

This is a count of parameter orbits; no assertion that distinct orbits have distinct full score tables is needed.

Take $k=d$, $n=2d$, and $H=\lfloor C2^n/n^2\rfloor$ for a fixed $C\gt0$. Since $\log_2 q=d-1+o(1)$ and $\log_2 H=2d+O(\log d)$, the logarithm of the orbit count is at least

$$ H\bigl(d\log_2 q-\log_2 H\bigr)=\left(\frac C4+o(1)\right)2^n. $$

Thus an estimate that makes every such parameter preimage of a positive linear-functional section subexponential in the full cube size is false even after head permutations are removed. This obstruction is stronger at the critical head scale than the earlier independent pole-matching branch count. It still leaves bounds exploiting the specific coordinate sign tests open. No bound on the number of distinct score tables is inferred from the parameter count.

## Formal and arithmetic audits

`formalization/HeadComplexity/Atoms/PositiveFunctionalGrid.lean` proves the nonnegative partial-fraction construction, identifies the zero set of the coordinate sum, constructs an equivalence with the finite grid, and proves its exact cardinality. The declarations are `exists_nonnegative_reciprocal_with_zeros`, `sum_reciprocal_zero_iff`, `exists_positive_zero_grid_equiv`, and `exists_positive_zero_grid_card`, in namespace `HeadComplexity.PositiveFunctionalGrid`.

The binary embedding into actual heads, the Hessian calculation, the permutation-orbit count, and the asymptotic calculation are proved above in ordinary mathematics. They are not asserted to be Lean declarations.

The independent exact verifier `verify_positive_functional_grid.py` checks the residue identity and nondegenerate minima for an explicit rational instance, and checks the functional identity on its entire parameter grid.

## Literature connection

The initial search concerned positive critical points of master functions and the positivity assumptions in [Varchenko's formula as presented in Pachter and Sturmfels, Theorem 1.5](https://beckassets.blob.core.windows.net/product/readingsample/364152/9780521857000_excerpt_001.pdf). Positive likelihood weights give a concavity argument there. Our evaluation functional has signed residue weights, so that argument does not apply.

[Borchardt's determinant-permanent identity](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/EJC/Volume_11/PDF/v11i1r48.pdf) provides another way to prescribe critical points using squared Cauchy kernels. The construction above uses a squared numerator and elementary partial fractions, avoiding a dependence on that identity. No novelty claim is made for partial fractions or the Cartesian-product step.
