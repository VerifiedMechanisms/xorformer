# Rational score spaces as tangent spaces of Hadamard powers

## Exact reformulation

Let $X=\lbrace0,1\rbrace^n$, and let $L\subseteq\mathbb R^X$ be the space of restrictions of affine functions. Fix $H\geq1$ affine denominators $B_1,\ldots,B_H$ which are positive on the full cube. Define their pointwise product $Q$ and the score space

$$ Q(x)=\prod_{h=1}^H B_h(x),\qquad V_B=\left\lbrace c+\sum_{h=1}^H\frac{A_h}{B_h}:c\in\mathbb R,\ A_h\in L\right\rbrace. $$

The constant is already in every summand space, since $1=B_h/B_h$. Consider the polynomial product map

$$ \Psi:L^H\to\mathbb R^X,\qquad \Psi(B_1,\ldots,B_H)=\prod_{h=1}^H B_h. $$

Its differential satisfies the exact identity

$$ D\Psi_B(A_1,\ldots,A_H)(x)=\sum_{h=1}^H A_h(x)\prod_{g\neq h}B_g(x)=Q(x)\sum_{h=1}^H\frac{A_h(x)}{B_h(x)}. $$

Consequently $V_B=\mathrm{diag}(Q)^{-1}\mathrm{im}D\Psi_B$. Since every $Q(x)$ is positive, these two linear spaces meet exactly the same strict orthants. This identity is elementary and holds at every parameter point, including singular points of the product map. At a generic parameter point its differential image is the tangent space of the Hadamard power $L^{\ast H}$, the Zariski closure of the coordinatewise products of $H$ vectors in $L$.

For original xorformer heads, each denominator has coherent slope signs and is positive on the whole cube. Thus every original score belongs to the displayed space for an admissible denominator configuration. The reformulation retains arbitrary signed numerators and target-dependent denominators. It does not authorize arbitrary positive affine denominators with mixed slope signs: allowing those gives a larger class.

When all denominator slopes are strictly positive, every affine numerator gives an original admissible head by `FracAtom.ofPositiveAffineRatio_eval`. The analogous statement holds after reflecting every input bit for a denominator with strictly negative slopes. At a constant denominator, allowing arbitrary affine numerators is an overapproximation of that exact parameter fiber. This distinction does not invalidate the upper-bound direction.

## The two-factor row matroid is known

For a query set $Y\subseteq X$, write $r(Y)$ for the rank of the affine evaluation rows $(1,x_1,\ldots,x_n)$ indexed by $Y$. The generic row matroid of $V_B$ for $H=2$ is completely determined: a set $I\subseteq X$ is independent if and only if

$$ |J|\leq2r(J)-1\qquad\text{for every nonempty }J\subseteq I. $$

This follows from Bernstein's theorem, proved again as Theorem 1.1 of [Antolini, Dewar, and Tanigawa](https://arxiv.org/html/2508.04798v1). It identifies the algebraic matroid of the Hadamard product of two linear spaces with the matroid induced by the sum of their rank functions minus one. Their Proposition 3.2 identifies its generic linear representation with the differential above. The same paper gives counterexamples to the direct extension for three or more arbitrary linear spaces.

The field issue causes no difficulty for this rank statement. Each relevant minor is a real polynomial after multiplying rows by nonzero products of denominators. A nonzero such polynomial cannot vanish throughout the open cone where every constant and slope coefficient is positive. Thus generic maximal ranks are attained within an admissible positive cone, as well as over the complex numbers.

For general $H$, the necessary inequalities

$$ |J|\leq H\bigl(r(J)-1\bigr)+1 $$

follow directly because the $H$ restricted spaces $\mathrm{diag}(B_h)^{-1}L|_J$ all contain the constant vector. They are not being asserted sufficient for arbitrary $H$. The cited counterexamples use differing linear spaces and do not, by themselves, settle the repeated Boolean affine space considered here.

Even a complete generic row-matroid description would not count the strict orthants of the union of these spaces as the denominators vary. Unoriented independence data forgets determinant signs, positive fibers, nongeneric degenerations, and the labels of unobserved cube vertices. This is the first missing step in using the matroid reformulation as an unrestricted capacity argument.

## A restricted probability interpretation

Suppose all denominator slopes are nonnegative, and normalize $B_h(1,\ldots,1)=1$. Write

$$ B_h(x)=p_{h,0}+\sum_{i=1}^n p_{h,i}x_i,\qquad p_{h,0}\gt0,\qquad p_{h,i}\geq0,\qquad\sum_{i=0}^n p_{h,i}=1. $$

For independent categorical variables $Z_h$ with probabilities $p_{h,i}$, and an input with active set $S$, one has

$$ Q(1_S)=\Pr\bigl(Z_h\in S\cup\lbrace0\rbrace\text{ for every }h\bigr). $$

Equivalently, the unique multilinear coefficients of $Q$ are the probabilities of the set of nonzero categories observed among the $H$ draws. They are nonnegative and sum to one. This follows by expanding the product and grouping choices with the same union of nonzero categories.

The score is a logarithmic directional derivative of this positive product. Its numerator directions are signed and need not define probability perturbations of a fixed size. The probability interpretation therefore does not bound the requested relative margin, and it does not prevent arbitrarily large cancellation. For mixed denominator orientations it applies separately to the two orientation groups after reflection, not to their joint product in a single common orientation.

## What would cross the barrier

Set $p=1+nH$. A sufficient geometric statement would control the additional strict orthants contributed while the positive-factorized tangent spaces vary by an entropy term of order $p\log n$, beyond the ordinary fixed-space term of order $p\log(N/p)$. In the critical regime $H=N/n^a$ with fixed $a\gt1$, both terms would be of order $nH\log n$.

No such control follows from the generic rank theorem above. General algebraic degree estimates for products of $H$ linear factors retain a logarithm of $H$ and return the existing order $n^2H$ entropy. A proof must use the actual Boolean coordinate evaluations and admissible positive factors, or a global feasibility condition on a chosen separating certificate.

Cardinality of an active query set alone does not supply a large address cube. Hamming balls with radius $n/2-\Theta(\sqrt{n\log n})$ have size $N/n^{\Theta(1)}$ but VC dimension only their radius. Such a set need not shatter $n-O(\log n)$ coordinates. Any argument selecting a near-full address cube from an active set therefore needs an additional hypothesis or a different certificate-selection theorem.

The differential identity and probability interpretation in this note are written proofs. The external two-factor matroid theorem has not been imported into Lean. No unrestricted lower bound is claimed here.
