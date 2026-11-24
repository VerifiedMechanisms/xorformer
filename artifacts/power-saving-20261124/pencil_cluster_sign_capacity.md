# Sign capacity with a linear parameter block

## Status and scope

This note independently checks the partially linear sign-count proof supplied in the continuation context and records its exact-pencil applications. It proves restricted results only. No statement below gives the requested improvement for unrestricted affine-ratio heads.

The original score is $c+\sum_{h=1}^H A_h(x)/B_h(x)$ on $X=\lbrace0,1\rbrace^n$, with $N=2^n$. Every actual denominator is positive on the cube and satisfies the original coherent-slope rule. Allowing arbitrary affine numerators when enlarging a family is valid for an upper bound on its capacity, including when some original denominators are constant.

The proof uses Sard's theorem and the multihomogeneous Bezout bound. The version bounding isolated roots even when other components are positive dimensional is stated as Theorem 1.69, printed page 49, in [Spaenlehauer's thesis](https://members.loria.fr/PJSpaenlehauer/data/these_spaenlehauer.pdf). That statement was opened and independently checked in this run on 2026-11-24. No Lean verification is claimed.

## Theorem 1. A partially linear sign bound

Let $f_1,\ldots,f_m$ be real polynomials in $a\in\mathbb R^L$ and $b\in\mathbb R^q$, of degree at most one in the whole block $a$ and degree at most $D\geq1$ in the whole block $b$. Put $p=L+q\geq1$. The number $T$ of strict sign vectors satisfies

$$ T\leq (2D)^q\binom{2p}{q}\sum_{j=0}^{p}2^j\binom mj. $$

If $p\leq m$ and $q\gt0$, then

$$ T\leq\left(\frac{2em}{p}\right)^p\left(\frac{4eDp}{q}\right)^q. $$

When $q=0$, omit the second factor. The case $p=0$ is separate and has at most one strict sign vector.

**Proof.** Choose one parameter witness for every realized strict sign vector. Their number is finite. Therefore one number $\varepsilon_0\gt0$ is smaller than the absolute value of every evaluation at these witnesses. For a positive vector $\varepsilon\in(0,\varepsilon_0)^m$ and each realized sign vector $\sigma$, the closed set

$$ K_\sigma=\lbrace z:\sigma_i f_i(z)\geq\varepsilon_i\text{ for every }i\rbrace $$

is nonempty.

Choose $\varepsilon$ so that every nonempty level set $f_i(z)=\tau_i\varepsilon_i$, indexed by at most $p$ distinct indices, is regular, and no set of $p+1$ such equations has a solution. Sard's theorem supplies this choice. For each fixed index set and sign assignment, the exceptional target values have measure zero; their inverse image under the relevant coordinate projection is null inside the bounded threshold box. There are only finitely many index sets and assignments. For $p+1$ equations, a regular value of the map from $\mathbb R^p$ has empty preimage.

Choose a center $u\in\mathbb R^p$ so that squared distance $Q_u(z)=\lVert z-u\rVert^2$ has only nondegenerate critical points on every nonempty regular level manifold just obtained. This is Sard's theorem for the normal-bundle endpoint map $(z,v)\mapsto z+v$. The family of manifolds is finite. Their possible noncompactness does not invalidate this regular-value argument.

The function $Q_u$ is coercive, so it attains a minimum on every nonempty closed set $K_\sigma$. Let $I$ be the active constraints at a chosen minimum and let $j=|I|\leq p$. Their gradients are independent. Consequently unique multipliers satisfy

$$ f_i(z)=\sigma_i\varepsilon_i\quad(i\in I),\qquad \nabla Q_u(z)=\sum_{i\in I}\lambda_i\nabla f_i(z). $$

The constrained Hessian is nonsingular by the choice of $u$. The square KKT system has nonsingular Jacobian: its constraint rows force the parameter part of a kernel vector into the active tangent space, its gradient rows projected to that tangent space kill that part, and gradient independence then kills the multiplier part. A nonsingular real root is an isolated complex root.

A selected point determines its full sign vector, since every evaluation there has magnitude at least its positive threshold. Thus distinct sign patterns yield distinct selected parameter points. The active signs are the only signs that must be enumerated when counting the systems.

For fixed $I$ and its signs, group the unknowns as $(a,\lambda)$ of dimension $L+j$ and $b$ of dimension $q$. The $j$ constraint equations and the $L$ stationarity equations in $a$ have bidegree at most $(1,D)$. Each of the other $q$ stationarity equations has bidegree at most $(2,D)$: the multiplier times a derivative with respect to $b$ has degree at most two in $(a,\lambda)$ and at most $D-1$ in $b$, while the distance derivative is linear in $b$.

The multihomogeneous Bezout bound is the coefficient of $U^{L+j}V^q$ in

$$ (U+DV)^{L+j}(2U+DV)^q. $$

That coefficient satisfies

$$ \begin{aligned} D^q\sum_r\binom{L+j}{r}\binom qr2^r&\leq(2D)^q\sum_r\binom{L+j}{r}\binom q{q-r}\cr&=(2D)^q\binom{p+j}{q}\cr&\leq(2D)^q\binom{2p}{q}.\end{aligned} $$

Summing over the $\binom mj$ active sets and $2^j$ active-sign assignments proves the first estimate. For the second, put $z=p/(2m)\leq1$. Then

$$ \sum_{j=0}^{p}2^j\binom mj\leq z^{-p}(1+2z)^m\leq\left(\frac{2em}{p}\right)^p,\qquad \binom{2p}{q}\leq\left(\frac{2ep}{q}\right)^q. $$

The first inequality holds because $z^j\geq z^p$ for $j\leq p$, and the second estimate in its chain uses $(1+p/m)^m\leq e^p$. Combining the bounds completes the proof. $\blacksquare$

## Theorem 2. A target-dependent exact pencil

Suppose all denominators lie in the span of two affine forms $B,C$, so $D_h=\alpha_h B+\beta_h C$. The basis forms and all coefficients may depend on the target. Only the actual denominators $D_h$ must be positive and admissible.

For $H\geq1$, absorb the bias into the first numerator. Clearing the positive product of denominators gives a sign-equivalent polynomial of the form

$$ P(x)=\sum_{k=0}^{H-1}L_k(x)B(x)^{H-1-k}C(x)^k, $$

where each $L_k$ is affine. Letting these affine forms vary independently enlarges the family. Its linear and nonlinear parameter counts are

$$ L=(n+1)H,\qquad q=2(n+1),\qquad p=(n+1)(H+2),\qquad D=\max\lbrace1,H-1\rbrace. $$

Thus, whenever $p\leq N$, its strict sign count is at most

$$ \left(\frac{2eN}{p}\right)^p\left(\frac{4eDp}{q}\right)^q. $$

This proves a restricted worst-case lower bound $\Omega(N/n)$. Indeed, take $H=\lfloor cN/n\rfloor$ for a sufficiently small absolute constant $c\gt0$. Then $p=(c+o(1))N$, the base-two logarithm of the first factor is $(c\log_2(2e/c)+o(1))N$, and the logarithm of the second is $O(n^2)=o(N)$. Choose $c$ so that $c\log_2(2e/c)\lt1$. For all sufficiently large $n$, the count is less than $2^N$.

An original weak false-label convention causes no problem: on the finite cube, subtract a sufficiently small positive bias to make every false score negative while retaining every true score positive. Bias absorption then gives exactly the displayed polynomial family.

## Theorem 3. Few exact pencil clusters

Partition the $H$ denominators into $G$ nonempty clusters, using one pair of affine basis forms per cluster. For any fixed ordered list of cluster sizes, parameterize the affine numerators and bias linearly, and the basis coefficients and the two coefficients of each denominator nonlinearly. The counts are

$$ L=(n+1)H+1,\qquad q=2(n+1)G+2H,\qquad p=L+q,\qquad D=2H. $$

The last degree follows because each denominator is bilinear in its cluster basis and its two scalar coefficients. The cleared score is affine-linear in all numerator coefficients and the bias. If $p\leq N$, its sign count is at most

$$ \left(\frac{2eN}{p}\right)^p\left(\frac{8eHp}{q}\right)^q. $$

Named-head assignments need not be counted: reorder heads so that clusters are consecutive. There are $\binom{H-1}{G-1}$ ordered positive lists of size $G$, and at most $2^{H-1}$ over every $G$. The bound can therefore be summed over size lists, adding at most $H$ bits to its logarithm when taking the largest displayed bound. It is monotone in the parameter counts over the stated regime.

Fix $0\lt\epsilon\leq1$ and require $G\leq H/n^\epsilon$. At widths $H=\Theta(N/n^x)$ with fixed $1\lt x\lt2$, the logarithmic count is

$$ O\bigl(nH\log n+n^{2-\epsilon}H\bigr). $$

For $\epsilon\lt1$, substituting $H=cN/n^{2-\epsilon}$ and taking a sufficiently small positive constant $c$ gives a count below $2^N$. At the endpoint $\epsilon=1$, use the exact estimate at $H=cN/n$: now $p=(c+o(1))N$, $q=O(cN/n)$, the first logarithmic contribution is $O(cN\log(1/c))$, and the second is $O(cN)$. The endpoint lower bound is again $\Omega(N/n)$.

These are lower bounds only for representations satisfying the stated exact cluster restriction.

## Paths and degenerations

If a path of parameters remains in one of these exact families and its strict sign table eventually stabilizes, choose one sufficiently small finite parameter value. The stabilized table is already among those counted above. Analytic coefficient germs at zero, or meromorphic germs after a common positive power of the path variable is cleared, suffice to justify stabilization when every repaired coordinate is nonzero. Analyticity merely on a punctured interval does not suffice.

There is no bounded-order Taylor truncation in this argument. Deep cancellation and different vanishing orders at different cube vertices do not enlarge the finite-parameter family.

First-order collinearity is insufficient. An expansion $D_h(t,x)=B(x)+t\lambda_h C(x)+O(t^2)$ permits new affine directions in the error terms. It does not imply exact pencil membership for positive $t$.

## Failure of an unrestricted bridge

For $n\geq2$, choose distinct positive numbers $t_h$ and define

$$ D_h(x)=1+t_hx_1+t_h^2x_2+\cdots+t_h^nx_n. $$

Every slope is strictly positive. The first three coefficients of any three denominators form a nonsingular Vandermonde matrix. Thus no exact pencil contains more than two of these displayed forms.

This does not rule out a different sign-equivalent representation with few clusters. It shows why the displayed model constraints do not themselves supply the cluster hypothesis. No such sign-preserving reduction is proved here.

## Independent audit record

The audit checked regular thresholds, coercivity on noncompact sign regions, generic distance centers, invertibility of the bordered KKT Jacobian, the two-block degree assignments, the coefficient extraction, the absence of a missing factor $2^m$, bias absorption, the head-reordering count, and both asymptotic endpoints. The proof survives these checks as a written mathematical proof using the two named general theorems.

The actual unrestricted head model has $L=(n+1)H+1$ numerator and bias parameters and $q=(n+1)H$ denominator parameters before normalization. Clearing uses degree $D=H$ in the latter. Theorem 1 therefore still pays $q\log H=\Theta(n^2H)$ at exponentially large width. Merely splitting linear and nonlinear parameters gives no fixed saving in the exponent of $n$.
