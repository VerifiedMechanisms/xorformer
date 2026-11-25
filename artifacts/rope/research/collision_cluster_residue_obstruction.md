# A Highest-Pole Obstruction for Denominator Collision Clusters

This note studies a route toward improving the vanilla lower bound for the separated pure three-head family. It proves a necessary condition on limits of full cleared affine-fraction polynomials, allowing arbitrarily divergent numerators and arbitrarily many collision scales. It does not prove a four-head or five-head Boolean lower bound. The precise distinction from the coefficient limits supplied by Boolean averaging is stated at the end.

## The setting

For affine denominators positive on the centered cube, divide each denominator and its numerator by the denominator's value at the cube center. The normalized constant term is one, and the sum of the absolute slope coefficients is strictly less than one. Thus the denominator coefficients lie in a compact closure, and every limit retains constant term one. In particular zero limiting forms are excluded, including when the limiting affine denominator is constant.

Work with homogeneous real polynomials in finitely many variables. Let

$$ R_k=\sum_{i=1}^{K}\frac{A_{i,k}}{L_{i,k}},\qquad Q_k=\sum_{i=1}^{K}A_{i,k}\prod_{j\neq i}L_{j,k}. $$

Every numerator and denominator is a linear form. Suppose each denominator converges in coefficients to a nonzero linear form, and the entire cleared polynomial $Q_k$ converges in coefficients to $Q$. No bound is assumed on any numerator coefficients.

Partition the denominator limits into proportionality classes. Rescaling the forms by convergent nonzero constants, write the distinct limits as $F_1,\ldots,F_s$, with multiplicities $m_1,\ldots,m_s$. Then

$$ R_k\longrightarrow R=\frac{Q}{\prod_{a=1}^{s}F_a^{m_a}} $$

uniformly on every compact complex set avoiding the limiting denominator hyperplanes. This follows directly from coefficient convergence and a positive lower bound for the denominator product on that compact set.

## The highest-pole coefficient splits completely

Fix one cluster, of size $m$, whose limit is $F$. Use a projective affine chart meeting a generic point of $F=0$ where the other limiting denominators are nonzero. Take a coordinate $\xi=F$ in this chart and transverse coordinates $z$.

After dividing each denominator in this cluster by its nonzero coefficient of $\xi$, its root is an affine polynomial $\alpha_{i,k}(z)$ tending to zero in coefficients. Division of its affine numerator by the denominator gives a constant plus

$$ \frac{a_{i,k}(z)}{\xi-\alpha_{i,k}(z)}, $$

where $a_{i,k}$ is affine in $z$. The residues may diverge.

Choose a small circle in the complex $\xi$ plane around zero and a small real box of transverse coordinates. For sufficiently large $k$, the circle encloses precisely this cluster's poles and avoids all other denominator zeros. Uniform convergence of the full rational functions on this circle gives convergence of the contour moments

$$ M_{j,k}(z)=\sum_{i=1}^{m}a_{i,k}(z)\alpha_{i,k}(z)^j,\qquad 0\leq j\leq m-1. $$

Each moment is a polynomial of degree at most $j+1$ in $z$. Pointwise convergence on a fixed finite interpolation grid in the box therefore implies convergence of its coefficient vector. Its limit is the coefficient of $\xi^{-j-1}$ in the Laurent expansion of $R$ at $F=0$.

Fix an index $t$ in the cluster. The following identity is exact, even when roots coincide:

$$ \sum_{i=1}^{m}a_{i,k}\prod_{j\neq t}(\alpha_{i,k}-\alpha_{j,k})=a_{t,k}\prod_{j\neq t}(\alpha_{t,k}-\alpha_{j,k}). $$

Expand the polynomial $\prod_{j\neq t}(X-\alpha_{j,k})$. The left side is $M_{m-1,k}$ plus lower moments multiplied by polynomial coefficients tending to zero. Those lower moments are coefficient-bounded, so

$$ \lim_{k\to\infty}M_{m-1,k}=\lim_{k\to\infty}a_{t,k}\prod_{j\neq t}(\alpha_{t,k}-\alpha_{j,k}). $$

Every polynomial on the right is a product of $m$ affine forms. Such products form a closed subset of the finite-dimensional polynomial coefficient space. To see this, normalize each nonzero factor to coefficient norm one. On the product of the unit spheres, the coefficient norm of the product has a strictly positive minimum: it is continuous, and a product of nonzero real polynomials cannot vanish. A convergent product sequence therefore has bounded products of factor norms. Taking a subsequence gives a limiting scalar and limiting normalized affine factors. Zero products are covered separately.

**Highest-pole lemma.** The coefficient of the highest possible pole $F^{-m}$ in the limiting rational function is either zero or a product of at most $m$ affine forms on the hyperplane $F=0$. This conclusion permits arbitrary divergent residues and arbitrary relative rates of denominator collision.

The proof does not assume a single perturbation parameter, a Laurent expansion of the numerator parameters, or bounded first-order perturbation directions.

## Consequences for a source with nonlinear hyperplane sections

Suppose $Q=P G\neq0$, where $P$ is a fixed homogeneous polynomial. Assume that for each limiting denominator $F_a$, the nonzero image of $P$ modulo $F_a$ has an irreducible factor of degree at least two.

The highest-pole lemma forces

$$ F_a\mid G\qquad(1\leq a\leq s). $$

Indeed, if $G$ did not vanish modulo $F_a$, the highest-pole coefficient would equal the nonzero rational function

$$ \frac{\overline P\overline G}{\prod_{b\neq a}\overline {F_b}^{m_b}}. $$

Equating this with a product of affine forms and clearing the displayed denominator contradicts unique factorization: the left numerator has a nonlinear irreducible factor, while every factor on the right has degree one. The same conclusion follows if the highest-pole coefficient is zero, because the quotient polynomial ring is an integral domain.

Since the distinct forms $F_a$ are pairwise nonproportional, their product divides $G$. Thus $s\leq\deg G$.

There is a stronger conclusion for clusters of size two. Once the double-pole coefficient vanishes, the remaining simple-pole coefficient is the limit of $M_{0,k}=\sum_i a_{i,k}$, hence is affine. Applying the same irreducible-factor argument again gives $F_a^2\mid G$. A simple cluster similarly forces its whole factor into $G$.

For the homogeneous source cubic in the [finite-factor obstruction](exact_finite_factor_obstruction.md), every nonzero oriented denominator section has the required nonlinear irreducible factor. The proof there also applies to nonzero weakly oriented limits: a nonnegative slope row with zero coordinate sum is zero, so a nonzero such form cannot belong to the span of the source denominator rows. Nonzero constant affine denominators are included by homogenization and by choosing a different projective chart in the argument above.

Consequently a full coefficient limit $Q=P G$ of four-head cleared polynomials must have all four denominator limits proportional. Here $\deg G=1$, so there can be at most one cluster.

For five heads, there are at most two clusters. A partition into sizes three and two is impossible: the size-two cluster forces a square factor into the degree-two multiplier, while the other cluster forces another distinct factor. The only possible partitions are a single size-five cluster or sizes four and one. In the latter case, the multiplier is proportional to the product of the two limiting denominator forms; the limiting rational function has only the triple pole associated with the size-four cluster.

## A concrete multiscale obstruction to a naive moment lemma

Bounded zeroth and first moments alone do not force the limiting cubic second moment of a four-pole cluster to depend on at most three linear coordinates. Let $x,y,A,D$ be independent coordinates, let $t\to0$ through nonzero real numbers, and take the four roots

$$ \alpha_0=0,\qquad \alpha_1=tx,\qquad \alpha_2=2tx+t^2y,\qquad \alpha_3=3tx+3t^2y. $$

Give the last three roots the affine residues

$$ a_1=t^{-3}(3A-2tD),\qquad a_2=t^{-3}(-3A+tD),\qquad a_3=t^{-3}A, $$

and set $a_0=-a_1-a_2-a_3$. Direct expansion gives

$$ M_0=0,\qquad M_1=Dy,\qquad M_2=6Axy+2Dx^2+6tAy^2+4tDxy+t^2Dy^2. $$

Thus $M_2\to6Axy+2Dx^2$. This cubic depends essentially on all four coordinates. Indeed, its directional derivative in a constant direction $(e_x,e_y,e_A,e_D)$ is

$$ 6e_xAy+6e_yAx+6e_Axy+4e_xDx+2e_Dx^2. $$

The distinct monomial coefficients force every component of a direction annihilating this polynomial to vanish.

The same example has

$$ M_3\to6Ax^3\neq0. $$

It therefore has a nonzero fourth-order pole. This is a counterexample only to the proposed inference from bounded $M_0,M_1$ to a bound on the essential number of variables of $M_2$. For the four-head source limit $Q=P F$, the rational limit is $P/F^3$, so its third moment must tend to zero. The example does not satisfy that extra hypothesis and does not settle the remaining four-head collision case. A five-head single-cluster limit can still have a fourth-order pole when its degree-two multiplier is divisible by $F$ but not by $F^2$.

## A limited vanishing-higher-pole result

There is a stronger conclusion for a restricted class of four-pole collisions. Set $\alpha_0=0$ and suppose

$$ \alpha_i(t)=t\ell_i+O(t^2)\qquad(1\leq i\leq3), $$

coefficientwise, where $\ell_1,\ell_2,\ell_3$ are nonzero, pairwise distinct homogeneous linear forms on a finite-dimensional real vector space. Suppose each residue has a finite Laurent expansion in integer powers of $t$, with homogeneous linear coefficients. If $M_1,M_2$ have bounded coefficient vectors and $M_3\to0$, then the residues at the three nonzero poles have no pole of order greater than two. Consequently the limiting cubic $M_2$ depends on at most three linear coordinates.

**Proof.** If $p\geq3$ were the largest residue pole order, let $A_i$ be its coefficient at the $i$-th nonzero pole, with at least one $A_i\neq0$. The leading coefficient of $M_j$ is $S_j=\sum_i\ell_i^j A_i$ at power $t^{j-p}$. Boundedness for $j=1,2$ and convergence to zero for $j=3$ force $S_1=S_2=S_3=0$. The exact polynomial identity

$$ S_3-(\ell_2+\ell_3)S_2+\ell_2\ell_3S_1=\ell_1(\ell_1-\ell_2)(\ell_1-\ell_3)A_1 $$

then implies $A_1=0$, since the three displayed linear factors are nonzero and the polynomial ring is an integral domain. Permuting indices gives $A_2=A_3=0$, a contradiction. Thus every residue is $O(t^{-2})$.

Write $B_i$ for its coefficient at $t^{-2}$. The coefficient at $t^{-1}$ in $M_1$ vanishes, while the constant coefficient in $M_2$ gives its limit. Therefore

$$ \sum_{i=1}^{3}B_i\ell_i=0,\qquad C=\lim_{t\to0}M_2=\sum_{i=1}^{3}B_i\ell_i^2. $$

Consider the linear map $v\mapsto(B_i(v)+\ell_i(v))_{i=1}^{3}$. If $v$ is in its kernel, evaluating the first identity at $v$ gives

$$ 0=\sum_{i=1}^{3}B_i(v)\ell_i(v)=-\sum_{i=1}^{3}\ell_i(v)^2. $$

Thus every $\ell_i(v)$ and every $B_i(v)$ is zero. Translating by any such $v$ leaves $C$ unchanged. The cubic therefore factors through the quotient by this kernel, whose dimension is at most three. This is the same sum-of-squares mechanism as the [regular common-base moment obstruction](common_base_jet_obstruction.md). $\blacksquare$

If all leading forms are multiples of one form, say $\ell_i=c_i x$ with distinct nonzero scalars $c_i$, the proof gives the stronger conclusion $C=x^2L$ for a linear form $L$. This case has at most two essential linear coordinates.

The hypotheses matter. Repeated or zero first-order leading forms, roots with leading order greater than one, fractional relative scales, and paths without finite Laurent expansions are not covered. In particular, reparameterizing a path can change the first-order-root hypothesis; the statement is not a classification of all collisions.

The accompanying [exact Laurent search](../search/check_four_cluster_laurent.py) checks eleven specified root paths in four variables and residue poles through order twelve. It solves the moment constraints over the rationals and checks the generic derivative rank of each resulting cubic space. This is a reproducible finite search, not a universal collision theorem or a Boolean lower bound.

## Exact scope and the remaining gaps

The [Lean algebraic identities](../../../formalization/HeadComplexity/Polynomial/RoPEClusterMoments.lean) prove the residue-annihilator identity for an arbitrary finite set over any commutative ring, the exact first, second, and third moment expansions for the multiscale example, and the Vandermonde residue elimination. The contour-limit, product-closure, and Laurent-order arguments above are rigorous mathematical proofs but are not claimed as additional Lean limit theorems.

These collision conclusions require convergence of every coefficient of the full cleared polynomial. The arbitrary-head Boolean separation proof supplies convergence only of the selected top squarefree coefficients of an oriented factor polynomial. Replica averaging produces a convergent full polynomial but generally destroys its affine-fraction factorization. The present lemma therefore cannot be applied directly to those averaged limits.

Even under full coefficient convergence, the surviving single-cluster cases allow higher-order numerator divergence and several perturbation scales. The [common-base jet obstruction](common_base_jet_obstruction.md) treats a regular second-order moment model and does not close these remaining cases. No sharper finite Boolean minimum than four through six is asserted for the separated three-head family.
