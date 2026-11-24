# Shared affine bases and finite observation fibers

## Status

This is a written finite capacity bound and a limitation of its polynomial enlargement. The weighted sign-count ingredient is kernel checked in `HeadComplexity.weightedStrictPolynomialSignPatterns_card_le`. The original-model bridge and the specialization below are written proofs. No unrestricted access theorem is asserted.

The comparison with `Research/StructuredDenominatorCapacity.lean` explains why this extension does not yet improve the unrestricted lower bound.

## The single-base class

Write $X=\lbrace0,1\rbrace^n$ and $N=2^n$. Fix a map $z:X\to\lbrace1,\ldots,K\rbrace$. Suppose an original score of width $H\geq1$ has denominators

$$ B_h(x)=T(x)+d_h(z(x)), $$

where $T$ is affine and every $B_h$ is strictly positive on the entire cube. The numerator $A_h$ is an arbitrary affine form. The numbers $d_h(z)$ may depend on the head and fiber, and may have either sign. This is an enlargement of the actual affine-denominator hypothesis whenever the displayed formula is realizable by original heads.

Absorb the bias into the first numerator by replacing $A_1$ with $A_1+bB_1$. This preserves affineness for actual original heads. For a fixed fiber $z$, put

$$ Q_z(t)=\prod_{h=1}^H(t+d_h(z)). $$

At every point of that fiber, $Q_z(T(x))$ is positive. Clearing it therefore preserves the strict truth table and gives

$$ P_z(x)=\sum_{i=0}^n x_i p_{zi}(T(x)),\qquad x_0=1,\qquad \deg p_{zi}\leq H-1. $$

Enlarge all coefficients of the polynomials $p_{zi}$ to arbitrary real numbers. Their dependence across fibers and heads is discarded only for an upper count. There are

$$ p=(n+1)(KH+1) $$

real parameters: $n+1$ coefficients of $T$ and $K(n+1)H$ polynomial coefficients. Give each coefficient of $T$ weight one and the coefficient of $t^j$ in $p_{zi}$ weight $H-j$, for $0\leq j\leq H-1$. Every Boolean score polynomial has weighted degree at most $H$. The product of all parameter weights is $(H!)^{K(n+1)}$.

If $p\leq N$, weighted Warren gives the finite bound

$$ |\mathcal F_{z,H}|\leq\frac{(4eHN/p)^p}{(H!)^{K(n+1)}}\leq(4e^2N/p)^p H^{n+1}. $$

For the second inequality, use $H!\geq(H/e)^H$, put $L=K(n+1)H$, and note $p-L=n+1$ and $e^L\leq e^p$. This bound permits arbitrary signed numerator cancellation and uses positivity only when clearing the original denominators.

## Counting the varying partition

Suppose $z$ records equality of a varying affine-observation map. Any number of observations has an equality partition of the form

$$ x\sim y\quad\Longleftrightarrow\quad (x-y)^\top G(x-y)=0 $$

for a positive semidefinite Gram matrix $G$. A small positive threshold separates the zero values from the finitely many nonzero values. Thus these partitions are among strict sign patterns of $N^2$ degree-one polynomials in $n^2+1$ variables. The kernel-checked declaration `AffineFiberCapacity.card_partitionPatterns_le` bounds their number by

$$ \left(\frac{4eN^2}{n^2+1}\right)^{n^2+1},\qquad n^2+1\leq N^2. $$

Choose one canonical labeling of the at most $K$ blocks in each partition. The arbitrary polynomial coefficients absorb any relabeling, so no extra factor $K!$ is needed. Consequently the variable-partition single-base class satisfies

$$ |\mathcal F_{K,H}|\leq\left(\frac{4eN^2}{n^2+1}\right)^{n^2+1}(4e^2N/p)^p H^{n+1},\qquad p=(n+1)(KH+1)\leq N. $$

Its logarithmic capacity is at most

$$ O\left(n^3+KnH\log\frac{eN}{KnH}+n\log H\right). $$

For example, there is an absolute $c\gt0$ such that $H\leq cN/(nK)$ makes the count at most $2^{N/2}$ for all sufficiently large $n$, provided the polynomial overhead $n^3$ and $n\log H$ is negligible compared with $N$. At the target width $H=cN/n^{3/2}$, this simple estimate is useful only for comparatively small $K$.

## The first loss at large fiber counts

The independent fiber-polynomial enlargement can already contain every truth table. Suppose every fiber has at most $H$ points. Choose an affine $T$ with distinct values on the whole cube, for example binary-weight slopes. For any labels $f:X\to\lbrace-1,1\rbrace$, interpolate their values separately on each fiber by a polynomial $p_{z0}$ of degree at most $H-1$. Set the other $p_{zi}$ equal to zero. Then

$$ P_z(x)=p_{z0}(T(x))=f(x) $$

at every Boolean point. Thus this enlarged class is exactly all truth tables whenever the fibers have size at most $H$. This is a limitation of the proposed count, not a construction of those truth tables by the original heads.

In particular, the affine-fiber theorem can remain useful when the complete denominator-observation map has exponentially many values $K$ and all scores are affine inside each fiber. Adding a varying common affine base and then independently interpolating degree $H-1$ within each fiber loses that advantage. For balanced fibers, the enlargement becomes universal once $H\geq N/K$.

## Relation to the existing affine-plane count

If the differences $B_h-T$ depend on $r$ designated Boolean coordinates, the normalized denominator coefficient vectors lie in a varying affine plane of dimension at most $r+1$. More generally, if their joint affine-observation map has $K$ distinct values on the cube and slope rank $r$, then

$$ 2^r\leq K. $$

To see this, choose $r$ linearly independent columns of the observation matrix. Their $2^r$ subset sums are distinct; fixing all other coordinates gives that many different observation values. The difference slope vectors lie in an $r$-dimensional linear subspace. Adjoining the common base slope vector increases its dimension by at most one, and normalizing each positive denominator by its intercept preserves containment in that linear subspace. Hence all normalized denominator vectors lie in an affine plane of dimension at most $r+1$.

The existing `StructuredDenominatorCapacity.card_clustered_le` therefore already counts this family with one plane of dimension at most $1+\log_2 K$. In the range of small $K$ where the independent fiber-polynomial count is useful, that plane count generally uses fewer nonlinear parameters. Neither argument proves that an arbitrary original representation admits a common affine base with sufficiently few difference observations.

The missing statement is an access theorem preserving the whole truth table, or a joint count retaining the dependence of the fiber polynomials on their common original numerators and shifts. Independent polynomial interpolation on every fiber does not supply it.
