# Weighted incidence capacity from finite polar witnesses

## Status and statement

This is a written proof, not a Lean theorem. Its regular polynomial root-counting ingredient is kernel checked as `HeadComplexity.PolynomialRootCount.weighted_regular_roots_card_le` in `Polynomial/WeightedRootWrappers.lean`. The local algebraic geometry, parameter transversality, and constrained optimization arguments below have not been formalized.

Let $u\in\mathbb R^b$ and $y\in\mathbb R^q$. Give the $u$ coordinates weight one and the $y$ coordinates an integer weight $M\geq1$. Put $K=b+q$. Suppose $V$ is the common real zero locus of finitely many real polynomials of weighted degree at most $L$, where $L\geq M$. Let $E\subseteq V$ be any subset such that the complex algebraic fiber obtained by fixing $u$ has local complex dimension at most $r$ at each point of $E$, where $0\leq r\lt q$. Write

$$ c=q-r,\qquad d=b+r=K-c. $$

Let $P_1,\ldots,P_N$ be polynomials of weighted degree at most $D$, with $D\geq2L$. Then the number $T$ of strict sign patterns realized on $E$ satisfies

$$ T\leq 6^K\frac{(2L)^cD^d}{M^q}\sum_{j=0}^d\binom{2N+1}{j}. $$

The binomial coefficient is zero when its lower argument exceeds $2N+1$. The defining polynomials may be singular or redundant. The hypothesis concerns the local dimension of the common zero locus in a fixed fiber, rather than the rank of their Jacobian. No margin bound is assumed.

For the incidence equations in `cayley_bacharach_base_locus.md`, the natural budgets are $b=nM$, $q=n(H-M)$, $r=r_\ast(H-M)$, and $L=2sM$. An invertible determining minor is required at the selected representatives, but no conditions are imposed on the rank-drop locus away from them. The factor in the theorem is then of the form

$$ O(1)^K M^b s^c (D/M)^d\sum_{j=0}^d\binom{2N+1}{j}. $$

This supplies a proposed effective version of the reduced-support configuration count. It does not supply an ordinary-moment lift for original xorformer representations, and it does not silently include arbitrary affine numerator parameters.

## Finite representatives and a common projection

There are finitely many strict sign patterns. Select one representative $z_a=(u_a,y_a)\in E$ of each. It is enough to construct a single smooth algebraic set of dimension $d$, of controlled weighted degrees, which still realizes all these patterns.

Choose one linear change of the $y$ coordinates such that projection onto their last $r$ coordinates locally isolates every $y_a$ in its fiber at fixed $u_a$. Such a choice exists simultaneously for the finitely many representatives. Indeed the projectivized tangent cone of a complex algebraic germ of dimension at most $r$ has dimension at most $r-1$. A generic codimension $r$ linear kernel avoids this projective cone. Its intersection with the germ is therefore isolated at the given point. Each point excludes a proper algebraic subset of possible linear projections; a finite intersection of their open complements is nonempty and has real points. In the case $r=0$, the fiber point is already isolated.

This change of coordinates mixes only variables of equal weight, so preserves all weighted-degree bounds. Write $y'=(y_1,\ldots,y_c)$ for the remaining fiber coordinates, which will vary while $u$ and the last $r$ coordinates are held fixed.

Let the original defining polynomials be $F_\alpha$, and set

$$ Q=\sum_\alpha F_\alpha^2. $$

Its weighted degree is at most $2L$. In the fixed affine fiber through $z_a$, choose a small closed Euclidean ball centered at $z_a$ in the $y'$ coordinates. It contains no other zero of $Q$, and all $P_i$ retain their strict signs throughout that ball. The boundary minimum of $Q$ is positive.

These are local compact balls, one for each selected representative. No global boundedness or compactness of $V$ is asserted.

## One common smooth polar perturbation

Choose an open neighborhood $\mathcal U$ of the constant polynomial one in the finite-dimensional real space of polynomials of weighted degree at most $2L$, small enough that every $H\in\mathcal U$ lies between $1/2$ and $2$ on all the chosen fiber balls. Choose one $t\gt0$ small enough that

$$ Q-tH\gt0 $$

on every ball boundary, for every $H\in\mathcal U$. At each center $Q-tH\lt0$. Both choices can be made uniformly because only finitely many compact balls occur.

Write $G=Q-tH$. For each $H$, take the connected component containing the center of the closed sublevel set inside the chosen fiber ball. It is nonempty and compact. Since $G\gt0$ on the boundary, this component lies strictly inside the ball and is also a component of the unrestricted sublevel set in that fixed fiber. Maximize $y_c$ on this component. At a maximizer $z$, one has

$$ G(z)=0,\qquad \partial_{y_1}G(z)=\cdots=\partial_{y_{c-1}}G(z)=0. $$

For the derivative assertion, if one of these derivatives were nonzero, the implicit function theorem would permit increasing $y_c$ while remaining in $\lbrace G\leq0\rbrace$ near $z$, a contradiction. The same local argument gives $G(z)=0$. Thus every original strict sign pattern occurs on the polar zero set

$$ W_H=\lbrace G=\partial_{y_1}G=\cdots=\partial_{y_{c-1}}G=0\rbrace. $$

Every displayed polynomial has weighted degree at most $2L$.

There is a choice $H\in\mathcal U$ for which $W_H$ is a smooth complete intersection of codimension $c$ in real affine space, or empty. Only real smoothness is needed; no complex or projective smoothness is asserted. To verify the required transversality, consider the map sending $(H,z)$ to the $c$ displayed polynomial values. Variations of the constant coefficient and the coefficients of $y_1,\ldots,y_{c-1}$ give a surjective derivative in the $H$ variables at every $z$. These monomials are available because $2L\geq M$. The universal map is a submersion, so parameter transversality, equivalently Sard's theorem applied to its zero set and the parameter projection, gives a dense set of suitable $H$. Choose one inside $\mathcal U$.

The set is nonempty when any pattern was selected. This constructs one common smooth $W=W_H$ realizing all patterns. It uses no full coordinate change mixing the two weight blocks and no global stratification of the exceptional determining tuples.

## Counting regular constrained critical points

We first give the weighted degree calculation for a fixed active set. Let $g_1,\ldots,g_c$ be the polar equations, of weighted degree at most $A=2L$. Add $j\leq d$ active equations of weighted degree at most $D$. Assume their joint gradients are independent and all critical points being counted are regular solutions of the corresponding Lagrange system for a generic squared-distance objective.

Assign multiplier weight $2D-A$ to the first $c$ equations, and weight $D$ to each of the $j$ active equations. These are positive, and the former are at least $D$, since $D\geq A$. All stationarity equations have weighted degree at most $2D-w_i$, where $w_i$ is the weight of the original coordinate being differentiated. The squared-distance objective has weighted degree at most $2M\leq2D$.

Match the $c$ low-degree equations to any $c$ heavy coordinates. Match the $j$ active equations to any $j$ of the remaining original coordinates. Match $c+j$ stationarity equations to the multiplier coordinates, and match the remaining stationarity equations to the remaining original coordinates. The regular root bound allows this permutation of the equations: output permutation preserves invertibility of the Jacobian.

For the low equations, diagonal exponents can be taken to be $\lfloor A/M\rfloor+1\leq2A/M$. For every other original coordinate of weight $w_i$, an exponent at most $3D/w_i$ suffices. For each multiplier coordinate, exponent two suffices because its weight is at least $D$ and every stationarity equation has weighted degree strictly less than $2D$.

Consequently the number of regular Lagrange roots is at most

$$ 2^{c+j}\left(\frac{2A}{M}\right)^c\prod_{i\text{ not matched to a low equation}}\frac{3D}{w_i}\leq6^K\frac{A^cD^d}{M^q}. $$

Here the product contains exactly $d$ original coordinates, the omitted $c$ coordinates all had weight $M$, and $2^{2c+j}3^d\leq4^c6^d\leq6^K$. This is a direct application of the existing weighted regular-root theorem, rather than an unproved weighted projective Bezout formula.

## From patterns to the critical systems

Choose a large Euclidean ball containing all the constructed witnesses in its interior. Choose two small thresholds for each $P_i$, one positive and one negative, so that the witnesses lie strictly beyond their corresponding thresholds. Choose these thresholds, and the squared radius of the large ball, generically. Sard's theorem on the smooth manifold $W$ implies that every intersection with any subset of the resulting $2N+1$ level hypersurfaces is transverse, and no more than $d$ of them meet at a point of $W$.

For each selected sign pattern, intersect $W$ and the large closed ball with the corresponding closed threshold inequalities. This is a nonempty compact set. Minimize squared distance to one generic center $a$ on each of these sets. At each minimizer, the polar gradients and the active level gradients are independent, so the usual Lagrange multiplier equations hold. There are at most $d$ active level equations.

One center $a$ can be chosen such that all the resulting Lagrange roots are regular, simultaneously for every active subset. For completeness, on the smooth intersection defined by a fixed active subset, its normal bundle has the same dimension as the ambient space. The map sending a normal vector to its endpoint is smooth. Sard's theorem gives regular values of this map, and a regular endpoint is exactly an invertible Jacobian of the Lagrange system. There are finitely many active subsets, so their full-measure sets of regular centers have a common point.

A point satisfying the strict threshold gaps determines its entire sign pattern. For each active subset, different selected patterns therefore give different Lagrange roots. Sum the preceding regular-root bound over the at most $\sum_{j=0}^d\binom{2N+1}{j}$ active subsets. This proves the stated inequality.

## Scope and external comparison

[Barone and Basu's degree-sensitive sign-condition theorem](https://www.math.purdue.edu/~sbasu/refined_bounds-04-11-11.pdf) treats arbitrary real algebraic varieties by smooth polar approximation and then complex projective Betti estimates. Its published theorem uses ordinary total degrees. The argument here keeps only finitely many strict-sign representatives and uses local fiber balls, a common weighted polynomial perturbation, and weighted regular Lagrange roots. These modifications are the substantive points that must be independently checked before relying on this written theorem.

The argument does not identify all original low-margin truth tables with ordinary Cayley–Bacharach supports. It also does not give a finite-scheme version of the determining-subset construction. These remain distinct access problems even if the weighted incidence theorem is accepted.
