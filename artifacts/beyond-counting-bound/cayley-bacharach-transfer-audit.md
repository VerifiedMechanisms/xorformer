# Boolean Moments Do Not Give Cayley–Bacharach Conditions

## The proposed mechanism and its hypothesis

High contact at a denominator collision gives a signed relation among the functions of a velocity vector $v$ of the form $(v\cdot x)^j$, with $x\in\lbrace0,1\rbrace^n$. A possible structural route would replace this restricted moment condition by the Cayley–Bacharach condition for all polynomials of degree at most $k$, and then constrain the velocity support geometrically.

That replacement is false even for support-minimal, nonpersistent collisions with strictly positive slopes. The obstruction below is a consequence of the existing elliptic circuits, with explicit polynomial separators. It blocks this transfer, not every possible use of algebraic geometry.

For a finite affine set $Z$, the Cayley–Bacharach condition in degree $k$ means that every polynomial of total degree at most $k$ vanishing on all but one point of $Z$ also vanishes on the last point. This is equivalent to the homogeneous projective formulation after homogenizing in a coordinate that is one on $Z$.

## Complete separation despite Boolean moment cancellation

**Theorem 1.** For every $k\geq3$, there are

$$ H=2k+2-\lfloor k/3\rfloor $$

distinct positive rational vectors $v_1,\ldots,v_H\in\mathbb R^2$ and nonzero integer coefficients $c_1,\ldots,c_H$ with the following properties.

1. For every Boolean $x$ and every $0\leq j\leq k$, one has $\sum_h c_h(v_h\cdot x)^j=0$. The restricted moment matrix has rank $H-1$, and every proper subset of its columns is independent.

2. The evaluation map from all polynomials of total degree at most $k$ to $\mathbb R^H$ is surjective. In particular, every individual support point has a polynomial separator of degree at most $k$.

3. The reciprocal family

$$ F_\varepsilon(x)=\sum_{h=1}^H\frac{c_h}{1+x_1+x_2+\varepsilon v_h\cdot x} $$

has strictly positive denominator slopes for $\varepsilon\geq0$, exact contact order $k+1$, and no persistent linear identity among its terms.

**Proof.** Take the rational points and residues from [the elliptic circuit theorem](ellipse-moment-circuits.md). They lie on the translated nondegenerate ellipse

$$ (u-2)^2+(u-2)(v-2)+(v-2)^2=1. $$

That theorem proves the first and third assertions, including distinct projections in each nonzero Boolean direction. It remains to prove surjectivity for the complete polynomial system.

Since $\lfloor k/3\rfloor\geq1$, one has $H\leq2k+1$. Fix one point $p\in Z$. Pair the other $H-1$ points. If one point remains unpaired, choose any rational line through it that avoids $p$. For each pair, take the line through the paired points. None of these lines passes through $p$: a line meets a nondegenerate ellipse in at most two points. The product of their affine equations has degree

$$ \left\lceil\frac{H-1}{2}\right\rceil\leq k, $$

vanishes at every point of $Z\setminus\lbrace p\rbrace$, and does not vanish at $p$. Dividing by its nonzero value at $p$ gives a polynomial whose evaluation vector is the coordinate vector at $p$. Doing this for every $p$ proves surjectivity. All coefficients are rational. $\blacksquare$

The theorem gives a maximal failure of the suggested transfer: the restricted system has a full-support circuit while the complete degree $k$ system has no relation at all. Removing persistent Boolean identities does not repair it, because the displayed family has none.

## An exact seven-point replay

For $k=3$, use the seven rational points and integer residues already listed in the elliptic circuit certificate. For each target point, pair the other six in increasing index order and multiply the three resulting line equations. The companion verifier evaluates the seven normalized cubic separators at all seven points and obtains the identity matrix. It also rechecks all sixteen restricted Boolean moment equations through degree three and computes a nonzero formal mixed moment.

These are exact rational computations. The general theorem above is a written proof; no new Lean theorem is claimed. The previously checked elliptic circuit declarations are unchanged.

## Literature audit and remaining gap

[Picoco, Theorem A](https://arxiv.org/html/2201.01665v2), requires the complete degree $k$ Cayley–Bacharach condition and proves a low-degree curve conclusion in its stated cardinality range for $3\leq h\leq5$. [Linh and Long, Theorem 1.4](https://arxiv.org/html/2511.22113v1), prove the plane-configuration conjecture for configuration dimension four, again assuming the complete Cayley–Bacharach condition. Neither hypothesis follows from the Boolean moment equations.

A different structural theorem for the restricted Boolean moment system would be needed. In addition, a collision theorem alone would still need a sign-preserving transfer from arbitrary finite, target-dependent denominators. Neither step is proved. This audit yields no improvement to the unrestricted lower bound on $W(n)$ and makes no change to the model.
