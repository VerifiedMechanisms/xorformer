# Staircase chart enumeration and the degree cost of shape coordinates

## Scope

This note records one cheap combinatorial ingredient for a possible collision-stratification argument, and an exact limitation of a natural interpolation chart. Neither result bounds the Boolean sign capacity of unrestricted affine-ratio sums. In particular, counting charts is not a substitute for controlling the parameters and equations inside each chart.

## The number of monomial staircases

A monomial staircase in $d\geq1$ variables is a finite nonempty subset $\Lambda\subset\mathbb N^d$ closed under coordinatewise decrease. Its size is the number of standard monomials in the corresponding quotient basis.

**Theorem.** For every $d,H\geq1$, the number of monomial staircases of size exactly $H$ is at most

$$ (4d)^{H-1}. $$

Consequently the logarithm of this number is $O(H\log(d+1))$.

**Proof.** The zero vector belongs to every staircase. For a nonzero $\alpha\in\Lambda$, choose its parent by subtracting one from the largest-index coordinate in which $\alpha$ is nonzero. The parent belongs to $\Lambda$, and total degree decreases by one. These parent edges therefore form a rooted tree on the $H$ elements of $\Lambda$.

Label the edge from a parent to its child by the coordinate that was increased. Order the children at each vertex by this coordinate label. This produces a plane rooted tree whose $H-1$ edges carry labels from $\lbrace1,\ldots,d\rbrace$.

The encoding is injective. Given the labelled plane tree, assign the root the zero vector and assign any other vertex the sum of the coordinate unit vectors along its root path. This recovers all elements of $\Lambda$. Some labelled trees decode to repeated vectors or fail downward closure, but this only enlarges the counting family.

There are at most $4^{H-1}$ plane rooted trees with $H$ vertices: their depth-first traversals are encoded by binary strings of length $2(H-1)$, recording each descent and ascent. There are at most $d^{H-1}$ edge labellings. Multiplying gives the claimed bound. $\blacksquare$

The same argument bounds the number of staircases of size at most $H$ by $(4d)^H$. Thus choosing a standard-monomial diagram does not by itself force a term of order $dH\log H$ in a sign count.

## A shape chart for distinct point configurations

Let $v_1,\ldots,v_H$ be distinct points of $\mathbb R^d$. Choose a real linear form separating these points, which is possible by avoiding finitely many proper hyperplanes in the dual space. After an invertible linear coordinate change, write the distinct first coordinates as $t_1,\ldots,t_H$.

Define

$$ f(t)=\prod_{h=1}^H(t-t_h)=t^H+\sum_{j=0}^{H-1}f_jt^j. $$

For each of the remaining $d-1$ coordinates there is a unique interpolation polynomial $g_i$ of degree less than $H$ such that $g_i(t_h)$ is that coordinate of $v_h$. Thus the unordered configuration is described, on this chart, by the $dH$ coefficients of $f,g_1,\ldots,g_{d-1}$, together with the requirement that $f$ have distinct real roots.

This is an actual parameter count, not a claim that all collision limits have a nonsingular chart of this form. A separate coordinate change can be chosen for each finite configuration. In capacity applications its parameters would also have to be included or otherwise controlled.

## Natural positive weights retain the large degree factor

Assume $d\geq2$ for this degree calculation. Assign the auxiliary variable $t$ weight one. Give the coefficients of $f$ the standard weights

$$ w(f_j)=H-j. $$

To make each interpolation polynomial $g_i(t)=\sum_{j=0}^{H-1}g_{ij}t^j$ weighted homogeneous of a common integer degree $G$, the coefficient weights must be

$$ w(g_{ij})=G-j. $$

All these weights are strictly positive only if $G\geq H$.

For a monic $f$, the resultant satisfies

$$ {\rm Res}_t(f,g_i)=\prod_{h=1}^H g_i(t_h). $$

It has weighted degree $HG$ under the displayed weights. For example, the monomial $g_{i0}^H$ occurs with coefficient one and already has that weight. More generally, clearing evaluations of an affine combination of the $g_i$ produces the same degree scale. The occurrence of a high-degree resultant is therefore real in this particular chart, even though the original coordinates were affine functions on the Boolean input.

Put $p=dH$. The product of the coefficient weights is

$$ \prod w=H!\left(\frac{G!}{(G-H)!}\right)^{d-1}. $$

The degree-over-weight factor entering the weighted sign-count estimate has the lower bound

$$ \frac{(HG)^{dH}}{H!\left(G!/(G-H)!\right)^{d-1}}\geq\frac{(HG)^{dH}}{H^H G^{(d-1)H}}=H^{(d-1)H}G^H\geq H^{dH}. $$

Thus this natural positive-weight chart still pays a factor at least $H^p$. The factorial coefficient weights do not remove the $p\log H$ term. This is an obstruction to this specific degree calculation, not a theorem that every coordinate system or every sign-count argument must pay that term.

## Why rescaling the interpolation parameter is not a collision reduction

Replacing $t_h$ by $\varepsilon t_h$ while preserving the original points requires replacing $g_i(t)$ by $g_i(t/\varepsilon)$. Its coefficient of $t^j$ becomes $\varepsilon^{-j}g_{ij}$.

These are negative powers for every nonzero higher coefficient. Thus a finite configuration can be made to have coalescing parameter values only at the cost of unbounded curve coefficients. It does not become a fixed bounded radial or curvilinear collision configuration to which the earlier transfer and weighted-jet theorems automatically apply.

## The remaining geometric issue

The inexpensive staircase count leaves a concrete question: can the smoothable configuration space of length $H$ be covered by charts whose nonlinear parameters, with appropriate positive weights, have total complexity $O(dH)$ and whose cleared evaluation predicates have a sufficiently small weighted degree?

Naive border-basis or multiplication-matrix coordinates introduce up to $dH^2$ entries. Their commutativity and quotient-algebra relations remove many degrees of freedom, but no sign-count theorem was established here that uses those relations without reintroducing a large degree factor. The shape chart above has the correct parameter dimension and the wrong degree scale. No bridge from unrestricted original head representations to the restricted low-cost collision charts has been proved.

## Verification status

The tree encoding, interpolation argument, and weighted-degree inequalities are written elementary proofs. No Lean formalization or finite computation is claimed for this note. They are auxiliary results and do not prove the requested improvement for the original worst-case head complexity.
