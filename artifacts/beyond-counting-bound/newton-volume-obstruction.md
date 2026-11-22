# A Large Newton Polytope Survives Normalization

## Statement

Let $n,H\geq1$ and put $p=nH$. Consider the manuscript's cleared parameter polynomial at the all-one input:

$$ P(b,u)=\sigma\prod_{h=1}^H\left(1+\sum_{i=1}^n b_{hi}\right)+\sum_{h=1}^H\left(\sum_{i=1}^n u_{hi}\right)\prod_{g\neq h}\left(1+\sum_{i=1}^n b_{gi}\right),\qquad \sigma\in\lbrace-1,1\rbrace. $$

Its Newton polytope has dimension $2p$. If $V(P)$ denotes its normalized volume, with the unit coordinate simplex assigned volume one, then

$$ V(P)\geq\frac{(2p)!}{2^{2p}(n!)^H p!}\geq\left(\frac H4\right)^p. $$

In particular, its logarithmic normalized volume retains a term of order $nH\log H$ when $H$ is large. A bound that treats this common Newton polytope only through its volume does not obtain a small-volume saving that removes this term.

## Proof

For each head, let $\Delta_n$ be the coordinate simplex in its $n$ denominator variables. The denominator-only monomials of $P$ are exactly the vertices of the product

$$ B=\prod_{h=1}^H\Delta_n. $$

They have nonzero coefficient $\sigma$. Each numerator variable $u_{hi}$ occurs as a monomial with coefficient one. The origin also belongs to the support. Thus the Newton polytope contains both $B\times\lbrace0\rbrace$ and $\lbrace0\rbrace\times\Delta_p$, where the second factor uses the numerator coordinates.

By convexity it contains every midpoint of a point of the first set and a point of the second. Since these coordinate spaces are disjoint, that set of midpoints is precisely

$$ \left(\frac12 B\right)\times\left(\frac12\Delta_p\right). $$

This is a full dimensional set. Its ordinary volume is

$$ 2^{-2p}\left(\frac1{n!}\right)^H\frac1{p!}. $$

Multiplication by $(2p)!$ converts ordinary to normalized volume and proves the first inequality. Finally,

$$ \frac{(2p)!}{p!}=\prod_{j=p+1}^{2p}j\geq p^p,\qquad (n!)^H\leq n^{nH}=n^p, $$

so the claimed second inequality follows from $p=nH$. $\blacksquare$

## Scope of the obstruction

This calculation concerns the normalized parameter polynomial, not its degree as a Boolean input polynomial. It also does not lower-bound the number of sign patterns or the number of components in the admissible parameter domain. It rules out the proposed explanation that the common Newton polytope is small enough, by itself, to remove the logarithmic dependence on $H$.

The use of normalized Newton volume in neural-network sign counting is explicit in [Rojas and Vidyasagar, Theorems 3 and 4](https://arxiv.org/html/math/0112208v3). The inclusion and volume lower bound above are direct calculations for this manuscript's polynomial. They are audited on paper and are not formalized in Lean.
