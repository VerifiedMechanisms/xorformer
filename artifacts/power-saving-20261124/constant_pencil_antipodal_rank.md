# An antipodal rank obstruction for a constant-base pencil

## Statement

Let $n\geq1$, $N=2^n$, and let $s(x)$ be any nonconstant affine function on the Boolean cube. Fix $H\geq1$ distinct constants $\lambda_h$ such that all denominators $\lambda_h+s(x)$ are nonzero. Allow arbitrary affine numerators and a free bias. After multiplication by their common denominator product, the resulting table space has dimension at most

$$ \min\left\lbrace\frac N2,n\left\lceil\frac H2\right\rceil\right\rbrace+\min\left\lbrace\frac N2,1+n\left\lfloor\frac H2\right\rfloor\right\rbrace. $$

For example, when $n=6$ and $H=11$, this bound is $63$, although the crude count $nH+1$ is $67$. Thus an unconditional claim that this fixed pencil always has rank $\min(N,nH+1)$ is false. This is a table-space statement, not the requested original head lower bound.

## Proof

Subtract the mean of $s$ and absorb the shift into the constants $\lambda_h$. Put $z_i=2x_i-1$, so the centered function has the form $s=\sum_iw_iz_i$ and changes sign under the antipodal map $x\mapsto1-x$.

Clearing denominators and absorbing the free bias into one affine numerator gives a polynomial table of the form

$$ \sum_{j=0}^{H-1}L_j(x)s(x)^j, $$

with affine $L_j$. This space is contained in

$$ V=\mathrm{span}\left(\lbrace1\rbrace\cup\lbrace z_i s^j:1\leq i\leq n,\ 0\leq j\leq H-1\rbrace\right). $$

Indeed every scalar term $s^j$ with $j\geq1$ equals $\sum_iw_iz_is^{j-1}$. A generator $z_is^j$ is odd under the antipodal map when $j$ is even, and even when $j$ is odd. Therefore the odd part of $V$ has dimension at most $n\lceil H/2\rceil$, and the even part has dimension at most $1+n\lfloor H/2\rfloor$.

The antipodal involution pairs the $N$ cube vertices without fixed points. Its even and odd table eigenspaces each have dimension $N/2$. Intersecting with these ambient bounds and adding the two parts gives the stated inequality. Multiplication by the fixed nonzero denominator product is an invertible diagonal map on table space, so the same rank bound holds before clearing. $\blacksquare$

## Scope

The proof applies to a pencil containing the constant form, so that every denominator can be normalized to $\lambda_h+s$. It does not automatically apply to a general pencil spanned by two nonconstant affine forms. It does not show that a different, target-dependent denominator family misses the same labels. In particular, the result supplies no unrestricted exponent improvement.

The argument is an elementary written proof. No Lean verification is claimed. A preliminary modular probe suggested the $n=6,H=11$ example, but the displayed rank bound proves that example without computation.
