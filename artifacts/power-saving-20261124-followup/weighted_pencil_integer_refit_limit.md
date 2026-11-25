# Quantitative limit of direct integer refitting on a weighted pencil

## Scope

This is a written intermediate bound and a precise failed inequality, not an unrestricted repair theorem. It concerns a fixed positive integer statistic $t(x)=\sum_i w_ix_i$, with $w_i\gt0$ and $0\leq t(x)\leq L$ on the Boolean cube. It keeps arbitrary affine numerators and signed cancellation.

Suppose an original score has $H$ denominator poles on this pencil. Clearing their positive product expresses its sign as

$$ F(x)=\sum_{i=0}^n x_iP_i(t(x)),\qquad x_0=1,\qquad \deg P_i\leq H. $$

Using $H+1$ rather than $H$ as the degree allowance also absorbs a free bias without a special case. The feature count is at most $p=(n+1)(H+1)$, and every integer feature has absolute value at most $V=\max(1,L^H)$.

## Direct refitting bound

The active-row integer separator argument gives coefficients with absolute value at most $M=p!V^p$ and signed gap at least one. Redundant features only decrease the determinant size, so this bound remains valid without assuming feature independence.

Choose new positive poles $1,\ldots,H+1$ and let $Q(t)=\prod_{j=1}^{H+1}(t+j)$. Each numerator $P_i(t)/Q(t)$ has a partial-fraction decomposition with residues bounded by $M(H+1)^{H+1}$. Indeed, $|P_i(-j)|\leq M(H+1)^{H+1}$ and the integer nonzero denominator $|Q'(-j)|$ is at least one.

The resulting score has $H+1$ genuine same-direction heads, full-cube signed gap at least $(L+H+1)^{-(H+1)}$, and head mass at most $(n+1)(H+1)^{H+2}M$. Therefore it has relative margin at least

$$ \gamma\geq\left[(n+1)(H+1)^{H+2}p!\max(1,L^H)^p(L+H+1)^{H+1}\right]^{-1}. $$

Zero statistic slopes may be made strictly positive by a sufficiently small perturbation after the strict finite-cube gap is established. This preserves the signs and changes the displayed margin by at most a fixed factor. The bound has no dependence on the original pole conditioning.

## Why this does not reach either requested scale

The bound pays

$$ \log\gamma^{-1}=O\left(p\log p+pH\log(L+1)+H\log(L+H+1)\right). $$

At the critical exponentially large widths this is much larger than either $\exp(\sqrt n)$ or $\exp(n/\log n)$. The inequality needed for the proposed repair, namely that this logarithm be at most one of those quantities, fails by an exponential factor even when $L$ is only polynomial in $n$.

This is not just a weakness of the determinant estimate for arbitrary weighted directions. The written theorem in `approximate_shared_direction_obstruction.md` gives tables represented by $H$ constant-numerator binary-direction heads such that every same-direction comparison score, of arbitrary finite width, with at most $N/16$ label errors has relative margin at most $2^{-\lfloor H/[8(n+4)(n+1)^2]\rfloor}$. Its logarithmic inverse margin is already of order $H/n^3$. Consequently no same-direction refitting theorem can supply either requested margin uniformly at the critical widths, even under the allowed approximation.

The ordinary Hamming statistic is different because its central probability mass occupies only $O(\sqrt n)$ distinct levels. The successful written repair in `approximate_hamming_pencil_repair.md` exploits that fact and does not extend merely from concentration of a general weighted statistic. New denominator directions or a direct count of this structured class are necessary.
