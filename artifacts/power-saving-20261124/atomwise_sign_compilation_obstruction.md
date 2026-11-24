# Fixed Atomwise Product Compilation Obstruction

## Status and scope

The following elementary proofs were independently checked in this run on 2026-11-24. They rule out a fixed atomwise replacement preserving all linear score signs. They do not rule out a transformation that depends jointly on the full score or its target labels, and they do not prove a lower bound on unrestricted head complexity. No Lean formalization is claimed.

## Two-term signs force a common multiplier

Let $X$ be finite, and let $\mathcal F$ be a collection of strictly positive real functions on $X$ containing $1$. Suppose a map $\Phi:\mathcal F\to\mathbb R^X$ preserves, pointwise, the sign of every strict score $af+b1$ after replacing it by $a\Phi(f)+b\Phi(1)$, for every $f\in\mathcal F$ and $a,b\in\mathbb R$.

Then there is one function $q:X\to(0,\infty)$ such that

$$ \Phi(f)(x)=q(x)f(x)\qquad(f\in\mathcal F,\ x\in X). $$

**Proof.** The score $1$ implies that $q=\Phi(1)$ is positive everywhere. The score $f$ similarly implies that $\Phi(f)$ is positive. If $\Phi(f)(x)/q(x)\neq f(x)$, choose a positive number $t$ strictly between these two values, avoiding the finitely many values $f(y)$ and $\Phi(f)(y)/q(y)$ for $y\in X$. Then $f-t$ and its replacement $\Phi(f)-tq$ are both strict on $X$, but their signs disagree at $x$. This contradiction proves the assertion. $\blacksquare$

## Every positive multiplier leaves a full-rank reciprocal

Let $n\geq2$, $m=\lfloor n/2\rfloor$, and $M=2^m$. Split $2m$ coordinates into two blocks of size $m$, with binary address values $i,j\in\lbrace0,\ldots,M-1\rbrace$. Fix any unused coordinate to zero. For every positive table $q$ on the cube, there is an admissible affine denominator $B$ such that the restricted matrix $q(x)/B(x)$ has rank $M$.

**Proof.** Write $Q_{ij}$ for the restricted positive table. For positive $t$, take $B_t(x)=1+t(i+j)$, with an additional strictly positive coefficient on the unused coordinate if $n$ is odd. All binary address weights are positive, so this is an original-model denominator with strictly positive slopes. Consider

$$ D(t)=\det\left(\frac{Q_{ij}}{1+t(i+j)}\right) _{0\leq i,j\lt M}. $$

At the formal parameter value $t_0=-1/(M-1)$, exactly the antidiagonal entries have poles. The reversal permutation is the unique term of the determinant expansion using all $M$ of these poles. Every other permutation uses fewer. Consequently

$$ \lim_{t\to t_0}(1+(M-1)t)^M D(t)=\mathrm{sgn}(\mathrm{reversal})\prod_{i=0}^{M-1}Q_{i,M-1-i}\neq0. $$

Thus $D$ is a nonzero rational function. It has no positive pole and only finitely many positive zeros. Any other positive $t$ gives the desired full rank. The negative value $t_0$ is used solely to prove a rational identity is nonzero; the actual denominator has positive $t$ and is admissible. $\blacksquare$

## Consequence

A product atom $\prod_i g_i(x_i)$ has matrix rank at most one across the indicated split. A sum of $K$ product atoms has rank at most $K$. An affine function times a product atom has rank at most two, by splitting the affine numerator into its two block contributions. A free bias adds rank at most one.

Apply the first theorem to the positive family consisting of the constant function and all admissible reciprocal atoms, and then apply the second theorem to the forced multiplier $q$. A fixed atomwise replacement by at most $K$ product atoms, preserving all strict two-term signs with constants, must therefore satisfy

$$ K\geq2^{\lfloor n/2\rfloor} $$

for some reciprocal atom. If the allowed replacement uses affine-times-product atoms and a free bias, the necessary inequality is

$$ 2K+1\geq2^{\lfloor n/2\rfloor}. $$

Thus a fixed polynomial-size per-head quadrature cannot provide exact cancellation-independent sign preservation for all scores. A successful argument would need joint score dependence, controlled classification error, a special degeneration such as a fixed radial germ, or another mechanism.
