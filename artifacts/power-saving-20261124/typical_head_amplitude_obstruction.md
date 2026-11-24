# Typical Boolean functions force small relative head margins

## Status and scope

This is an independently checked preservation of an auxiliary theorem supplied by the asker on 2026-11-24. It is a written proof, not Lean verification, and is not a lower bound on head count. In particular, it does not resolve the requested exponent improvement.

Let $X=\lbrace 0,1\rbrace^n$, let $N=2^n$, and choose $F:X\to\lbrace -1,+1\rbrace$ uniformly with independent values. Consider any finite sum

$$ S(x)=c+\sum_{h=1}^H\phi_h(x),\qquad \phi_h(x)=A_h(x)/B_h(x),\qquad B_h(x)\gt0. $$

Here numerator and denominator are affine. The argument permits every denominator orientation and hence applies to all admissible original heads. Define the representation-dependent quantity

$$ M=|c|+\sum_{h=1}^H\max_{x\in X}|\phi_h(x)|,\qquad T_n=2\sum_{j=0}^n\binom{N-1}{j}. $$

## Statement

For every $0\lt\delta\lt1$, with probability at least $1-\delta$, simultaneously for every finite $H$ and every such representation,

$$ \min_{x\in X}F(x)S(x)\leq2\sqrt{\frac{2\log(2T_n/\delta)}N}M. $$

For $n\geq2$ and $\delta=2^{-n^2}$ this gives

$$ \min_{x\in X}F(x)S(x)\leq\frac{4n}{\sqrt N}M. $$

Whenever $S$ strictly represents $F$, its relative head-amplitude margin is therefore at most $4n2^{-n/2}$. The assertion is simultaneous over target-dependent denominators, arbitrary coefficients and cancellations, and all head counts.

## Proof

### Lemma 1. Counting halfspace traces

An affine form on $n$ variables is linear in $n+1$ coefficients. The equation that it vanishes at a particular cube input defines a central hyperplane in coefficient space. The number of open regions cut out by $N$ central hyperplanes in dimension $n+1$ is at most $T_n$.

For completeness, if $R(m,d)$ is the maximal number of central regions, adding the last hyperplane gives $R(m,d)\leq R(m-1,d)+R(m-1,d-1)$. The regions that split inject into regions of the induced arrangement on the last hyperplane. The initial bounds $R(1,d)=2$ and $R(m,1)\leq2$ give $R(m,d)\leq2\sum_{j=0}^{d-1}\binom{m-1}{j}$ by induction. Degeneracies only decrease the count.

Every weak affine-halfspace trace is also strict: add a sufficiently small positive constant to its defining affine form. Finiteness of the cube keeps every formerly negative value negative and moves zero values to positive ones. Let $\mathcal H_n$ be the collection of these traces, including $\varnothing$ and $X$. Thus $|\mathcal H_n|\leq T_n$.

### Lemma 2. One event controls every head

Put

$$ D(F)=\max_{Q\in\mathcal H_n}\left|\sum_{x\in Q}F(x)\right|. $$

For fixed nonempty $Q$ and $t\gt0$, independence and $\cosh u\leq e^{u^2/2}$ give the Chernoff estimate

$$ \Pr\left(\left|\sum_{x\in Q}F(x)\right|\geq t\right)\leq2\exp\left(-\frac{t^2}{2|Q|}\right)\leq2\exp\left(-\frac{t^2}{2N}\right). $$

The empty set is trivial. A union bound over the finite trace family gives

$$ \Pr(D(F)\geq t)\leq2T_n e^{-t^2/(2N)}. $$

Consequently, with probability at least $1-\delta$,

$$ D(F)\leq\sqrt{2N\log(2T_n/\delta)}. $$

### Lemma 3. Layer-cake estimate

For a single head $\phi=A/B$ let $L=\max_X|\phi|$. If $L=0$, its correlation is zero. Otherwise $g=\phi/L$ takes values in $[-1,1]$ and satisfies the pointwise integral identity

$$ g(x)=\int_0^1\left(\mathbf1_{\lbrace g(x)\geq t\rbrace}-\mathbf1_{\lbrace g(x)\leq-t\rbrace}\right)dt. $$

Endpoint conventions in these level sets do not affect the integral. Because $B\gt0$, both level sets are affine-halfspace traces:

$$ \lbrace g\geq t\rbrace=\lbrace A-tLB\geq0\rbrace,\qquad \lbrace g\leq-t\rbrace=\lbrace -A-tLB\geq0\rbrace. $$

Interchanging the finite sum over $X$ with the integral proves

$$ \left|\sum_{x\in X}F(x)\phi(x)\right|\leq2LD(F). $$

The constant term has correlation at most $|c|D(F)$ because $X$ itself is a trace. Hence, deterministically and simultaneously over every representation,

$$ \sum_{x\in X}F(x)S(x)\leq D(F)\left(|c|+2\sum_h\|\phi_h\|_\infty\right)\leq2D(F)M. $$

The left side is at least $N\min_xF(x)S(x)$. Combining this with Lemma 2 proves the first statement. There is no union bound over heads, coefficients, or representations.

### Lemma 4. The explicit constant

For $n\geq2$, the usual binomial estimate yields

$$ \sum_{j=0}^n\binom{N-1}{j}\leq\left(\frac{e(N-1)}n\right)^n. $$

It follows, with $\delta=2^{-n^2}$, that

$$ \log(2T_n/\delta)\leq\log4+n\log(eN/n)+n^2\log2=2(\log2)n^2+n-n\log n+\log4\leq2n^2. $$

For the final inequality, subtract its left side from $2n^2$. The resulting real function is positive at $n=2$ and has derivative $4(1-\log2)n+\log n\gt0$ for real $n\geq2$. Substitution proves the stated $4n/\sqrt N$ bound. $\blacksquare$

## Consequence and limitation

A representation theorem for almost every target cannot provide a polynomial relative head-amplitude margin, regardless of how many heads are allowed. In particular, if a normalized-atom covering argument pays $O(nH\log(n/\gamma))$, its required margin scale already contributes $\log(1/\gamma)=\Omega(n)$ on typical targets. Excluding parity alone cannot repair that method.

This does not constrain head count without an additional relation between head count and relative margin. No such relation is proved here, and no additional normalization is imposed on the original model.

## Independent audit record

On 2026-11-24, the preservation audit independently checked the central-arrangement recurrence, weak-to-strict trace reduction, Chernoff optimization, level-set identity, simultaneous quantifiers, and the explicit constant. The proof remains written-only. No source model definition was changed.
