# Tensor Sign Rank and the Cost of Converting Heads

## A concrete obstruction

For a Boolean sign table $f$ on $n$ bits, define its tensor sign rank to be the least $R$ for which some functions $g_{hi}:\lbrace0,1\rbrace\to\mathbb R$ satisfy

$$ f(x)\sum_{h=1}^R\prod_{i=1}^n g_{hi}(x_i)\gt0\qquad\text{for every }x. $$

A constant term, if present, is counted as one product. The factors and coefficients are unrestricted real numbers. This rank permits a target-dependent separable dictionary, so the sparse-Walsh obstruction does not apply to it.

There is nevertheless no absolute constant $C$ bounding this rank by $CH$ for every admissible $H$-head classifier. More precisely, there is an infinite sequence of pairs $(n,H)$ and admissible functions with tensor sign rank greater than $cH\log_2n$, for an absolute $c\gt0$.

### Lemma 1. Some square sign matrices have linear sign rank

For every integer $M\geq200$, there is an $M$ by $M$ sign matrix with sign rank greater than $\lfloor M/100\rfloor$, and hence greater than or equal to $M/200$.

**Proof.** Put $r=\lfloor M/100\rfloor$. A real matrix of rank at most $r$ factors as $UV$, where $U$ has size $M$ by $r$ and $V$ has size $r$ by $M$. Its entries are quadratic polynomials in $2Mr$ parameters. Since $r\leq M/2$, Warren's strict-sign theorem bounds the number of resulting sign matrices by

$$ \left(\frac{4eM}{r}\right)^{2Mr}. $$

Here $M/200\leq r\leq M/100$. Since $e\lt3$, the base is less than $2400\lt2^{12}$, and the exponent is at most $M^2/50$. The count is therefore less than $2^{(12/50)M^2}\lt2^{M^2}$. It cannot include all sign matrices. This uses the same strict Warren theorem as the manuscript; see also [Goldberg and Jerrum, Theorem 2.1](https://www.cs.ox.ac.uk/people/paul.goldberg/papers/goldbergjerrum.pdf). $\blacksquare$

### Lemma 2. Restricting a product tensor to a two-hot slice

Split $2M$ input coordinates into two blocks. Restrict a tensor of rank at most $R$ to the inputs $(e_i,e_j)$. Each product term becomes a function of $i$ times a function of $j$, so the resulting $M$ by $M$ real matrix has rank at most $R$. Consequently every tensor sign representation of a Boolean function has rank at least the sign rank of its two-hot sign matrix. This assertion allows zero entries in individual factors; the complete represented table must have strict signs.

### Theorem 3. A logarithmic conversion loss is necessary

Let $q=2^s$ with $s\geq4$, and put

$$ H=2q^2,\qquad M=\frac{q(q+1)s}{2},\qquad n=2M. $$

The already proved [bipartite reciprocal construction](bipartite-reciprocal-shattering.md) realizes every sign matrix on the $M^2$ inputs $(e_i,e_j)$ using exactly $H$ admissible heads. Every denominator has strictly positive constant and slope coefficients. Choose the sign matrix from Lemma 1, and let $f$ be the full-cube Boolean function computed by its head witness. If a full-cube score has zero values away from the selected inputs, a sufficiently small negative change of the readout bias makes all its classifications strict and preserves the selected signs.

By Lemma 2 its tensor sign rank is greater than $M/200$. In particular, its ratio to the head count is greater than or equal to

$$ \frac{M}{200H}=\frac{(q+1)s}{800q}\geq\frac{s}{800}. $$

Also $\log_2n=\log_2(q(q+1)s)\leq2s+1+\log_2s\leq4s$ for $s\geq4$. Thus the ratio is at least $(\log_2n)/3200$. This proves the claimed obstruction. $\blacksquare$

The head realization used here is a previously Lean-checked theorem. The sign-rank counting argument and tensor restriction argument are complete written proofs in this note. No new Lean declaration for their combination is claimed.

## What would be needed for an asymptotic head lower bound

A rank $R$ product tensor on $n$ bits has $2nR$ real factor parameters, and each table entry is a polynomial of degree at most $n$ in them. Warren's theorem therefore gives, when $2nR\leq2^n$,

$$ \lvert\lbrace\text{strict signs of rank }R\text{ tensors}\rbrace\rvert\leq\left(\frac{2e2^n}{R}\right)^{2nR}. $$

Substituting $R=\lfloor c2^n/(n\log_2n)\rfloor$ for a fixed $c\lt1/2$ makes the base-two logarithm of this bound $(2c+o(1))2^n$. Hence some Boolean functions have tensor sign rank greater than this $R$.

A universal conversion with cost $CH\log n$ would combine with that fact to yield a head lower bound of order $2^n/(n(\log n)^2)$, which would refute the requested upper bound. Theorem 3 shows that a constant conversion cost is impossible and that the logarithm cannot simply be omitted.

No conversion with cost $CH\log n$ is proved. Integral representations of reciprocals by exponentials provide separable terms, but replacing those integrals by few nodes has no established uniform sign guarantee under arbitrary signed cancellation. The sparse-polynomial result also shows that well-conditioned denominators alone do not supply a general sign-preserving approximation argument.

This route is blocked at the conversion theorem. The counting calculation is a benchmark, not a new proof mechanism for the original target, and it must not be counted as a resolution. Reopening it requires an actual uniform construction or an invariant that establishes such a conversion in the unrestricted model.
