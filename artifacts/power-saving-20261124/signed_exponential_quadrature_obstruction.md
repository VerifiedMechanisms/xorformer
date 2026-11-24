# Signed exponential quadrature can require superpolynomially many nodes

## Status and scope

This note proves an obstruction to a joint, target-dependent quadrature compiler that retains the original head numerators and denominator directions. Arbitrary signed weights, arbitrary real exponential nodes, a free output bias, unbounded coefficients, and collisions of nodes are all permitted. Even for one displayed admissible two-head representation, such a compiler can require exponentially many nodes in the square root of the input dimension.

This is not a lower bound on the original number of heads, nor on product sign rank with freely chosen directions. The constructed target already has a two-head representation and has a sign representation by four product atoms with other directions. The result rules out a particular possible bridge to a polynomial-degree sign count.

The proof is written mathematics. No Lean verification of the new separation theorem or construction is claimed.

## Uniform separation from signed exponential sums

### Lemma 1. Real zeros of an exponential polynomial

Let $s_1,\ldots,s_M$ be distinct real numbers. A nonzero function

$$ q(t)=\sum_{i=1}^M a_i e^{-s_i t} $$

has at most $M-1$ real zeros, counted with multiplicity.

**Proof.** Induct on the number of nonzero coefficients. One nonzero exponential has no zero. For more than one term, multiply by $e^{s_1t}$, which preserves all zero multiplicities. The derivative is an exponential sum with at most $M-1$ nonzero terms. On any finite interval containing a finite collection of zeros of total multiplicity $z$, Rolle's theorem, including the zeros inherited from multiplicities, gives at least $z-1$ derivative zeros. Induction gives $z-1\leq M-2$. Thus every finite collection has total multiplicity at most $M-1$, proving the claim. The derivative is not identically zero because distinct real exponentials are linearly independent; this independence also follows inductively from the same differentiation operation. $\blacksquare$

### Theorem 2. Uniform reciprocal separation

Fix an integer $K\geq0$ and $M=2K+1$ distinct positive numbers $s_1,\ldots,s_M$. Put $r=(1/s_i)_{i=1}^M$. There is a number $\Delta\gt0$, depending only on these query values, such that

$$ \left\|r-\left(\sum_{j=1}^K c_j e^{-t_j s_i}\right)_{i=1}^M\right\|_2\geq\Delta $$

for every choice of real coefficients $c_j$ and real nodes $t_j$.

In particular, the reciprocal vector is outside the closure of this set of signed exponential sums. There are no boundedness, separation, or positivity conditions on the nodes or coefficients.

**Proof.** For any $K$ given nodes, enlarge the collection of distinct nodes to exactly $K$ distinct real numbers if necessary. Solve the $2K$ homogeneous linear equations

$$ q(t_j)=q'(t_j)=0,\qquad 1\leq j\leq K, $$

in the $2K+1$ coefficients of $q(t)=\sum_i a_i e^{-s_i t}$. There is a nonzero solution. Lemma 1 shows that its prescribed zeros have multiplicity exactly two and that there are no other zeros. Therefore $q$ has one sign on the real line. Choose the overall sign so that $q(t)\geq0$ everywhere, and normalize $\|a\|_2=1$.

Consider the set

$$ C=\left\lbrace a\in\mathbb R^M:\|a\|_2=1,\ \sum_i a_i e^{-s_i t}\geq0\text{ for every }t\in\mathbb R\right\rbrace. $$

It is nonempty by the preceding construction and compact because it is a closed subset of the unit sphere. For every $a\in C$, the continuous nonnegative function $q_a$ is nonzero. Lemma 1 implies that it cannot vanish on the entire positive half-line. Since all $s_i$ are positive, its integral on that half-line is finite and strictly positive:

$$ \ell(a):=\sum_i\frac{a_i}{s_i}=\int_0^\infty q_a(t)dt\gt0. $$

The displayed integral notation uses the ordinary real integral. The linear function $\ell$ is continuous on $C$, so it has a strictly positive minimum $\Delta$ there.

For any proposed exponential sum vector $v$, choose the normalized coefficient vector $a\in C$ constructed from its nodes. Then $a\cdot v=\sum_j c_j q_a(t_j)=0$. Consequently

$$ \|r-v\|_2\geq a\cdot(r-v)=\ell(a)\geq\Delta. $$

This is uniform over all nodes and coefficients and proves the theorem. $\blacksquare$

A free constant in the exponential sum counts as one additional node, namely $t=0$. Therefore $2K+3$ distinct positive query values suffice to separate the reciprocal vector uniformly from a free constant plus $K$ exponential terms. No compactness assumption on a parameterization of the proposed sums is needed: the compact set used in the proof consists of normalized separating functions.

## An exact coherent two-head construction

### Theorem 3. Superpolynomial node requirement

For every integer $n\geq144$, there is a strict Boolean target on $\lbrace0,1\rbrace^n$ with an admissible displayed two-head score

$$ S(x)=c_0+\frac1{B(x)}-r(x), $$

where $B$ has strictly positive constant and slopes and $r$ has strictly positive slopes, with the following property. If a score of the form

$$ G(x)=c+\sum_{j=1}^{K}a_j e^{-t_j B(x)}-r(x)\sum_{j=1}^{J}b_j e^{-u_j} $$

has exactly the same strict signs as $S$ on the whole cube, then

$$ K\geq2^{\sqrt n/6}. $$

Here $J$ is arbitrary and all weights, nodes, and the bias $c$ are arbitrary real numbers. Thus the result allows separate quadratures for the two heads and unlimited quadrature complexity in the constant-denominator head.

**Proof.** First construct an example from a squarefree positive integer $P$ with $2^k$ divisors, where $k\geq2$. Set

$$ L=\lceil\log_2(P+1)\rceil,\qquad J_0=2L+1,\qquad \eta=\frac1{4J_0}. $$

Use $4L+2$ Boolean coordinates, organized into pairs $u_j^+,u_j^-$ and $v_j^+,v_j^-$ for $0\leq j\lt L$, and one pair $w^+,w^-$. On each selected query exactly one member of every pair is one. The $u^+$ coordinates encode $d-1$, where $d$ is a divisor of $P$. The $v^+$ coordinates encode $y=P/d$. Both numbers fit in $L$ bits.

Define the affine denominator

$$ B=1-J_0\eta+\sum_{j=0}^{L-1}\left((\eta+2^j)u_j^++\eta u_j^-\right)+\sum_{j=0}^{L-1}\eta(v_j^++v_j^-)+\eta(w^++w^-). $$

Its constant is $3/4$, and every slope is strictly positive. It is therefore strictly positive everywhere on the cube. On the selected queries the pair baselines cancel its constant adjustment and give exactly

$$ B=1+(d-1)=d. $$

Choose a positive number $\varepsilon$, to be made sufficiently small below, and put $\gamma=1+\varepsilon$. Define

$$ r=-J_0\gamma+\sum_{j=0}^{L-1}\gamma(u_j^++u_j^-)+\sum_{j=0}^{L-1}\left((\gamma+2^j/P)v_j^++\gamma v_j^-\right)+(\gamma+\varepsilon)w^++(\gamma-\varepsilon)w^-. $$

Every slope of $r$ is strictly positive, including $\gamma-\varepsilon=1$. For the two selected queries associated to divisor $d$, it satisfies

$$ r=\frac1d+\varepsilon\quad\text{when }w^+=1,\qquad r=\frac1d-\varepsilon\quad\text{when }w^-=1. $$

Thus $1/B-r$ has opposite signs on this pair, negative on the first query and positive on the second. Choose $c_0\in(-\varepsilon/2,\varepsilon/2)$ avoiding the finitely many values $r(x)-1/B(x)$ on the cube. This makes $S=c_0+1/B-r$ nonzero everywhere and preserves every prescribed paired sign.

The original-model representation is admissible: the first head has numerator one and the strictly positive-slope denominator $B$, while the second has denominator one and numerator $-r$, whose slopes are all strictly negative. The bias is free.

Any candidate compiled score can be written as $G=c+Q(B)-\alpha r$, with $Q(s)=\sum_{j=1}^K a_j e^{-t_j s}$ and $\alpha=\sum_{j=1}^Jb_j e^{-u_j}$. Its two strict inequalities at divisor $d$ imply

$$ c+Q(d)-\alpha/d-\alpha\varepsilon\lt0,\qquad c+Q(d)-\alpha/d+\alpha\varepsilon\gt0. $$

These force $\alpha\gt0$ and

$$ \left|\frac c\alpha+\sum_{j=1}^K\frac{a_j}{\alpha}e^{-t_jd}-\frac1d\right|\lt\varepsilon. $$

Let $M=2^k$, and choose any $M-1$ distinct divisors of $P$. Put $K_0=M/2-2$, so $M-1=2(K_0+1)+1$. Apply Theorem 2 to these $M-1$ positive query values and $K_0+1$ nodes, counting the free bias as one node. Choose $\varepsilon\lt\Delta/\sqrt{M-1}$. The preceding inequalities contradict the separation theorem whenever $K\leq K_0$. Therefore every such compiler needs

$$ K\geq2^{k-1}-1. $$

To obtain the stated dimension bound, choose distinct primes $p_1,\ldots,p_k$ with $p_j\leq2^j$, starting with $p_1=2$ and using Bertrand's postulate at each step. For $P=\prod_jp_j$ this gives

$$ \log_2P\leq\frac{k(k+1)}2,\qquad 4L+2\leq2k(k+1)+6. $$

Given $n\geq144$, take $k=\lfloor\sqrt n/2\rfloor$. Then $2k(k+1)+6\leq n$. If the construction uses fewer than $n$ bits, add strictly positive coefficients to both $B$ and $r$ on every unused coordinate and fix these extra coordinates to zero on all selected queries. Positivity, coherent slopes, and every selected query value are preserved. Choose the strictifying bias after adding these coordinates.

Finally, $k\geq\sqrt n/3$ for $n\geq36$, and for $n\geq144$ one has

$$ 2^{k-1}-1\geq2^{k-2}\geq2^{\sqrt n/6}. $$

This proves the theorem. $\blacksquare$

Bertrand's postulate is available in the repository's mathlib source as `Nat.exists_prime_lt_and_le_two_mul` in `formalization/.lake/packages/mathlib/Mathlib/NumberTheory/Bertrand.lean`. Its statement is that every positive integer has a prime strictly above it and at most twice it. The new construction and separation theorem have not been formalized by citing that declaration.

## Exact limitation of the obstruction

The construction refutes a polynomial-node compiler even when the node locations and signed weights are chosen jointly after seeing the whole target. It includes geometric grids, head-specific grids, arbitrary real nodes, and arbitrary limits of such sums. The two crucial restrictions are that the original affine numerator factor of each head is retained and that its exponential direction remains a scalar multiple of the original denominator.

Changing directions makes this particular target easy. Put $R=r-c_0$. Multiplication by the positive denominator shows that its strict signs equal those of $1-RB$. For sufficiently small positive $t$, the score

$$ 1-\frac{(e^{tR}-1)(e^{tB}-1)}{t^2} $$

has the same signs on the finite cube, since it converges pointwise to the nonzero table $1-RB$. Expanding the product gives four exponential product atoms, including the constant atom. Since $R$ and $B$ are affine, each exponential is a product of one-bit factors. Hence Theorem 3 is not a lower bound on the number of product atoms with freely chosen directions.

Allowing the affine numerator factors to move also removes this particular obstruction without changing the denominator direction: $1+R(e^{-tB}-1)/t$ converges to $1-RB$ and consists of two affine-times-product terms. Thus the theorem does not rule out compilers that jointly redistribute affine numerator factors between the original denominator directions.

No implication for the requested unrestricted exponent improvement follows without a different joint compilation mechanism or another sign-counting argument.
