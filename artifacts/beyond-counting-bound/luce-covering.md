# Uniform Covers of Bounded Head Tables

## Scope

This note proves a uniform covering theorem even when coherent denominators approach their admissible boundary. It then proves a counting theorem under an explicit margin relative to the sum of individual head amplitudes. That margin condition is not a hypothesis of the manuscript. No unconditional head lower bound, intermediate exponent, or solution of the selected target is claimed.

## A simultaneous cover of every choice menu

Let $m\geq1$ and $0\lt\epsilon\leq1$. For positive weights $w_1,\ldots,w_m$, and every nonempty subset $S$ of the indices, define the probability vector

$$ p_i(S)=\frac{w_i\mathbf1_{i\in S}}{\sum_{j\in S}w_j}. $$

### Theorem 1. Clipped adjacent ratios

There is a family of at most $m!(K+1)^{m-1}$ positive weight vectors whose choice tables approximate all such tables, simultaneously for every menu, within $\epsilon/2$ in the sum of absolute coordinate errors. Here

$$ r=1+\frac{\epsilon}{16m},\qquad K=\left\lceil\frac{\log(16m/\epsilon)}{\log r}\right\rceil\leq1+\frac{32m}{\epsilon}\log(16m/\epsilon). $$

**Proof.** Sort the weights in nondecreasing order, allowing any fixed tie rule. For $1\leq j\lt m$, write $g_j=w_{j+1}/w_j$ and choose

$$ q_j=\min\bigl(K,\lfloor\log_r g_j\rfloor\bigr),\qquad v_1=1,\qquad v_{j+1}=r^{q_j}v_j. $$

Each $q_j$ is one of $K+1$ integers, proving the stated cardinality after allowing all sorting permutations. The upper bound on $K$ follows from $\log(1+t)\geq t/2$ for $0\leq t\leq1$.

Fix a nonempty menu, and let $j_\ast$ be its largest sorted index. On this menu put $a_i=w_i/w_{j_\ast}$ and $b_i=v_i/v_{j_\ast}$. Put both quantities equal to zero off the menu, and write $A=\sum_i a_i$, $B=\sum_i b_i$. Both sums are at least one.

An index in the menu is *good* if no gap between it and $j_\ast$ satisfies $g_j\geq r^K$. For a good index, rounding changes each adjacent ratio by a factor less than $r$. Consequently

$$ a_i\leq b_i\leq r^m a_i\leq(1+\epsilon/8)a_i. $$

For the last inequality, the binomial theorem gives $r^m\leq(1-\epsilon/16)^{-1}\leq1+\epsilon/8$. Indeed $\binom{m}{k}\leq m^k$, so the binomial sum is at most the corresponding infinite geometric sum; and $t/(1-t)\leq2t$ for $t\leq1/2$.

For every remaining index in the menu, at least one gap was clipped. All other gaps are at least one, so

$$ a_i\leq r^{-K}\leq\frac{\epsilon}{16m},\qquad b_i\leq r^{-K}\leq\frac{\epsilon}{16m}. $$

The total unnormalized error therefore satisfies

$$ E=\sum_i|a_i-b_i|\leq\frac{\epsilon}{8}A+\frac{\epsilon}{8}\leq\frac{\epsilon}{4}A. $$

Finally, for any nonnegative vectors with positive sums,

$$ \sum_i\left|\frac{a_i}{A}-\frac{b_i}{B}\right|\leq\frac{2}{A}\sum_i|a_i-b_i|. $$

To prove this, expand each difference as $(a_i-b_i)/A+b_i(B-A)/(AB)$, apply the triangle inequality, sum, and use $|B-A|\leq E$. The desired error is at most $\epsilon/2$. The construction was independent of the menu. $\blacksquare$

Clipping all weights against the single largest weight would not prove this statement: a menu can omit that weight. Clipping adjacent sorted gaps is what permits a separate reference weight for every menu.

## Bounded affine ratios

Let $\mathcal F_n$ be the class of all tables on the Boolean cube of affine numerators divided by positive affine denominators whose nonconstant coefficients are all nonnegative or all nonpositive. Require $|F(x)|\leq1$ at every vertex. Zero denominator coefficients are allowed in this enlarged class.

### Theorem 2. Uniform head cover

For $n\geq1$, $m=n+1$, and $0\lt\epsilon\leq1$, this class has a cover in maximum absolute table error of radius $\epsilon$, containing at most

$$ A(n,\epsilon)=2m!(K_\tau+1)^{m-1}(2+8m/\epsilon)^m,\qquad \tau=\frac{\epsilon}{4m},\qquad K_\tau=\left\lceil\frac{\log(16m/\tau)}{\log(1+\tau/(16m))}\right\rceil. $$

In particular, for an absolute constant $C$,

$$ \log_2 A(n,\epsilon)\leq C(n+1)\log_2\bigl(C(n+1)/\epsilon\bigr). $$

**Proof.** Complement all input coordinates if necessary. The denominator is then $D(x)=w_0+\sum_i w_ix_i$, with $w_0\gt0$ and $w_i\geq0$. First suppose all weights are positive. Set $r_0=F(0)$ and $r_i=F(e_i)$; every one of these values is in $[-1,1]$. The affine numerator coefficients are determined by these values:

$$ a_0=r_0w_0,\qquad a_i=(w_0+w_i)r_i-r_0w_0. $$

For a vertex with support $S$ and $k=|S|$, use the choice menu $\lbrace0\rbrace\cup S$. Direct substitution gives

$$ F(S)=p_0(S)\left(r_0(1-k)+\sum_{i\in S}r_i\right)+\sum_{i\in S}p_i(S)r_i. $$

Every coefficient of a choice probability in this expression has absolute value at most $2m$. Round each $r_i$ to a mesh in $[-1,1]$ of step at most $\tau$, using at most $2+2/\tau$ possible values per coordinate. This changes each displayed coefficient by at most $2m\tau$. Approximate the choice table by Theorem 1 at accuracy parameter $\tau$, which changes its probability vector in sum norm by at most $\tau/2$, and hence by at most $\tau$.

The resulting table error is at most $2m\tau+2m\tau=\epsilon$. The two terms follow respectively by using that the original probabilities sum to one, and bounding the rounded coefficients by $2m$. The count is the product of the mesh count, the choice count, and the two input orientations.

If some $w_i$ vanish, replace the denominator by $D(x)+t\sum_i x_i$ with $t\gt0$, retaining the numerator. The resulting table still has absolute value at most one and converges to $F$ as $t$ decreases to zero. The same finite cover works for all $t$. Some center is used along a sequence tending to zero; its closed error ball contains $F$. Thus zero weights add no centers.

For the logarithmic estimate, Theorem 1 gives

$$ K_\tau\leq1+\frac{128m^2}{\epsilon}\log(64m^2/\epsilon). $$

Taking logarithms in the explicit expression for $A$, bounding $m!\leq m^m$, and using $\log\log t\leq\log t$ for $t\geq e$ proves the assertion with an absolute constant. $\blacksquare$

The centers can themselves be written as affine ratios. Their absolute table values can exceed one by the error radius, which does not affect the following estimate.

## Relative amplitude margin

For a score $S=c+\sum_{h=1}^H\phi_h$ of admissible heads, define

$$ M=|c|+\sum_{h=1}^H\max_x|\phi_h(x)|. $$

Assume $M\gt0$ and $\min_x|S(x)|\geq\gamma M$ for some $0\lt\gamma\leq1$. This ratio is unchanged by scaling the whole score. It is not implied by strict sign realization.

### Theorem 3. Conditional sign count

The number of Boolean labelings realized with this relative amplitude margin and at most $H$ heads is at most

$$ \left(A(n,\gamma/4)\frac{16e}{\gamma}\right)^{H+1}. $$

Consequently its logarithm is at most

$$ C(n+1)(H+1)\log_2\bigl(C(n+1)/\gamma\bigr) $$

for an absolute constant $C$.

**Proof.** Divide the score by $M$. It becomes a convex combination of $K=H+1$ members of $\mathcal F_n$, counting the signed constant term as one member and filling unused positions by arbitrary zero-weight members. The signs of the numerator coefficients absorb coefficient signs.

For $0\lt\rho\leq1$, the probability simplex in $K$ coordinates has a sum-norm cover of radius $\rho$ with at most $(4e/\rho)^K$ points. To see this, put $L=\lceil2K/\rho\rceil$, round down every coordinate to a multiple of $1/L$, and distribute the missing units among coordinates. The sum error is at most $2K/L\leq\rho$. The possible grid points number $\binom{L+K-1}{K-1}\leq\binom{L+K}{K}\leq(e(L+K)/K)^K\leq(4e/\rho)^K$.

Use $\rho=\gamma/4$ and approximate each head table with error $\gamma/4$. If $a,b$ are the original and rounded probability vectors, and $f,g$ the corresponding tables, then

$$ \left|\sum_i a_if_i(x)-\sum_i b_ig_i(x)\right|\leq\sum_i|a_i-b_i|+\sum_i b_i|f_i(x)-g_i(x)|\leq\gamma/2. $$

Here the first inequality uses $|f_i(x)|\leq1$. Every original coordinate has magnitude at least $\gamma$, so its sign is determined by the rounded table. Counting the choices proves the result. $\blacksquare$

For a fixed positive relative amplitude margin, universal representation would therefore require $\Omega(2^n/(n\log n))$ heads. For a guarantee $\gamma\geq\exp(-n^\beta)$ with $0\lt\beta\lt1$, it would require $\Omega(2^n/n^{1+\beta})$ heads. Both conclusions retain the displayed margin hypothesis.

## Exact gap to the requested theorem

The unrestricted model does not supply a positive lower bound on this ratio as a function of $n$ and the head count. Dividing the score by its minimum margin does not help: it scales $M$ by the same factor. Very large cancelling heads remain allowed. No transformation producing the needed relative amplitude margin at a sufficiently small head overhead has been proved.

In particular, the theorem only shows that if every Boolean function had $O(2^n/n^2)$ heads, then some of those functions would require relative amplitude margins exponentially small in $n$ in all representations with that head budget. Such conditioning is permitted. This implication does not refute the hypothesized head bound.

The [bounded amplitude obstruction](bounded-amplitude-obstruction.md) separately rules out a constant-overhead repair for fixed amplitude ratios, even for certain one-head functions. It does not settle possible repairs with larger overhead or weaker margins. The present route is blocked at that unconditional transfer step.

## Quantitative obstruction to a uniform repair

### Theorem 4. The exponent cost already occurs for one head

Fix $0\lt\beta\lt1$. Any procedure that replaces every one-head Boolean classifier on $n$ bits by a representation with relative amplitude margin at least $\exp(-n^\beta)$ must sometimes use $\Omega(n^{1-\beta})$ heads.

**Proof.** Use the explicit one-head halfspaces in [Sherstov's Theorem 1.2](https://web.cs.ucla.edu/~sherstov/pdf/hardest-hs.pdf). The amplitude obstruction proved in the linked note says that, for $1\leq H\leq cn$, every signed score confined to the interval $[1,B]$ satisfies $B+1\gt2^{1+an/H}$, for fixed positive constants $a,c$.

A relative amplitude margin $\gamma$ gives signed scores in $[\gamma M,M]$. Dividing by $\gamma M$ therefore permits $B=1/\gamma$. The displayed obstruction yields

$$ \gamma\lt\frac{1}{2^{1+an/H}-1}\leq2^{-an/H}. $$

If $\gamma\geq\exp(-n^\beta)$, taking logarithms gives $H\gt a(\log 2)n^{1-\beta}$. If $H\gt cn$, the same asymptotic conclusion holds already. $\blacksquare$

Thus a repair theorem with a uniform multiplicative head cost $o(n^{1-\beta})$ is false. Combining only a uniform multiplicative repair and Theorem 3 cannot obtain the desired intermediate exponent by assuming this smaller cost. This does not exclude a more selective mechanism that exploits a large original head count or the particular target function.

## Related choice-model literature

[Chierichetti, Giacchini, Kumar, Lattanzi, Panconesi, Tani, and Tomkins, Learning Multinomial Logits in O(n log n) time, version 2, November 19, 2026](https://arxiv.org/html/2601.04423v2) study the same simultaneous distance over all nonempty choice menus. They prove adaptive learning bounds with unrestricted positive weights, using approximate ordering and estimation forests; their revised additive-error bound uses $O(m\log m/\epsilon^2)$ pair queries. The present clipping proof is a direct deterministic finite-cover argument, not a claim that simultaneous choice approximation is new. Neither their learning result nor this cover controls cancellation in a signed sum of head tables.

## Verification

`formalization/HeadComplexity/Atoms/LuceCovering.lean` checks the normalization inequality, good-set error estimate, exact head/choice identity, and convex-combination error estimate. The sorting, clipping, finite cover counts, and conditional asymptotic deduction above are written proofs. The full covering theorem is not claimed to be formalized.
