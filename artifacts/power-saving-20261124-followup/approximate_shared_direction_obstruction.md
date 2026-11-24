# Approximation does not repair a fixed binary direction

## Statement and scope

This is a written theorem extending the exact shared-direction obstruction. It permits changing every pole, arbitrary affine numerators, arbitrary signed cancellation, arbitrary finite comparison width, and errors on one sixteenth of the entire Boolean cube. The restriction is that every comparison denominator retains the same binary address direction, up to sign. New denominator directions remain outside the theorem.

Put $N=2^n$, with $n\geq4$, and let $M=2^k$ for an integer $4\leq k\leq n$. Suppose

$$ M\geq16(n+4)(n+1)^2,\qquad q=\left\lfloor\frac{M}{8(n+4)(n+1)^2}\right\rfloor. $$

There is a truth table $F$ represented by $M$ original heads such that every strict original score $S$ whose truth table differs from $F$ on at most $N/16$ inputs, and whose denominators have the forms

$$ a+bz(x)\quad\text{or}\quad a+b(N-1-z(x)),\qquad a\gt0,\quad b\geq0,\qquad z(x)=\sum_{i=1}^n2^{i-1}x_i, $$

has full-cube relative margin at most $2^{-q}$. The comparison width can be any finite integer. For $b=0$ we even allow arbitrary affine numerators over constant denominators, an enlargement of the original model.

Since $q\geq M/[16(n+4)(n+1)^2]$, the margin upper bound is exponentially small in $M/n^3$. At either critical width in the research request, choose the largest power of two $M$ not exceeding that width. The resulting upper bound is eventually smaller than both the corresponding tested double-exponential margin and every margin $\exp(-\mathrm{poly}(n))$.

The truth table has a good representation at the same width when new directions are allowed. It is merely an arbitrary function of its $k$ high address bits. Its multilinear expansion has $2^k=M$ monomials and coefficient mass at most $3^k$. The genuine monomial margin compiler therefore gives width $M$ and margin at least $1/(2\cdot3^k+1)$. Thus this is a counterexample to a direction-preserving approximate repair, not to the unrestricted goal.

## A uniform comparison space

The shell construction in [the shared-direction note](margin_repair_shared_direction_obstruction.md) gives a linear space $U_{q-1}$ of real tables, containing the constant table, with

$$ d:=\dim U_{q-1}\leq2(n+1)^2q. $$

Every allowed ratio $\phi=A/B$ admits a table $Q_\phi\in U_{q-1}$ satisfying, on every cube vertex,

$$ |\phi(x)-Q_\phi(x)|\leq2^{-q}|\phi(x)|\leq2^{-q}\|\phi\|_\infty. $$

The same space works for all allowed poles and both orientations. It is independent of the target and the comparison width. Consequently a strict comparison score with relative margin greater than $2^{-q}$ has exactly the same truth table as a strict member of $U_{q-1}$.

Indeed, retain the bias and sum the individual approximations. The uniform error is at most $2^{-q}\sum_h\|\phi_h\|_\infty$, which is strictly smaller than the signed gap at every vertex. This step uses the sum of individual full-cube norms, so arbitrary cancellation does not invalidate it.

## Counting all approximate comparison tables

A $d$-dimensional linear space on $N$ inputs has at most $(4eN/d)^d$ strict sign tables, by the degree-one Warren bound. Here $d\geq1$, since the constant table belongs to the space, and $d\leq N$. Using $e\lt4$ gives the convenient coarse bound

$$ \left|\mathrm{sign}_{\mathrm{strict}}(U_{q-1})\right|\leq(16N)^d=2^{(n+4)d}\leq2^{M/4}. $$

The last inequality is exactly the chosen bound on $q$. The unconditional Warren theorem used here is kernel checked in this repository; this particular application is written mathematics.

Partition the consecutive integers $0,\ldots,N-1$ into $M$ intervals of equal length $L=N/M$. Each word $w\in\lbrace-1,1\rbrace^M$ defines a cube table $F_w$ by assigning the constant value $w_j$ on interval $j$.

For any arbitrary comparison table $g$, let $m(g)$ be its majority word on the $M$ intervals, with either fixed rule for ties. If $g$ differs from $F_w$ at most $N/16$ times, each interval where $m(g)$ differs from $w$ contributes at least $L/2$ errors. Hence

$$ d_H(w,m(g))\leq M/8. $$

A Hamming ball of radius $M/8$ in $M$ bits contains strictly fewer than $2^{3M/4}$ words. An elementary integer proof weights every matching coordinate by four and every mismatching coordinate by one. The sum of the weights over all words is $5^M$, while every word in that ball has weight at least $4^{7M/8}$. Since $5^8\lt2^{20}$, the claimed bound follows. This is the same finite weighted-count method as `ApproximateMarginCounting.card_hammingBall_weighted`.

There are at most $2^{M/4}$ majority words arising from strict sign tables of $U_{q-1}$. Their radius $M/8$ balls therefore cover strictly fewer than $2^M$ words. Choose a word $w$ outside this union and set $F=F_w$. Then no strict table from $U_{q-1}$ agrees with $F$ on at least $15N/16$ inputs.

This counts truth tables, not representations. In particular it proves the required universal quantifier over every comparison score satisfying the shared-direction restriction.

## Realizing the chosen block table at the original width

The sign sequence of $F$ on the ordered address values changes at most $M-1$ times. Put one real root halfway between consecutive integer addresses at each actual sign change. The product of these linear factors, multiplied by an appropriate sign, is a real polynomial $p$ of degree at most $M-1$ with

$$ \mathrm{sign}(p(z(x)))=F(x)\qquad\text{on the entire cube}. $$

It has no integer root. The $M$ polynomials $\prod_{j\neq h}(z+j)$, for $1\leq h\leq M$, form a basis of the polynomials of degree at most $M-1$, by evaluating at the distinct numbers $-h$. Therefore constants $a_h$ exist with

$$ \frac{p(z)}{\prod_{h=1}^M(z+h)}=\sum_{h=1}^M\frac{a_h}{z+h}. $$

Each denominator has positive intercept and strictly positive binary slopes, so every summand is admissible in the original model. The common denominator is positive on the cube. The displayed $M$ heads strictly represent $F$.

If an arbitrary-width shared-direction comparison score had margin greater than $2^{-q}$ and differed from $F$ on at most $N/16$ inputs, the shell approximation would produce an excluded strict table from $U_{q-1}$. This contradiction completes the theorem.

## Consequence for concentration arguments

All the original denominators in a fixed-pencil version can additionally be chosen uniformly close to a constant, using the same partial-fraction basis with $1+t\lambda_h(1+z)$. Consequently concentration or Taylor approximation of each denominator cannot by itself prove a direction-preserving approximate margin repair. The collective numerator coefficients can encode the excluded block word at every positive scale.

A surviving theorem must change directions, or control which whole truth tables remain after such changes. The present construction does not show that any of its tables lacks a good comparable-width representation in that larger class. No new lower bound on the original unrestricted worst-case complexity is asserted.
