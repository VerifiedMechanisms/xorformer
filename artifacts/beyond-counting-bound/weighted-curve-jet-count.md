# Weighted Counting for Rational Curve Coefficients

## Statement and scope

This note gives a counting mechanism for sums of Taylor coefficients of rational curves. It does not prove an improved lower bound for unrestricted head complexity. In particular, no reduction of arbitrary head sums to a small number of curve centers is assumed.

Fix integers $n\geq1$, $q\geq1$, and $K_1,\ldots,K_q\geq1$. Write $d=n+1$, $M=\sum_iK_i$, and $k_i=K_i-1$. For each $i$, let

$$ A_i(t,x)=\sum_{j=0}^{k_i}A_{ij}(x)t^j,\qquad B_i(t,x)=\sum_{j=0}^{k_i}B_{ij}(x)t^j, $$

where every coefficient function is affine in $x\in\mathbb R^n$. Require that $B_{i0}$ is positive on the Boolean cube and has either all strictly positive slopes or all strictly negative slopes. Define

$$ R_i(x)=\mathrm{coeff}_{t^{k_i}}\left(\frac{A_i(t,x)}{B_i(t,x)}\right),\qquad F(x)=\sum_{i=1}^q R_i(x). $$

Only strict sign tables are counted. Define $\pi_i=K_i/M$ and the binary entropy

$$ E(\pi)=\sum_{i=1}^q\pi_i\log_2(1/\pi_i). $$

**Theorem 1.** For the fixed list of orders above, the VC dimension of this class of strict cube classifiers is at most

$$ 4(n+1)M\bigl(6+E(\pi)\bigr). $$

Every strict table in this class has an actual admissible representation with at most $M$ heads. This is an inclusion in the unrestricted head class, not the reverse inclusion.

For one curve, the VC bound is $24(n+1)M$. For $q=M$ and all $K_i=1$, it is $4(n+1)M(6+\log_2M)$, which retains the loss at issue in the main problem.

## The weighted polynomial mechanism

Suppress the center index temporarily. Let $r_j$ be the coefficient of $t^j$ in $A/B$ and put $P_j=B_0^{j+1}r_j$. Coefficient comparison in $B(A/B)=A$ gives the polynomial recurrence

$$ P_0=A_0,\qquad P_j=A_jB_0^j-\sum_{a=1}^jB_a B_0^{a-1}P_{j-a}. $$

Assign weight $a+1$ to every affine parameter of both $A_a$ and $B_a$. For each fixed input, $P_j$ is weighted homogeneous of degree $2j+1$. Indeed, the first term has weight $(j+1)+j$, while every summand has weight $(a+1)+(a-1)+(2(j-a)+1)=2j+1$. This also proves inductively that clearing the denominator gives a polynomial, with no use of the Boolean relations.

For the sum over centers, the positive common denominator is $\prod_i B_{i0}^{K_i}$. The resulting sign polynomial is

$$ P(x)=\sum_{i=1}^q P_{i,k_i}(x)\prod_{h\neq i}B_{h0}(x)^{K_h}. $$

The term indexed by $i$ has weighted degree $2K_i-1+M-K_i=M+K_i-1\leq2M-1$. There are

$$ p=2dM $$

real parameters. Their weight product is

$$ \prod_{i=1}^q(K_i!)^{2d}. $$

Let $V$ be the convex hull of all monomial exponent vectors of the sample polynomials, together with the origin and all coordinate unit vectors in parameter space. It lies in the weighted simplex of degree $2M$. All unit vectors are included because their weights are at most $\max_iK_i\leq M$. With volume normalized so that the standard $p$-simplex has volume one,

$$ \mathrm{Vol}_p(V)\leq\frac{(2M)^p}{\prod_i(K_i!)^{2d}}\leq(2e)^p2^{pE(\pi)}. $$

The last inequality follows from $K!\geq(K/e)^K$ and $p=2dM$. For completeness, the factorial bound follows by summing $\log j$ and comparing with $\int_1^K\log t dt$; the integral equals $K\log K-K+1$.

## From Newton volume to strict signs

The external results used here concern real signs, not constructible zero/nonzero classifiers. [Rojas, Main Theorem 1.1](https://arxiv.org/pdf/math/9905004) bounds the connected components of real algebraic fibers by a constant times their augmented Newton volume. In the deliberately weaker normalization stated in [Vidyasagar and Rojas, Theorems 1 and 3](https://arxiv.org/html/math/0112208v3), the two relevant inequalities are

$$ B\leq2^p\mathrm{Vol}_p(V),\qquad \mathrm{VCdim}\leq2\log_2B+2p\log_2(2es). $$

Here $B$ bounds the components of every regular fiber of every system obtained by choosing at most $p$ sample polynomials, and $s$ is the number of polynomial predicates used to classify one input. Constants subtracted to specify a fiber only add the zero exponent, already included in $V$.

Apply these results to the single predicate $P(x)\gt0$, with $s=1$, allowing all parameter values. This enlarged polynomial class contains the admissible strict cube class: the restrictions on $B_{i0}$ need not be added as extra predicates. The common Newton containment holds for every choice of samples. Consequently

$$ \mathrm{VCdim}\leq2p\bigl(\log_2(8e^2)+E(\pi)\bigr)\lt2p\bigl(6+E(\pi)\bigr). $$

This proves the asserted non-strict upper bound after substituting $p=2(n+1)M$. If the class shatters the entire cube, its VC dimension is at least $2^n$. Thus the theorem is a genuine necessary condition for universality of this fixed-order curve class. It is not a necessary condition for a larger class without a representation theorem. $\blacksquare$

## Exact-model inclusion by finite differences

Fix a strict table $F$. For each center set $G_i(t,x)=A_i(t,x)/B_i(t,x)$. Positivity on the finite cube and strict coherence of the slopes are open conditions on the coefficients. Thus every denominator $B_i(jt,x)$, for $0\leq j\leq k_i$, is positive and has the same strict slope orientation for all sufficiently small $t\gt0$.

The finite-difference formula gives, uniformly over the finite cube,

$$ \frac{1}{k_i!t^{k_i}}\sum_{j=0}^{k_i}(-1)^{k_i-j}\binom{k_i}{j}G_i(jt,x)\longrightarrow R_i(x). $$

Indeed, the alternating binomial sum annihilates powers $j^a$ for $a\lt k_i$ and equals $k_i!$ for $a=k_i$. Analyticity near zero bounds the remaining Taylor terms. When $k_i=0$, the formula is simply $G_i(0,x)$.

Summing over the finitely many centers and choosing $t$ sufficiently small preserves the strictly nonzero signs of $F$ at every vertex. Each summand in each finite difference is one affine ratio with an admissible strict denominator orientation. Its scalar coefficient is absorbed in its unrestricted affine numerator. The manuscript's exact normal form therefore supplies at most $\sum_i(k_i+1)=M$ actual heads. No lower bound on the final margin, numerator norm, or coefficient precision is required.

A free readout bias introduces no additional parameters needed for this bound. At any chosen center, adding $cB_{i0}$ to $A_{i,k_i}$ adds exactly the constant $c$ to $R_i$.

## Why this does not settle the requested lower bound

For ordinary heads, take $q=M=H$ and $K_i=1$. This recovers the entropy $\log_2H$, rather than removing it. The calculation is sensitive to a different parametrization, but it does not produce that parametrization for arbitrary strict labels.

For a single curve to cover every $H$-head sign table with $M\leq C H\log n$ would imply an improved worst-case head bound. No such conversion is established here. It is a theorem-strength gap. Exact rational equality cannot supply this conversion with one affine base denominator: on a continuous open set, a sum with distinct genuine affine poles has those distinct poles, whereas a single curve coefficient has only powers of its base denominator. Equality of signs on the finite cube is a substantially weaker requirement, so this pole argument does not disprove a sign conversion.

Even a constant-overhead sign conversion is impossible uniformly over all $n,H$. The existing [actual bipartite shattering construction](bipartite-reciprocal-shattering.md) has $q_0=2^s$, $H=2q_0^2$, $M_0=q_0(q_0+1)s/2$, $n=2M_0$, and $M_0^2$ shattered cube points. A conversion to one curve of order budget $K$ would force

$$ K\geq\frac{M_0^2}{24(n+1)},\qquad \frac{K}{H}\geq\frac{s}{288}\quad(M_0\geq1). $$

For the second inequality use $n+1=2M_0+1\leq3M_0$ and $M_0/H\geq s/4$. This obstruction occurs in a different head regime from the main exponential-scale target. It does not rule out a logarithmic-overhead conversion, and it does not prove one.

## Verification status

The coefficient recurrence, weighted-volume calculation, and actual-model inclusion are complete written proofs. The topology and VC inequalities are externally cited theorems whose stated hypotheses were checked above. No new Lean result is claimed for them, and no improved unrestricted head lower bound follows. The precise open step is a global sign-count or representation theorem that controls independent target-dependent denominator centers.
