# Audit of universal constructions near the counting scale

## Status and model

This note preserves and independently checks auxiliary arguments supplied by the asker, then records new adversarial construction checks from this run. It proves no new unrestricted bound on $W(n)$. In particular, no universal construction of order $2^n/n^2$ and no fixed-exponent lower improvement has been obtained here.

The score is $S(x)=c+\sum_{h=1}^H A_h(x)/B_h(x)$ on $\lbrace0,1\rbrace^n$. Numerator and denominator are affine. Every denominator is positive on the whole cube and its slopes are all strictly positive, all strictly negative, or all zero. In the last case the original numerator restriction remains. All constructions below that purport to be original heads explicitly use nonconstant coherent denominators.

## Lower-star transplantation

Partition $a+b$ coordinates into sets $I,J$, with $a,b\geq2$, and use inputs $v_{ij}=\mathbf1-e_i-e_j$ for $i\in I,j\in J$. Let the desired positive additive denominator table be $C_{ij}=\theta_i+p_j$. Set

$$ M=\max_{i,j}C_{ij},\qquad r_i=\max_k\theta_k-\theta_i,\qquad s_j=\max_\ell p_\ell-p_j. $$

Then $C_{ij}=M-r_i-s_j$, and these deficits are invariant under the gauge change $\theta\mapsto\theta+t$, $p\mapsto p-t$.

**Proposition.** A denominator $B(x)=d+\sum_i\beta_i x_i+\sum_j\gamma_jx_j$, with $d,\beta_i,\gamma_j\gt0$, realizes the table exactly if and only if

$$ M\gt\sum_i r_i+\sum_j s_j. $$

**Proof.** Differences within a row or column force $\beta_i=r_i+u$ and $\gamma_j=s_j+v$ for positive $u,v$. The maximal entry then forces

$$ d=M-\sum_i r_i-\sum_j s_j-(a-1)u-(b-1)v. $$

Thus positivity implies the displayed criterion. Conversely, when it holds, sufficiently small positive $u,v$ give $d\gt0$ and the required table. All positive coefficients ensure positivity on the entire cube. $\blacksquare$

Every positive additive table instead embeds with strictly negative slopes. Choose $\varepsilon\gt0$ with $2\varepsilon\lt\min C$, put

$$ w_i=\theta_i-\min_k\theta_k+\varepsilon,\qquad z_j=p_j-\min_\ell p_\ell+\varepsilon,\qquad d=\min_{i,j}C_{ij}-2\varepsilon, $$

and take $B(x)=d+\sum_iw_i(1-x_i)+\sum_jz_j(1-x_j)$. The coefficients $w_i,z_j,d$ are positive and $B(v_{ij})=C_{ij}$.

This is an orientation mismatch for a particular localization scheme, not a model-wide impossibility. A lower-star localization that adds large positive coefficients on forbidden coordinates cannot simultaneously retain negative slopes on programmed coordinates. Joint cancellation or a different localization could evade it.

## Near constancy on a lower star

For the positive-slope case put $K=d+\sum_i\beta_i+\sum_j\gamma_j$, $\lambda_i=\beta_i/K$, and $\mu_j=\gamma_j/K$. Then

$$ B(v_{ij})/K=1-\lambda_i-\mu_j,\qquad \sum_i\lambda_i+\sum_j\mu_j\lt1. $$

For $0\lt\eta\lt1$, delete rows with $\lambda_i\gt\eta/2$ and columns with $\mu_j\gt\eta/2$. Fewer than $2/\eta$ indices in total are deleted. Every remaining denominator belongs to $[K(1-\eta),K]$.

This is a valid individual-head statement. Arbitrary signed cancellation prevents deducing a sign-preserving approximation of a sum from it. No such approximation is assumed.

## Independent polynomial-size patches

Fix a residual score $R$ and $m$ sample inputs. Suppose a module of $H$ new heads must realize every strict labeling on those inputs by varying only its own coefficients. Dropping coherence can only enlarge the label class. Clearing positive denominators gives the polynomial test

$$ P_x=R(x)\prod_{h=1}^HB_h(x)+\sum_{h=1}^HA_h(x)\prod_{g\neq h}B_g(x). $$

It has degree at most $H$ in $p=2(n+1)H$ real parameters. For $m\geq p$, [Warren's strict-sign estimate, as stated in Alon, Proposition 5.4](https://web.math.princeton.edu/~nalon/PDFS/tools1.pdf), gives at most

$$ \left(\frac{4eHm}{p}\right)^p=\left(\frac{2em}{n+1}\right)^{2(n+1)H} $$

sign tables. Therefore shattering requires

$$ H\geq\frac{m}{2(n+1)\log_2(2em/(n+1))}. $$

If $m\lt p$, the inequality $H\gt m/[2(n+1)]$ already holds. Thus both regimes are covered by

$$ H\geq\frac{m}{2(n+1)\max\lbrace1,\log_2(2em/(n+1))\rbrace}. $$

For a fixed partition of the cube into independently programmed patches of size at most $n^C$, summing this inequality yields $H_{\mathrm{total}}=\Omega_C(2^n/(n\log n))$. Nonnegative correction overhead does not help.

The precise independence assumption matters. This argument does not count arbitrary target-dependent partitions or correlated residuals. Nor may one multiply conditional counts over uncountably many preceding parameter states merely because those states have the same earlier labels. Earlier modules could store information in their values on future inputs. No such multiplication is used here.

## Addressed permutations with first-order programming

Suppose $r$ Boolean address bits distinguish $H$ objects, so $2^r\geq H$, and the other $s=n-r$ coordinates independently permute them. There are at most $(H!)^s$ branches. Suppose each branch supplies signs of an affine parameter family of dimension at most $p=CnH$.

For $p\leq N=2^n$, each such family gives at most $\sum_{j=0}^p\binom Nj\leq(eN/p)^p$ strict sign patterns. The logarithmic total is at most

$$ s\log_2(H!)+p\log_2(eN/p). $$

At $H=\lfloor N/n^x\rfloor$ for fixed $x\gt1$, the address condition gives $s\leq x\log_2n+O(1)$, and $\log_2(H!)\leq nH$. Consequently the bound is $O_x(nH\log n)=o(N)$.

Thus these branches with strict first-order programming cannot give every cube label table at that width. Higher-order cancellation and general curved paths are excluded from this calculation. This qualification cannot be dropped.

## Check of the existing logarithmic compiler

Selective reads of `origin/ar/0f08fe6fb98a` establish that this branch contains a reported kernel-checked upper bound $W(n)=O(2^n/(n\log n))$. Its final module is `formalization/HeadComplexity/Results/UniversalLogSaving.lean`, with declaration `HeadComplexity.worstCaseHeadComplexity_isBigO_two_pow_div_mul_log`. The explicit reported bound is $W(n)\leq23232022^n/(n\log n)$ for $n\geq32$.

The source construction, `artifacts/head-compression/continuation-affine-plane-decoder.tex`, was independently read in this run. For $q=2^k$, it encodes $k$ bits in one real token at each point of $\mathbb F_q^2$. Cauchy kernels decode the bits. Nonvertical line sums have $q^2$ displayed rank factors, while each other point contributes to a query on at most one line. One admissible correction head per point cancels those off-target terms. In total, $2q^2+1$ heads program $kq^2$ rows on a one-hot row by one-hot column grid. Compact poles and tokens ensure that every denominator stays positive on the entire cube. Axis repair and a separately proved descending cover transfer the grid to the full cube.

The source uses full-cube denominator positivity, target-dependent tokens, arbitrarily precise real coefficients, and exact cancellation. It supplies a real global mechanism and is compatible with the current lower-bound goal. The reported Lean proof was not rebuilt in this run; this paragraph records the source and exact claims, not a fresh kernel verification.

The compiler also explains why the polynomial-patch barrier is quantitatively relevant: its local efficiency is logarithmic in the number of row coordinates. Increasing the finite-field size increases those coordinate costs. Replacing its one-hot columns by binary addresses would require the independently selected column tokens to become affine functions of the address bits; the given proof supplies no such replacement.

## New check. A one-parameter sign decoder has limited efficiency

The exact Cauchy decoder in the compiler uses $q=2^k$ poles to realize $k$ independent bits of a token. Sign-only decoding can potentially improve constants or logarithmic secondary terms, but cannot give a power saving in the row-to-head ratio through this mechanism alone.

**Lemma.** Let $r_1(t),\ldots,r_k(t)$ be rational functions with a common denominator that never vanishes on an interval. Suppose each numerator has degree at most $d$. If all $2^k$ strict sign vectors occur on that interval, then $kd\geq2^k-1$.

**Proof.** Remove the real roots of the $k$ nonzero numerators. There are at most $kd$ distinct roots and at most $kd+1$ complementary intervals. Each numerator and the common denominator have constant sign on each interval, so the whole sign vector is constant there. Identically zero numerators cannot realize strict sign vectors at all. Hence at most $kd+1$ vectors occur. $\blacksquare$

For $q$ simple common Cauchy poles, the numerator degree is at most $q-1$. Therefore universality requires $k(q-1)\geq2^k-1$. In particular $k=O(\log(q+1))$: for example $2^k\leq kq+1$ and $k\leq2^{k/2}$ for $k\geq4$ imply $k\leq2\log_2(2q)$.

Even if a sign-only decoder reduced the number of poles by a factor comparable to $k$, the finite-plane scheme would still obtain only $O(\log q)$ bits per point. This lemma does not rule out multivariate token schemes or a different compiler, and it gives no unrestricted lower bound.

## Unresolved global possibility

An exponential-size patch might consist of a one-hot row block and a $k$-bit full cube. The affine-plane compiler does not handle this geometry. A hypothetical slope dictionary permitting every $k$-bit label table using $O(2^k/k)$ heads, with only row-dependent intercepts and numerator constants, could beat the polynomial-patch limit when shared across many rows. No such dictionary or obstruction was obtained.

The scalar common-direction case cannot do this: restricting all denominators to a shared affine statistic makes the cleared univariate score have degree at most the number of heads, so an alternating label sequence needs a comparable number of heads. Allowing genuinely different directions is the unproved step. The original unrestricted exponent question remains open in this audit.

## Verification record

The transplantation criterion, deletion bound, polynomial sign count, address calculation, and one-parameter decoder lemma were checked independently as written proofs. No finite search is being substituted for universality, and no new Lean theorem is claimed. The original model definitions and statements were unchanged.
