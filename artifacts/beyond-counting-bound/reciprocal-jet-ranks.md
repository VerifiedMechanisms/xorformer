# Finite Reciprocal Jet Ranks

## Matrix and exact meaning

For an integer $d$, positive integer weights $\beta_1,\ldots,\beta_d$, and distinct positive integers $r_1,\ldots,r_q$, define a matrix with columns indexed by $y\in\lbrace0,1\rbrace^d$ and rows indexed by pairs $(j,S)$ with $1\leq j\leq q$ and $S\subseteq\lbrace1,\ldots,d\rbrace$, $|S|\leq2$:

$$ M_{(j,S),y}=\frac{\prod_{i\in S}y_i}{(r_j+\beta\cdot y)^3}. $$

There are $qL_d$ rows, where $L_d=1+d+\binom d2$. The script `test_reciprocal_jet_rank.py` performs Gaussian elimination over the prime field of order 65521. Every denominator in the retained cases is nonzero modulo this prime. Full row rank over that field therefore certifies full row rank over the rational numbers: the corresponding nonzero minor is the reduction of a rational minor whose denominator is invertible modulo the prime.

All integer products during elimination are bounded in magnitude by the square of the prime, which is below the signed 64-bit range. Thus the NumPy integer operations used by the elimination do not overflow. The rank results are exact finite computations, not floating-point rank estimates.

## Completed cases

The retained file `reciprocal-jet-rank-results.jsonl` contains 64 completed eliminations for $4\leq d\leq13$. Every binary-weight case, with $\beta_i=2^{i-1}$ and $r_j=j+1$, has full row rank. In particular, the largest such case has $d=13$, $q=89$, 8188 rows, and 8192 columns, and its rank is 8188.

Some randomly chosen positive integer weights give deficient rank. For example, the recorded thirteen-bit case with 8188 rows has rank 7158. Repeated weights and repeated subset sums occur in that example. The observations do not justify asserting full rank for arbitrary positive weights.

A later fourteen-bit elimination was killed with exit code 137 before returning a rank. Its interruption is recorded in `experiments/long-job-outcomes.json`; it supplies no rank conclusion.

## Scope

These rows arise in value, gradient, and Hessian interpolation for fixed linear functionals of reciprocal evaluations. Full rank could help construct additional parameter-space critical points. Such points are not Boolean sign patterns. No asymptotic rank theorem or head-complexity lower bound follows from this finite table.

The proposed general statement that binary weights give full row rank whenever $qL_d\leq2^d$ remains unproved. It is an auxiliary interpolation question, not a substitute for the research target.
