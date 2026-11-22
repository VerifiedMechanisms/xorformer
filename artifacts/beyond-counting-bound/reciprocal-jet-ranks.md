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

## Memory-bounded extension

A subsequent implementation, `blocked_mod_rank.py`, completed the binary-weight cases in dimensions thirteen, fourteen, and fifteen. The complete records are in `reciprocal-jet-blocked-results.jsonl`. The selected pivot columns are the first as many columns as there are rows in each case.

| Dimension | Number of poles | Rows | Columns | Rank modulo 65521 | Selected minor determinant modulo 65521 |
| --- | --- | --- | --- | --- | --- |
| 13 | 89 | 8188 | 8192 | 8188 | 9985 |
| 14 | 154 | 16324 | 16384 | 16324 | 63020 |
| 15 | 270 | 32670 | 32768 | 32670 | 62774 |

The new implementation stores residues in sixteen-bit unsigned arrays and performs elimination in panels of at most 64 columns. Panel row operations and modular reductions use signed 64-bit integers. Trailing block products use binary64 matrix multiplication and then convert back to integers. This use of floating-point storage has an exact-integer justification, not a numerical rank tolerance: every operand is an integer between zero and $65520$, and every dot product has at most 64 terms. Hence every product and partial sum is an exactly representable integer, since

$$ 64\cdot65520^2=274743705600\lt2^{53}. $$

The panel algorithm applies ordinary row swaps, normalizes each pivot, and records the unnormalized pivot values. For each trailing block, forward substitution first computes the normalized pivot rows, and subtraction of their recorded multiples gives the Schur complement. The product of the pivots, multiplied by the row-swap sign, is the determinant of the selected square minor. No column-swap sign is needed because pivot columns are retained in increasing order.

Before the large calculations, 120 finite tests compared the blocked rank to a separate scalar modular implementation. These included rectangular and rank-deficient matrices over three different prime fields, with four panel widths. Whenever full row rank held, a separate scalar determinant calculation checked the selected minor determinant. The thirteen-dimensional rank also agrees with the earlier independent elimination. The larger computations remain executable arithmetic certificates, not Lean proofs of the elimination algorithm or an asymptotic result.

## Scope

These rows arise in value, gradient, and Hessian interpolation for fixed linear functionals of reciprocal evaluations. Full rank could help construct additional parameter-space critical points. Such points are not Boolean sign patterns. No asymptotic rank theorem or head-complexity lower bound follows from this finite table.

The proposed general statement that binary weights give full row rank whenever $qL_d\leq2^d$ remains unproved. It is an auxiliary interpolation question, not a substitute for the research target.

## An exact obstruction in small characteristic

The choice of field matters for structural reasons. Let $K$ be a field of characteristic two or three, let the $r_j$ and $\beta_i$ belong to $K$, and assume all denominators are nonzero at every Boolean vertex. For any $q\geq1$, the same reciprocal-cube matrix satisfies

$$ \mathrm{rank}_K M\leq qL_d-q+1. $$

In particular, two or more pole blocks can never have full row rank over either characteristic, even if there are enough columns. This is not a statement about characteristic zero or about the prime 65521 used above.

**Proof.** Write $c(y)=\sum_i\beta_i y_i$. In characteristic three, the Frobenius identity and $y_i^3=y_i$ give

$$ (r+c(y))^3=r^3+\sum_i\beta_i^3y_i. $$

In characteristic two, squaring first gives $c(y)^2=\sum_i\beta_i^2y_i$. Multiplication by $r+c(y)$ then gives

$$ (r+c(y))^3=r^3+\sum_i(r^2\beta_i+r\beta_i^2)y_i+\sum_{i,j}\beta_i\beta_j^2y_i y_j. $$

Using $y_i^2=y_i$ and collecting the two orders of each distinct pair, the right side is a linear combination of the squarefree monomials of degree at most two. Dividing by $(r+c(y))^3$ proves that the constant function one is in every pole block's row span. Its coefficient on that block's constant-numerator row is $r^3$, which is nonzero: evaluation of the denominator at the all-zero vertex gives $r\neq0$.

For each block after the first, subtract its representation of one from the first block's representation. This gives $q-1$ row relations. They are independent because each relation has a nonzero coefficient on the constant-numerator row of its own block, and all other relations have coefficient zero on that row. Rank-nullity proves the bound. $\blacksquare$

The cube expansions and the normalized identities are proved in `formalization/HeadComplexity/Atoms/ReciprocalJetCharacteristic.lean`, notably `HeadComplexity.ReciprocalJetCharacteristic.constant_identity_char_two` and `HeadComplexity.ReciprocalJetCharacteristic.constant_identity_char_three`. The row-rank consequence is the written argument above. This prevents importing a characteristic-two coding construction directly as a full-rank certificate for this particular jet matrix.
