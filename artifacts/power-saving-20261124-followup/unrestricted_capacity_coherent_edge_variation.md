# Coherent edge variation and mixed-point amplitude

## A dimension-free edge inequality

Let $\phi=A/B$ be one original admissible head whose affine denominator slopes are nonnegative, and let $u=\|\phi\|_\infty$ on the full Boolean cube. At a vertex $x$, let $P$ denote its one-coordinates. Then

$$ \sum_{i\in P}|\phi(x)-\phi(x-e_i)|\leq2u. $$

For a head with nonpositive denominator slopes, the complementary statement is

$$ \sum_{j:x_j=0}|\phi(x)-\phi(x+e_j)|\leq2u. $$

Zero slopes are allowed. A constant denominator belongs to both cases. The numerator coefficients are arbitrary real numbers.

**Proof.** Restrict to the face obtained by varying the coordinates in $P$, and put $c=\phi(x)$. Write $B=B(x)$ and let $a_i,b_i$ be the affine numerator and denominator slopes on this face. All $b_i\geq0$, and

$$ \phi(x)-\phi(x-e_i)=\frac{p_i}{B-b_i},\qquad p_i=a_i-cb_i. $$

Partition the indices according to the sign of $p_i$. For the nonnegative group $I$, write $B_I=B-\sum_{i\in I}b_i\gt0$. The full-cube norm bound at the vertex with all coordinates of $I$ deleted gives

$$ cB_I-\sum_{i\in I}p_i\geq-uB_I,\qquad \sum_{i\in I}p_i\leq(c+u)B_I. $$

Every $B-b_i\geq B_I$, so the sum of the nonnegative edge differences is at most $c+u$. Applying the upper norm bound to the negative group gives a sum of absolute negative differences at most $u-c$. Adding proves the result. Complementing the entire cube proves the negative-orientation case; this global complementation preserves coherence. No independent coordinate flips are used. $\blacksquare$

`CoherentEdgeVariation.affine_ratio_corner_variation` kernel-checks this statement with subsets encoding vertices of the restricted face. `sum_abs_edge_le` checks the underlying deletion-budget inequality, and `sum_div_le` checks the common-denominator comparison.

## A mixed-star functional

Fix a mixed vertex $p$ with $r\geq1$ one-coordinates $P$ and $s\geq1$ zero-coordinates $Q$. Define

$$ L(T)=T(p)-\frac1r\sum_{i\in P}T(p-e_i)-\frac1s\sum_{j\in Q}T(p+e_j)+\frac1{rs}\sum_{i\in P,j\in Q}T(p-e_i+e_j). $$

The functional kills constants, has coefficient absolute sum four, and satisfies $L(\mathbf1_p)=1$.

For a positive-orientation head, group the expression as the average downward difference at $p$ minus the average downward difference over the vertices $p+e_j$. The edge inequality at each of these vertices gives

$$ |L(\phi)|\leq\frac{4\|\phi\|_\infty}{r}. $$

For a negative-orientation head, grouping the upward differences instead gives

$$ |L(\phi)|\leq\frac{4\|\phi\|_\infty}{s}. $$

`mixedContrast_bound_of_down` and `mixedContrast_bound_of_up` kernel-check these averaging implications for arbitrary finite rectangular data. `mixedContrast_swap` checks their symmetry. The instantiation by cube neighbors is the displayed written construction.

## Amplitude obstruction at arbitrary width

Let $S=b+\sum_h\phi_h$ be any original score, with arbitrary signed cancellation and any number of heads. Its actual amplitude is $D=|b|+\sum_h\|\phi_h\|_\infty$. If

$$ \|S-\mathbf1_p\|_\infty\leq\varepsilon, $$

then

$$ D\geq\frac{\min(r,s)}4(1-4\varepsilon). $$

**Proof.** The error bound and the coefficient absolute sum of $L$ give $1-4\varepsilon\leq|L(S)|$. Constants vanish, and the head bounds give $|L(S)|\leq4D/\min(r,s)$. $\blacksquare$

This is a written theorem for the original model, using the kernel-checked edge and averaging inequalities. It does not give a head-count lower bound: increasing the number of heads cannot eliminate this amplitude cost, but large amplitudes remain permitted.

## Consequence for joint product replacements

The indicator of the zero-face specified by $Q$ is a uniform limit of norm-one positive-orientation heads. The indicator of the one-face specified by $P$ is a uniform limit of norm-one negative-orientation heads. Their product is $\mathbf1_p$.

Consequently there is no compiler that approximates the product of every pair of norm-one original heads to arbitrary uniform accuracy with amplitude bounded by an absolute constant independent of $n$, even if its output head count is unrestricted. For balanced mixed vertices, a fixed error below $1/4$ already forces amplitude of order $n$.

The argument leaves polynomial or exponential amplitude overhead open. Such overhead may still be compatible with the much smaller relative-margin thresholds in the research target. It also does not imply that a whole truth table requiring a poorly conditioned representation exists: the statement concerns approximation of values, and every fixed mixed-point truth table has other admissible representations.

The stronger higher-difference extension in `mixed_point_high_order_amplitude.md`, uses the anchored expansion and is a separate written argument. The first-order edge proof here does not depend on it.

## Verification boundary

The edge bound and both averaging implications are kernel checked in `formalization/HeadComplexity/Research/CoherentEdgeVariation.lean`. The passage to arbitrary original scores and the product-compiler obstruction are written proofs. An independent agent audited the edge partition, both averaging bounds, the four disjoint support layers, and the arbitrary-width amplitude consequence. Original definitions and admissibility conditions are unchanged. This checkpoint does not resolve the unrestricted lower-bound benchmark.

`lake build HeadComplexity.Research.CoherentEdgeVariation` completed successfully with 3842 jobs. All six theorem declarations in `CoherentEdgeVariationAudit.lean` have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. The GitHub render audit recognized all 46 mathematical spans.
