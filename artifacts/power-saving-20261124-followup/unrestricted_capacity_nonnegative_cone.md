# Nonnegative original heads cannot approximate a mixed-point gate

## The arbitrary-width cone obstruction

Fix a Boolean vertex $p$ with $r\geq2$ one-coordinates and $s\geq2$ zero-coordinates. Let $S$ be a sum of any number of original admissible heads, each nonnegative on the full cube. A nonnegative constant bias may also be included. Then

$$ \|S-\mathbf1_p\|_\infty\geq\frac15. $$

There is no restriction on the coefficient magnitudes, denominators, head count, or total amplitude. The nonnegativity of every summand is essential. Arbitrary signed original-head sums are outside this theorem.

## The one-head corner inequality

Suppose first that $\phi=A/B\geq0$ and the denominator slopes are nonnegative. Restrict to the face obtained by varying the one-coordinates $P$ of $p$. Its bottom vertex is denoted $0_P$. The affine identity is

$$ \sum_{i\in P}A(p-e_i)=(r-1)A(p)+A(0_P). $$

Since $A(0_P)\geq0$, $A(p-e_i)\geq0$, and $0\lt B(p-e_i)\leq B(p)$, division gives

$$ \phi(p)\leq\frac1{r-1}\sum_{i\in P}\phi(p-e_i). $$

For a nonpositive denominator orientation, complementary coordinates give

$$ \phi(p)\leq\frac1{s-1}\sum_{j\in Q}\phi(p+e_j). $$

Global complementation preserves the original coherent orientation condition. No independent coordinate flips are used.

`NonnegativeHeadCone.affine_corner_ratio_le` kernel-checks the first inequality with subsets encoding the restricted face. `corner_ratio_le` isolates its scalar identity and positive-denominator comparison.

## Summing both orientations

Partition the heads by orientation. Since every head is nonnegative, each partial orientation sum at a neighbor is at most the complete score there. Therefore

$$ S(p)\leq\frac1{r-1}\sum_{i\in P}S(p-e_i)+\frac1{s-1}\sum_{j\in Q}S(p+e_j). $$

A nonnegative constant satisfies either one-head inequality because $r/(r-1)\geq1$ and $s/(s-1)\geq1$. It can therefore be treated as one additional constant head.

If the uniform error is at most $\varepsilon$, then

$$ 1-\varepsilon\leq S(p)\leq\left(\frac r{r-1}+\frac s{s-1}\right)\varepsilon\leq4\varepsilon. $$

Thus $\varepsilon\geq1/5$. `NonnegativeHeadCone.approximation_error_ge` kernel-checks this finite two-orientation summation and error argument. The passage from actual cube neighbors to its finite arrays is the displayed written instantiation.

## A failed nonnegative product compiler

The obstruction already applies to products of two heads with the same positive orientation. On four bits put

$$ t=x_1+x_2,\qquad z=x_3+x_4,\qquad \phi_i(x)=\frac{\varepsilon x_i}{\varepsilon+z+\eta t}\quad(i=1,2). $$

For $\varepsilon,\eta\gt0$ these are genuine admissible heads with all denominator slopes strictly positive. Both are nonnegative and have full-cube norm at most one. As $\varepsilon\to0$ and $\eta/\varepsilon\to0$, their product converges uniformly to $\mathbf1_{1100}$.

Consequently no compiler can approximate every such product arbitrarily well using a sum of nonnegative original heads. This is impossible even with unlimited head count and unlimited amplitude. In particular, a positive integral or Bernstein expansion that treats arbitrary affine numerator products as staying inside the nonnegative original-head cone cannot work. Products of constant-residue reciprocal kernels constitute a narrower class and are not excluded by this example.

## Relation to zero-cost upper-budget additions

For an added score $T=b+\sum_h\phi_h$, let $u_h=\max_x\phi_h(x)$ and define its upper interval contribution

$$ U=b+\sum_hu_h. $$

Redistributing constants gives

$$ T=U-\sum_h(u_h-\phi_h). $$

Every $u_h-\phi_h$ is a nonnegative admissible head: only its affine numerator changes. Thus an added score with $U=0$ is the negative of a nonnegative-head sum. Such an addition cannot approximate $-\mathbf1_p$ below error $1/5$ at a vertex with at least two literals of each sign.

This observation addresses a proposed cost-free product addition while existing heads and their extrema are fixed. It does not exclude coordinated changes to existing heads, which might lower their upper contribution and compensate for a positive cost in the new terms. It also does not assert that the complete interval amplitude remains unchanged merely because one branch contribution is zero; the other branch must still be checked.

## Verification and scope

The affine-ratio corner inequality and the finite cone error theorem are kernel checked in `formalization/HeadComplexity/Research/NonnegativeHeadCone.lean`. The original-head specialization, same-orientation product example, and interval-budget interpretation are written proofs. An independent agent audited the affine identity, denominator inequality, orientation summation, and nonnegative-bias treatment. No original definitions are changed. The unrestricted lower-bound target remains open because unrestricted scores permit signed cancellation, and a truth-table-preserving joint repair may use it.

`lake build HeadComplexity.Research.NonnegativeHeadCone` completed successfully with 3843 jobs. All three theorem declarations in `NonnegativeHeadConeAudit.lean` have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. The GitHub render audit recognized all 34 mathematical spans.
