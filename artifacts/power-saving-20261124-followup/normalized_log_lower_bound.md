# Exact logarithmic form of the unrestricted counting bound

## Statement

Write $N=2^n$ and let $W(n)$ be the original `HeadComplexity.worstCaseHeadComplexity`. For every integer $n\geq8$,

$$ W(n)\geq\frac{(N-1)\log 2}{2n\log(2eN/n)}=\frac{N-1}{2n\bigl(n-\log_2 n+\log_2(2e)\bigr)}. $$

This is an unconditional kernel-checked consequence of exact score normalization and the imported, audited Warren theorem. It allows target-dependent denominators, arbitrary real coefficients, and arbitrary signed cancellation. The original model definitions are unchanged.

The declaration is `HeadComplexity.NormalizedLogCounting.worstCase_real_log_lower` in `formalization/HeadComplexity/Research/NormalizedLogCounting.lean`. The public alias is `HeadComplexity.normalized_counting_worst_case_log_lower_bound` in `Results/All.lean`.

This bound is slightly stronger than $(N-1)/(2n^2)$ for $n\geq8$. It is still of order $N/n^2$. The logarithm in its exact denominator is not the requested multiplicative $\log n$ improvement.

## Proof

Let $H=W(n)$. Every Boolean table is representable at width $H$, by the definition of the maximum and zero-head padding. The declaration `card_at_worstCase` checks this equality of cardinalities:

$$ |\mathcal F_{n,H}|=2^N. $$

Set $A=2eN/n$. Since $N\geq n\geq8$, one has $A\geq2$ and $\log A\geq\log2\gt0$.

If $2nH\leq N$, exact normalized counting gives $2^N\leq2A^{2nH}$. Taking natural logarithms proves

$$ (N-1)\log2\leq2nH\log A. $$

If instead $2nH\gt N$, the same inequality follows from $\log A\geq\log2\gt0$. In both cases divide by $2n\log A\gt0$. The intermediate declaration is `entropy_at_worstCase`.

Finally, $\log(2eN/n)=(n+1)\log2+1-\log n$, giving the displayed base-two form. Since $2e\lt6\leq n$, its denominator is at most $2n^2\log2$. This verifies the comparison to the earlier finite bound. $\blacksquare$

## Verification boundary

The first displayed inequality, the full cardinality at worst-case width, and its entropy proof are kernel checked. The algebraic base-two restatement and asymptotic comparison are written consequences. No new axiom, coefficient restriction, or margin premise was introduced.
