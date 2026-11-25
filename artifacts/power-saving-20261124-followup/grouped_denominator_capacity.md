# Capacity of grouped denominator statistics

## Statement and scope

This extends the shared-statistics count to several independently chosen groups. It is a kernel-checked restricted capacity theorem, not an unrestricted representation theorem. The original definitions of heads and worst-case complexity are unchanged.

Write $N=2^n$. After dividing each denominator by its value at the zero vertex, suppose its slope vector has the form

$$ B_h(x)=1+U_{g(h),0}(x)+\sum_{j=1}^r v_{hj}U_{g(h),j}(x),\qquad U_{gj}(x)=\sum_{i=1}^n u_{gji}x_i,\qquad g(h)\in\lbrace1,\ldots,G\rbrace. $$

The assignment $g$, all statistics, all coefficients, every affine numerator, and the bias may depend on the target table. Actual original denominators must remain positive and admissible. The counted polynomial comparison class is larger and need not satisfy positivity. There is no restriction on signed cancellation within or between groups.

Put

$$ q=rH+n(r+1)G,\qquad p=nH+q,\qquad D=2H+k-2. $$

For $n,H\geq1$, $k\geq2$, and $p\leq N$, the number of represented strict truth tables is at most

$$ 2G^H\frac{(4eDN/p)^p}{k^{nH}}. $$

For a fixed assignment, the factor $G^H$ is omitted. Taking $k=2H$ gives

$$ \log T\leq\log2+H\log G+q\log(16eN/n)+nH\log(8eN/(nH)). $$

The formula with logarithms assumes $G\geq1$. When $G=0$ and $H\geq1$, the represented class is empty.

## Finite half-table estimates

For every $n\geq32$, suppose

$$ \log(n+1)\leq t\leq n,\qquad q\leq2tH,\qquad 1\leq H\leq\frac{N}{400nt},\qquad G\leq N. $$

Then

$$ T\leq\exp(8N/25)\leq2^{N/2}. $$

In particular, the two requested scales work with $t=\sqrt n$ and $t=n/\log n$. Their respective width constants are $1/400$. These are margin-free counts under the explicit grouped-statistics hypothesis.

For affine pencils, $r=1$, the parameter condition reads $H+2nG\leq2tH$. Thus the number of independently chosen pencils can be proportional to $H/\sqrt n$ at the aimed scale, or to $H/\log n$ at the fallback scale. A generic independent denominator family can require $G$ of order $H$, so this does not cover all original representations.

## Proof

Normalize the entire score at the zero vertex. Its nonzero value determines one of two fixed bias signs, and each normalized numerator has zero constant term. This is the same exact normalization used in the unrestricted weighted count. It leaves $nH$ arbitrary real numerator parameters.

For a fixed assignment, there are $q$ denominator parameters. Give each numerator parameter weight $k$ and every denominator parameter weight one. Every denominator has weighted degree at most two. Clear the product of all denominators once for the entire score. The weighted degree is at most $2H+k-2$, and the product of parameter weights is $k^{nH}$. The weighted Warren theorem yields the finite formula. Union over all $G^H$ assignments.

Clearing different groups separately and then adding their cleared scores would change cancellations. The proof never makes that operation.

For $k=2H$, the ordinary numerator contribution after dividing by its weights is the sparse entropy term $nH\log(8eN/(nH))$. The denominator contribution is at most $q\log(16eN/n)$. Under the finite budget above, the checked estimates are

$$ nH\log(8eN/(nH))\leq7N/25,\qquad q\log(16eN/n)\leq N/100,\qquad \log2\leq N/100. $$

The assignment count satisfies $G^H\leq\exp(N/50)$ because $\log G\leq n$ and $H\leq N/(400nt)$ with $t\geq1$. These four costs sum to $8N/25$. Finally $16/25\leq\log2$ gives the half-table exponent.

## Exact remaining access lemma

Let $K$ be a comparable width satisfying the same budget, and put $\gamma=\exp(-\exp t)$. The existing high-margin theorem counts at most $2^{N/2}$ tables at width $K$ and margin at least $\gamma$.

It would suffice to prove that every table representable with $H_0$ original heads, for which every width $K$ original representation has relative margin below $\gamma$, belongs to the grouped comparison class at width $K$. The two counted classes would then cover all width $H_0$ tables and have total size at most $2\cdot2^{N/2}\lt2^N$. The conditional conclusion is $H_0\lt W(n)$.

The quantifier is over every comparable-width representation of each table. A single high-dimensional or ill-conditioned representation does not establish failure of this access lemma. Conversely, no argument here establishes the access lemma. It is now a broader possible replacement for either uniform margin repair or one globally shared low-rank denominator factorization.

If $K=\lceil CH_0\rceil+B$, with fixed $C\geq1$ and $B\geq0$, the width budget follows from $H_0\leq N/(800Cnt)$ and $800(B+1)n^2\leq N$. The latter inequality holds eventually, since $t\leq n$. This tracks the constant and additive overhead without using rescaling to change relative margin.

## Kernel-checked declarations

- `LowParameterDenominatorCapacity.card_represented_le` proves the fixed-chart finite weighted formula for any denominator polynomials with the stated degree bound.
- `LowParameterDenominatorCapacity.card_represented_le_exp` isolates the denominator-parameter entropy.
- `LowParameterDenominatorCapacity.card_chart_union_le_exp` includes the number of target-dependent charts.
- `GroupedDenominatorCapacity.mem_represented_of_original` is the exact inclusion from admissible original heads with the displayed normalized slope factorization.
- `GroupedDenominatorCapacity.card_represented_le_half_tables`, `card_represented_sqrt_scale`, and `card_represented_logarithmic_scale` prove the finite counts.
- `GroupedDenominatorCapacity.worstCase_gt_of_low_margin_grouped_statistics` proves the conditional conclusion against the original `worstCaseHeadComplexity` definition.

The finite formula after summing assignments, the displayed specialization to pencils, and the final ceiling-overhead calculation are written consequences of these declarations. The unrestricted access statement remains a conjectural missing lemma.
