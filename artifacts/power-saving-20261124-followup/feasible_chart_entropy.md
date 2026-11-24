# The Exact Missing Feasible-Chart Entropy Bound

## Kernel-checked reduction

Write $N=2^n$ and $L=nH+1$. The original unrestricted head class is covered by active-basis certificates consisting of an unordered set of $L$ sample or coefficient-box rows and their selected labels. The number of certificates is at most

$$ \binom{N+2L}{L}2^L\leq\exp\left(L\log\frac{2e(N+2L)}{L}\right). $$

The new file `formalization/HeadComplexity/Research/FeasibleChartEntropy.lean` proves this estimate and the following exact finite implication. Suppose $n\geq32$, $\log(n+1)\leq t\leq n$, and

$$ L\leq\frac{N}{25t}. $$

If every globally feasible chart has at most $\exp(Lt)$ full truth-table extensions, the entire original width $H$ class has at most

$$ \exp(8N/25)\lt2^{N/2} $$

truth tables. The Lean theorem proves the exponential bound and uses the weaker consequence that it is strictly less than $2^N$. The strict half-table comparison follows directly from $8/25\lt(\log2)/2$.

The conclusion $H\lt W(n)$ is kernel checked as `HeadComplexity.FeasibleChartEntropy.worstCase_gt_of_chart_entropy`. Its square-root and logarithmic specializations retain the chart-cardinality premise explicitly. Setting $t=\sqrt n$ gives the aimed scale; setting $t=n/\log n$ gives the fallback scale. This is a conditional reduction, not either requested unconditional theorem.

## Retaining coherent original denominators

The general affine chart permits every affine denominator positive on the cube. The original model has the stronger restriction that all nonconstant slopes in each denominator have one common sign. The file `formalization/HeadComplexity/Research/CoherentDenominatorCharts.lean` retains this restriction in the count.

For an original head, the slope in coordinate $i$ is exactly $\rho_i(\alpha-1)$, and the constant coefficient is positive. After normalization, encode each slope as $\sigma u_i^2$, where $\sigma\in\lbrace-1,+1\rbrace$ is common to that head. This gives the polynomial chart

$$ B_h(x)=1+\sigma_h\sum_i u_{hi}^2x_i. $$

Only parameter choices with $B_h(x)\gt0$ everywhere enter the feasible extension set. Zero slopes are allowed in this upper-count comparison class; the original heads embed in it without changing their scores or labels. This is not a claim that every point of the comparison class is an original head.

For each active certificate $c$, let $\mathcal F_c$ be the union over all coherent head orientations of its feasible extension tables. Feasibility includes the actual nonsingular basis, its Cramer solution, the coefficient box, and every full-cube unit-gap inequality. The exact missing inequality is

$$ \lvert\mathcal F_c\rvert\leq\exp\bigl((nH+1)t\bigr)\qquad\text{for every certificate }c. $$

The orientation union is already inside $\mathcal F_c$, so it must not be omitted when proving this hypothesis. The declaration `HeadComplexity.CoherentDenominatorCharts.worstCase_gt_of_chart_entropy` converts this hypothesis into $H\lt W(n)$. The declarations ending in `of_sqrt_chart_entropy` and `of_logarithmic_chart_entropy` specialize it to the two target scales.

## What is proved and what remains open

The certificate count, original-model embedding, global-feasibility cover, and conditional implications are kernel checked. The combined target build passed with 4035 jobs. Fifteen audited exported declarations have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. No original model or worst-case-complexity definition was changed.

The extension bound is open. The fixed-basis counterexamples already committed in this run disprove uniqueness, even with full-cube feasibility and coherent positive denominators. They do not disprove the displayed entropy bound. A later exact count shows that the generic seven-variable counterexample has precisely two extensions. The denominator-balanced one-head packing argument gives a written bound of $n^{O(n)}$ per actual basis, but its balance assumption has not been removed and it has not been extended to arbitrarily canceling sums of heads.
