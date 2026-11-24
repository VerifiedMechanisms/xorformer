# Stronger margins can pay for growing head overhead

## Exact finite implication

This is a conditional theorem, not a margin repair. Its purpose is to keep a broader access route available after constant-overhead constructions fail. The original unrestricted model and the full-cube relative margin are unchanged.

Write $N=2^n$. Let $n\geq32$, $C\geq1$, and let $B$ be a nonnegative integer such that $500(B+1)n^2\leq N$. At every integer width satisfying

$$ H\leq\frac{N}{100Cn\log(n+1)}, $$

at most $2^{N/2}$ truth tables have a representation with at most $\lceil CH\rceil+B$ heads and relative margin at least $\exp(-(n+1))$. The factor $C$ is allowed to depend on $n$.

**Proof.** In the finite margin estimate set $t=\log(n+1)$. Then $\exp(-\exp t)=\exp(-(n+1))$, and the required parameter interval holds because $\log(n+1)\leq n$. Apply `MarginCapacityEstimates.card_highMargin_test_with_overhead`, including its ceiling allowance. This is kernel checked as `SublinearOverheadRepairTradeoff.card_highMargin_linear_exponent_overhead`. $\blacksquare$

Consequently, if every width $H$ original truth table has such a repaired representation, then $H\lt W(n)$. The same conclusion holds if the class of width $H$ truth tables for which **every** comparison-width representation has smaller margin has cardinality at most $2^{N/2}$. These exact alternatives are `worstCase_gt_of_linear_exponent_repair` and `worstCase_gt_of_linear_exponent_low_count`.

## A power-saving access target

For example, a repair using at most $\lceil\sqrt n H\rceil$ heads and margin at least $\exp(-(n+1))$ would imply

$$ H\lt W(n)\qquad\text{whenever}\qquad H\leq\frac{N}{100n^{3/2}\log(n+1)}. $$

This implication is kernel checked as `worstCase_gt_of_sqrt_overhead_repair`. With the repair hypothesis at every sufficiently large dimension, taking the natural floor would give a real lower bound of that order. Since $\log(n+1)=o(n^\varepsilon)$ for every fixed $\varepsilon\gt0$, this would give any fixed power saving smaller than one half. The asymptotic conversion in this paragraph is written mathematics; no repair hypothesis has been established.

More generally an overhead $C(n)=O(n^a)$ with fixed $a\lt1$ and this singly exponential margin would yield a lower bound of order $N/(n^{1+a}\log n)$. A polynomial in $n$ inside the negative margin exponent changes constants in the same entropy calculation. These tradeoffs do not follow from the universal interpolation upper bound: that upper bound is not proportional to the width of the supplied representation.

## Verification and remaining gap

The six declarations are in `formalization/HeadComplexity/Research/SublinearOverheadRepairTradeoff.lean`. The build and exact transitive axiom outputs are recorded in `sublinear-overhead-build.txt` and `sublinear-overhead-axioms.txt`. They depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The new first failing lemma is explicit: a width-sensitive, truth-table-preserving repair with a sublinear power of $n$ overhead and singly exponential relative margin. Rescaling a poorly conditioned score does not provide it. Replacing the entire target with a universal construction can use too many heads. Low-rank polynomial rounding can lose rank, while clearing all denominators produces a polynomial whose low-rank decomposition is not controlled after rounding. No such bridge is asserted here.
