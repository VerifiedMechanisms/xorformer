# A bootstrap of the unrestricted weighted lower bound

## Strongest unconditional statement

The original definition of `HeadComplexity.worstCaseHeadComplexity` is unchanged. Write $W(n)$ for it and $N=2^n$. The new theorem gives

$$ W(n)\geq\frac{N-1}{n(n+7)}\qquad(n\geq256). $$

Its implementation is `HeadComplexity.BootstrapWeightedCounting.worstCase_real_lower` in `formalization/HeadComplexity/Research/BootstrapWeightedCounting.lean`. The public alias is `HeadComplexity.bootstrap_weighted_counting_worst_case_lower_bound` in `formalization/HeadComplexity/Results/All.lean`.

A more precise estimate holds already for $n\geq8$. Define

$$ B_1(n)=\frac{16e^2N^2(n+8)}{n(N-1)}. $$

Then

$$ W(n)\geq\frac{(N-1)\log2}{n\log B_1(n)}. $$

This is `HeadComplexity.BootstrapWeightedCounting.worstCase_real_log_lower`, publicly aliased as `HeadComplexity.bootstrap_weighted_counting_worst_case_log_lower_bound`.

The lower bound still has order $N/n^2$. Neither a positive power saving nor the requested logarithmic fallback follows. In particular, this does not refute the original conjecture.

## Proof

The already proved unrestricted weighted count gives, at the original worst-case width, an entropy inequality with base at most

$$ \frac{16e^2N^2}{n^2W(n)}. $$

The preceding unconditional theorem says $W(n)\geq(N-1)/(n(n+8))$. Substituting this lower bound into the denominator gives the explicit upper bound $B_1(n)$ for the entropy base. The original entropy theorem handles both the Warren parameter range and its complementary case, so no width-range assumption is added here. Dividing its inequality by $n\log B_1(n)$ gives the logarithmic statement.

For $n\geq256$, use $N\geq256$ and $e\leq11/4$ to obtain

$$ B_1(n)=N\cdot16e^2\cdot\frac{n+8}{n}\cdot\frac{N}{N-1}\leq N\cdot121\cdot\frac{33}{32}\cdot\frac{256}{255}\leq128N. $$

Consequently $\log B_1(n)\leq(n+7)\log2$, proving the simple form. All these finite steps are kernel checked.

The logarithmic denominator has the written asymptotic expansion

$$ n\log B_1(n)/\log2=n^2+(4+2/\log2)n+O(1). $$

This is a finite-constant refinement of the same counting method. The separate kernel-checked `WeightedCountBarrier` module shows that every positive block-weight certificate of this form exceeds $2^N$ once $n^2H\geq2N$, $n\geq4$, $H\geq2$, and $2nH\leq N$. Further changes of these block weights cannot yield either requested gain.

## Verification

`bootstrap-weighted-build.txt` records the full `lake build`. `bootstrap-weighted-axioms.txt` records the transitive checks of all seven new theorems and both public aliases. Their only axioms are `propext`, `Classical.choice`, and `Quot.sound`. No definition of the original model, admissibility, computability, or worst-case head complexity was changed.
