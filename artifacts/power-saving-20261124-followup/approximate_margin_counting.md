# Approximate margin repair suffices for unrestricted counting

## Kernel-checked conditional theorem

Let $N=2^n$, with $n\geq4$. Suppose at most $2^{N/2}$ truth tables have an original-model representation at width $K$ and relative margin at least $\gamma$. Suppose also that every truth table representable at width $H$ agrees on at least $15N/16$ inputs with one of these high-margin tables. Then

$$ H\lt W(n). $$

The approximation is of the entire truth table under the uniform measure on the Boolean cube. The high-margin center must have a genuine admissible representation at width $K$, and its margin uses the full-cube head norms. Neither the input distribution nor the denominator norm is changed.

The theorem is `HeadComplexity.ApproximateMarginCounting.worstCase_gt_of_approximate_repair` in `formalization/HeadComplexity/Research/ApproximateMarginCounting.lean`. The approximation premise is the explicitly defined proposition `HasApproximateMarginRepair`. It has not been established for unrestricted xorformers.

## Hamming-ball calculation

For a fixed Boolean table $g$, assign a table $f$ the integer weight $4^{N-d(f,g)}$, where $d$ is Hamming distance. Summing independently at each input gives

$$ \sum_f4^{N-d(f,g)}=5^N. $$

Consequently a Hamming ball of radius $r$ satisfies

$$ |B(g,r)|4^{N-r}\leq5^N. $$

Set $N=16m$ and $r=m$. The finite integer inequality $5^{16}\lt2^{38}$ implies

$$ |B(g,m)|4^{15m}\leq5^{16m}\lt2^{38m}=2^{8m}4^{15m},\qquad |B(g,m)|\lt2^{8m}. $$

At most $2^{8m}$ such balls therefore contain strictly fewer than $2^{16m}$ truth tables. The represented class is contained in this union under the approximate-repair hypothesis. A missing table has original head complexity greater than $H$, proving the claim.

The cardinality statements are `card_hammingBall_weighted`, `card_hammingBall_lt_half`, and `card_nearbyTables_lt`. They do not rely on an asymptotic entropy estimate.

## The two audited margin scales

For $n\geq32$, $C\geq1$, and a nonnegative integer additive overhead $B$, assume

$$ 500(B+1)n^2\leq2^n,\qquad K=\lceil CH\rceil+B. $$

The previously checked finite margin count gives both of the following implications, now also with the weaker approximate-repair premise:

$$ \begin{aligned} H&\leq\frac{2^n}{100Cn\sqrt n},&\gamma&=\exp(-\exp(\sqrt n));\cr H&\leq\frac{2^n\log n}{100Cn^2},&\gamma&=\exp(-\exp(n/\log n)).\end{aligned} $$

For either row, approximate repair at width $K$ with at most $2^{n-4}$ errors implies $H\lt W(n)$. The declarations are `worstCase_gt_sqrt_of_approximate_repair` and `worstCase_gt_logarithmic_of_approximate_repair`. Their real-valued floor-width consequences are `real_sqrt_bound_of_approximate_repair` and `real_logarithmic_bound_of_approximate_repair`.

These are conditional statements. This checkpoint proves neither target lower bound unconditionally. All original model definitions remain unchanged.

## A weaker prospective repair target

The choice $15/16$ is convenient for exact integer arithmetic. A fixed advantage over random agreement would also suffice if the high-margin counting constant were reduced enough. More generally, a possible research target is a repair with width overhead $n^a$, advantage $n^{-b}$ over one-half agreement, and margin $\exp(-n^{O(1)})$. The finite margin count would then have exponent $O(n^{a+1}H\log n)$, while the Hamming-ball deficit is of order $Nn^{-2b}$. At width $H=N/n^{2-\delta}$, this comparison would give a fixed power saving whenever

$$ a+2b+\delta\lt1. $$

This last paragraph is an asymptotic written reduction, not a Lean theorem or an established repair construction. It identifies a less demanding sufficient condition than exact constant-overhead repair.

## Verification

The module build succeeds. The eight audited declarations depend transitively only on `propext`, `Classical.choice`, and `Quot.sound`. The exact audit input and output are `ApproximateMarginAudit.lean` and `approximate-margin-counting-axioms.txt` in this directory.
