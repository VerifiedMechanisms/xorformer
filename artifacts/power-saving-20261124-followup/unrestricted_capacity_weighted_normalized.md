# Weighted counting for the original unrestricted model

## Statement

Write $N=2^n$ and let $W(n)$ denote the original `HeadComplexity.worstCaseHeadComplexity`. For every integer $n\geq8$,

$$ W(n)\geq\frac{(N-1)\log 2}{n\log(32e^2N^2/(N-1))}\geq\frac{N-1}{n(n+8)}. $$

Both inequalities against $W(n)$ are kernel checked separately in `HeadComplexity.WeightedNormalizedCounting.worstCase_real_log_lower` and `HeadComplexity.WeightedNormalizedCounting.worstCase_real_lower`, in `formalization/HeadComplexity/Research/WeightedNormalizedCounting.lean`. The logarithmic bound has asymptotic leading constant one in front of $N/n^2$, twice the leading constant of the earlier unweighted count. It does not prove any fixed power gain or the requested multiplicative $\log n$ gain.

Every original admissible head is included. Denominators may depend on the target, coefficients are arbitrary real numbers, and signed cancellation is unrestricted. No margin hypothesis is used, no head is added, and no original definition is changed.

## Exact finite capacity bound

Let $\mathcal F_{n,H}$ be the truth tables computable by $H$ original heads. Suppose $n,H,k\geq1$ and $2nH\leq N$. Then

$$ |\mathcal F_{n,H}|\leq\frac{2}{k^{nH}}\left(\frac{4e(H+k-1)N}{2nH}\right)^{2nH}. $$

This is `card_le_weighted`. Its factor two accounts for the two possible signs of the normalized score at the zero vertex. It is not a width overhead.

For $H\geq2$, choosing $k=H-1$ gives the sharper declaration `card_le_optimal`:

$$ |\mathcal F_{n,H}|\leq2\left(\frac{16e^2N^2(H-1)}{n^2H^2}\right)^{nH}. $$

Among positive real uniform numerator weights, this choice minimizes $(H+k-1)^2/k$, since

$$ \frac{(H+k-1)^2}{k}=4(H-1)+\frac{(k-(H-1))^2}{k}. $$

The optimality identity is a written algebraic observation; the finite bound at the integer choice $H-1$ is kernel checked. The convenient bound `card_le`, valid also for $H=1$, is

$$ |\mathcal F_{n,H}|\leq2\left(\frac{16e^2N^2}{n^2H}\right)^{nH}. $$

## Proof of the weighted count

The existing exact zero-input normalization represents every strict original score, with unchanged width, in one of the two forms

$$ S(x)=s+\sum_{h=1}^H\frac{u_h\cdot x}{1+v_h\cdot x},\qquad s\in\lbrace-1,+1\rbrace. $$

All denominators remain strictly positive on the full Boolean cube. The polynomial chart may enlarge the allowed denominator parameter set for counting, which is harmless for this upper bound. The normalization and original-model embedding are the previously checked declarations in `NormalizedCounting.lean`.

There are $nH$ numerator and $nH$ denominator parameters. Give every numerator parameter weight $k$ and every denominator parameter weight one. After multiplying by the product of the positive denominators, the bias term has weighted degree at most $H$, and each numerator term has weighted degree at most $k+H-1$. Since $k\geq1$, the whole cleared score has weighted degree at most $H+k-1$. The product of all parameter weights is exactly $k^{nH}$.

Apply the kernel-checked weighted Warren theorem to each bias sign, with $p=2nH$ parameters and $N$ strict sign queries. Its parameter-dimension hypothesis is exactly $2nH\leq N$, and every weight is positive and at most the degree bound. Adding the two resulting counts proves the displayed finite formula. The declarations `clearedPoly_weighted` and `product_parameter_weights` verify the weighted-degree and weight-product calculations.

## Consequence for the worst-case width

Set $H=W(n)$. The existing declaration `NormalizedLogCounting.card_at_worstCase` states that all $2^N$ truth tables occur at this width. If $2nH\leq N$, the simplified capacity bound therefore gives

$$ (N-1)\log2\leq nH\log\left(\frac{16e^2N^2}{n^2H}\right). $$

The earlier unconditional lower bound $H\geq(N-1)/(2n^2)$ makes the logarithm's argument at most

$$ B=\frac{32e^2N^2}{N-1}. $$

Thus $(N-1)\log2\leq nH\log B$. If instead $2nH\gt N$, this same inequality follows from $B\geq4$. This second case is necessary: Warren's parameter-dimension hypothesis cannot simply be assumed at the worst-case width. The declaration `entropy_at_worstCase_of_base` handles both cases.

For $n\geq8$, the kernel checks $4\leq B\leq2^{n+8}$, using $N\geq256$ and $e\leq11/4$. Division by the positive logarithmic denominator gives the two stated lower bounds. $\blacksquare$

## Remaining obstruction

At $H\asymp N/n^{3/2}$, the simplified count has logarithm of order $n^2H$, which is larger than $N$. At $H\asymp N\log n/n^2$, it still has logarithm of order $N\log n$. The weighted theorem removes one of the two old leading parameter contributions but retains the denominator-parameter cost $nH\log H$.

A power or logarithmic improvement still needs a model-specific reduction of this residual denominator entropy, such as a bound on globally feasible coherent active-basis charts, a proved comparable-width margin repair, or a new unrestricted counting argument. The weighted count by itself does not justify any such reduction.

## Verification

The fifteen theorem declarations in this file are listed in `WeightedNormalizedAudit.lean`. Their transitive axiom output is in `weighted-normalized-axioms.txt`; the successful module build is in `weighted-normalized-build.txt`. All audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The exact finite capacity bounds and both stated lower bounds are kernel checked. The asymptotic descriptions and the comparison of leading constants are written consequences.
