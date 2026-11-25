# Shared denominator statistics and a rank-or-margin alternative

## Status

The finite count below is kernel checked in `formalization/HeadComplexity/Research/SharedStatisticsCapacity.lean`. It applies to an explicitly restricted denominator class, with arbitrary real numerators and signed cancellation. The original model and `HeadComplexity.worstCaseHeadComplexity` are unchanged.

The unrestricted rank-or-margin alternative in the last section is an unproved structural premise. Its implication for the original worst-case complexity is formalized, but the premise is not asserted.

## The shared-statistics chart

Write $N=2^n$. Normalize a strict score at the zero input using `NormalizedCounting`: its bias is $s\in\lbrace-1,1\rbrace$, each denominator has constant coefficient one, and each numerator has constant coefficient zero. This operation preserves every label, uses the same number of heads, and imposes no margin hypothesis.

Suppose the normalized denominator slopes factor through $r$ shared linear statistics:

$$ B_h(x)=1+\sum_{j=1}^r v_{hj}L_j(x),\qquad L_j(x)=\sum_{i=1}^n u_{ji}x_i,\qquad A_h(x)=\sum_{i=1}^n a_{hi}x_i. $$

All $a_{hi}$, $v_{hj}$, and $u_{ji}$ are arbitrary real parameters and may depend on the target truth table. In the original-model bridge every $B_h$ is positive on the entire cube. The upper-counting class enlarges the parameter domain after denominator clearing.

This factorization differs from a bound on the number of denominator values. One nonconstant linear statistic may take $N$ distinct values. The condition here controls the dimension of the shared linear span.

The chart has $p=nH+rH+nr$ parameters. Give each numerator parameter weight $k\geq2$ and every other parameter weight one. Each denominator has weighted degree two. The cleared polynomial

$$ P_s(x)=s\prod_h B_h(x)+\sum_h A_h(x)\prod_{g\neq h}B_g(x) $$

therefore has weighted degree at most $D=2H+k-2$. The product of variable weights is $k^{nH}$.

For $n,H\geq1$ and $p\leq N$, the formal finite theorem `card_represented_le` gives

$$ T(n,H,r)\leq 2\left(\frac{4eDN}{p}\right)^p k^{-nH}. $$

The factor two accounts for the normalized bias. The original admissible-atom bridge is `mem_represented_of_original`. It requires precisely the displayed slope factorization and a strict full-cube score certificate, with no coefficient-height or margin assumption.

## Separating numerator and denominator costs

Set $k=2H$. Since $D\leq4H$ and $p\geq nH$, define $B=16eN/n$ and obtain

$$ \begin{aligned} \log T(n,H,r)&\leq\log2+p\log B-nH\log(2H)\cr &=\log2+(rH+nr)\log\left(\frac{16eN}{n}\right)+nH\log\left(\frac{8eN}{nH}\right). \end{aligned} $$

This is `card_represented_le_exp`. The numerator dimension appears in the last sparse-entropy term. The head-count degree is charged to the denominator-factor parameters.

Assume

$$ n\geq32,\qquad \log(n+1)\leq t\leq n,\qquad r\leq t,\qquad n\leq H\leq\frac{N}{200nt}. $$

The proof uses three explicit estimates:

$$ \log2\leq\frac{N}{50},\qquad (rH+nr)\log\left(\frac{16eN}{n}\right)\leq\frac{N}{50},\qquad nH\log\left(\frac{8eN}{nH}\right)\leq\frac{7N}{25}. $$

For the middle estimate, $rH+nr\leq2tH$ and $\log(16eN/n)\leq2n$. For the final estimate, apply the already formal finite entropy lemma with parameter count $nH$, polynomial degree two, and zero chart cost. All its positivity and dimension hypotheses are checked.

Consequently `card_represented_le_exp_at_budget` and `card_represented_le_half_tables` prove

$$ T(n,H,r)\leq\exp(8N/25)\leq2^{N/2}. $$

The two requested scales are explicit corollaries:

- `card_represented_sqrt_scale`: $r\leq\sqrt n$ and $n\leq H\leq N/(200n^{3/2})$.

- `card_represented_logarithmic_scale`: $r\leq n/\log n$ and $n\leq H\leq N\log n/(200n^2)$.

Both count all such representations regardless of their margin.

## The missing unrestricted alternative

The high-margin count and the shared-statistics count can be combined without assuming a common good representation. The following sufficient premise is deliberately stated over truth tables.

> Every truth table representable with $H$ original heads has, at a comparable width $K$, either a representation with relative margin at least $\exp(-\exp t)$, or a strict representation whose normalized denominator slopes factor through at most $r\leq t$ shared statistics.

Here the relative margin uses the original full-cube norm $|b|+\sum_h\|\phi_h\|_\infty$. In either alternative the representation may change all heads. The theorem does not infer anything from a poorly conditioned supplied representation.

If $n\leq K\leq N/(200nt)$, each alternative contributes at most $2^{N/2}$ truth tables. Their union has at most $2^{N/2+1}\lt2^N$ tables. The declaration `worstCase_gt_of_rank_or_margin` proves $H\lt W(n)$ from the corresponding set-cover premise. Its low-statistic side is actually allowed to use the enlarged cleared-polynomial chart, so an admissible-head alternative is sufficient.

For a fixed multiplicative overhead $K=\lceil CH\rceil+B$, one may take $H\leq N/(400Cnt)$ and absorb the ceiling and fixed $B$ for all sufficiently large $n$. Thus a proof of this alternative at $t=\sqrt n$ would give the requested benchmark. The choice $t=n/\log n$ would give the logarithmic fallback.

No rank-or-margin alternative is established here. Full-rank denominator matrices can occur in exact zero-score identities and in representations of trivial labels, so the rank of one supplied representation cannot disprove the truth-table premise. A successful argument must either find a new comparable-width representation or count all targets that admit neither alternative.
