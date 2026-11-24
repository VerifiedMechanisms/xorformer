# Finite smoothable-cluster entropy estimates

## Kernel-checked statement

The file `formalization/HeadComplexity/Research/SplitSmoothableEstimates.lean` proves finite counts for the strict class from `SplitSmoothableCapacity.lean`. These are counts of an explicitly defined class, not an access theorem for the original model.

Write $Q=q+1$, $K=GQ$, $d=n+1$, and $N=2^n$, with $G\geq 1$. The parameter count is

$$ p=1+2dK+GQ^2. $$

For every assignment of positive filtration orders $1\leq k_{g,i}\leq q$, `card_smoothableFunctions_le_coarse` proves

$$ \lvert\mathcal{S}_{n,G,q,k}\rvert\leq\left(\frac{4e(3+2Q)N}{p}\right)^p Q^{2dK}K^{dG+GQ^2}. $$

The only size hypothesis is $p\leq N$. The count includes arbitrary real numerator coefficients and signed cancellation. The underlying definition requires positive base denominators and strict signs on the full Boolean cube. It also requires membership in the real topological closure of the split-algebra orbit, with the fixed filtration mask used by the score formula.

The proof lower-bounds the product of parameter weights by

$$ K G^{G(2q+1)d}. $$

The common power of $G$ cancels before any logarithmic estimate. All filtration-order assignments are then unioned explicitly. There are $q^{Gq}\leq Q^{Gq}$ such assignments, including the empty-order case $q=0$. No uncharged choice remains in this union.

Define the resulting entropy by

$$ E=p\log\left(\frac{4e(3+2Q)N}{p}\right)+2dK\log Q+(dG+GQ^2)\log K+Gq\log Q. $$

The declaration `unionEntropy_at_budget` proves, for $n\geq 32$,

$$ \log(n+1)\leq t\leq n,\qquad n\leq Qt,\qquad Q\leq t,\qquad K\leq\frac{N}{1000nt}\quad\Longrightarrow\quad E\leq\frac{8N}{25}. $$

The main logarithmic term costs at most $7N/25$. The remaining three terms together cost at most $8N/1000$. This is below $8N/25$ and hence below $(N/2)\log 2$. The parameter-count hypothesis is derived from the same budget.

## Both requested scales

The integer cluster sizes and constants are explicit. The following two declarations prove that at most $2^{N/2}$ truth tables belong to the union over every order assignment:

- `card_smoothableUnion_sqrt_scale`: $q=\lfloor\sqrt n\rfloor$ and $K\leq N/(2000n\sqrt n)$.
- `card_smoothableUnion_logarithmic_scale`: $q=\lfloor\log n\rfloor$ and $K\leq N\log n/(2000n^2)$.

Both hold for every $n\geq 32$. The proof uses $t=2\sqrt n$ and $t=2n/\log n$, respectively. The factor two pays for the integer cluster size. These values of $t$ are internal entropy parameters, not replacements for the test margins in the separate high-margin theorem.

## Exact missing access statement

`HasSmoothableAccess n H G q` is the inclusion of every original width $H$ truth table in this explicitly counted union. `worstCase_gt_of_smoothable_access` derives $H\lt W(n)$ from that inclusion and the entropy budget. The inclusion is not proved.

There is also a weaker sufficient premise. `worstCase_gt_of_lowMargin_access` requires only

$$ \mathcal{L}_{n,H,H',\gamma}\subseteq\bigcup_k\mathcal{S}_{n,G,q,k}, $$

where $\mathcal{L}_{n,H,H',\gamma}$ consists of original width $H$ truth tables for which **every** width $H'$ representation has relative margin below $\gamma$. Together with the separate high-margin half-table count, the two classes have total cardinality strictly below $2^N$. This is a conditional implication against the original `worstCaseHeadComplexity`; it does not infer access from one badly conditioned representation.

Neither statement changes an original definition. The remaining problem is a label-preserving access theorem or an independent upper count for the universally low-margin class.

## Verification

The module build completed successfully with 4044 jobs. `AuditSplitSmoothableEstimates.lean` prints the transitive axioms of all 17 public theorem declarations. They use only `propext`, `Classical.choice`, and `Quot.sound`.
