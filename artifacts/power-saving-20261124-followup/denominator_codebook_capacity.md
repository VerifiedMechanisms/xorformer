# A finite denominator codebook as an alternative repair target

## Finite margin-free formula

Fix a target-independent list of $M$ denominator value vectors $D_j:\lbrace0,1\rbrace^n\to\mathbb R$. Consider scores

$$ T(x)=b+\sum_{h=1}^H\frac{\sum_{i=1}^n c_{hi}x_i}{D_{a_h}(x)},\qquad a_h\in\lbrace1,\ldots,M\rbrace. $$

All numerator coefficients and the bias are arbitrary real numbers. No margin or cancellation condition is imposed. For a fixed assignment of denominator indices, this is a linear polynomial in $p=1+nH$ real parameters. Therefore, if $p\leq N=2^n$, its strict truth tables number at most

$$ M^H\left(\frac{4eN}{1+nH}\right)^{1+nH}. $$

The upper bound even permits arbitrary real denominator value vectors, using Lean's total division operation. A codebook repair by genuine original heads would use only positive coherent affine denominators. Enlarging the class for the count does not supply such a repair.

The zero numerator constants cause no loss. For any positive affine denominator with constant coefficient $b_0$, write

$$ \frac{a_0+u(x)}{b_0+v(x)}=\frac{a_0}{b_0}+\frac{\big(u(x)-(a_0/b_0)v(x)\big)/b_0}{1+v(x)/b_0}. $$

The constants enter the free bias. The coefficient and denominator normalization is exact; no original head is changed. The formal bridge `mem_represented_of_affine` checks this identity on every cube point.

## Explicit scale and overhead

Let $n\geq32$ and $\log(n+1)\leq t\leq n$. Suppose $M\geq1$ and

$$ \log M\leq nt,\qquad H\leq\frac{3N}{250nt},\qquad 1+nH\leq\frac{N}{25t}. $$

The logarithm of the finite count is at most

$$ H\log M+(1+nH)\log\left(\frac{4eN}{1+nH}\right)\leq\frac{3N}{250}+\frac{7N}{25}=\frac{73N}{250}\lt\frac{N\log2}{2}. $$

Consequently at most $2^{N/2}$ tables occur.

The overhead version is explicit. If $C\geq1$, $B$ is a nonnegative integer, and

$$ 500(B+1)n^2\leq N,\qquad H\leq\frac{N}{100Cnt},\qquad K\leq CH+B+1, $$

then the same half-table count holds at comparison width $K$. Thus $K=\lceil CH\rceil+B$ is covered. An additive cost that is subexponential in $n$ satisfies the displayed overhead inequality eventually. At the critical exponential widths it can also be absorbed into a constant multiplicative cost.

For the aimed scale use $t=\sqrt n$, so a codebook of cardinality at most $\exp(n\sqrt n)$ suffices. For the logarithmic fallback use $t=n/\log n$, allowing cardinality at most $\exp(n^2/\log n)$. Both test values satisfy the interval hypotheses for $n\geq32$, by the previously kernel-checked lemmas `sqrt_test_range` and `logarithmic_test_range`.

## The exact missing lemma

For each sufficiently large $n$, choose one codebook before choosing the truth table. Prove that every original table of width $H$ at the relevant critical scale has a strict comparison score of width $K$ using this codebook, with the displayed budgets. The codebook cannot vary freely with the target. The numerator coefficients may vary arbitrarily, and arbitrary signed cancellation remains permitted.

The Lean predicate `HasCodebookRepair` is exactly containment of the original `headComputableFunctions n H` class in the fixed-codebook class. The theorem `worstCase_gt_of_codebook_repair` concludes $H\lt W(n)$ from that predicate and the finite budgets. This is a conditional original-model theorem. It is not a denominator quantization theorem, and no unrestricted asymptotic gain has been proved by this route.

In particular, pointwise rounding of one badly conditioned representation does not establish the missing lemma. The lemma permits a new representation chosen jointly from the complete target. A proof restricted to fixed original numerator coefficients, a balanced denominator class, or a target-dependent dictionary would not satisfy it.

## Verification

The module is `formalization/HeadComplexity/Research/DenominatorCodebookCapacity.lean`. The namespace is `HeadComplexity.DenominatorCodebookCapacity`. The main declarations are `card_represented_le`, `card_represented_le_exp`, `card_represented_le_half_tables`, `card_represented_with_overhead`, and `worstCase_gt_of_codebook_repair`.

The module build passed with 4030 jobs. The separate audit checks ten declarations transitively. The original `FracAtom`, computability, and `worstCaseHeadComplexity` definitions are unchanged.
