# Almost all tables require the leading quadratic-scale constant

## Kernel-checked statement

Write $N=2^n$, and let $\mathcal F_H$ be the set `HeadComplexity.headComputableFunctions n H` in the original unrestricted model. All real coefficients, target-dependent denominators, and signed cancellation remain allowed. For $n\geq8$, $H\gt0$, $u\leq1$, and $n^2H\leq uN$, the new theorem proves

$$ |\mathcal F_H|\leq\exp\bigl((u+10/n)N\log2\bigr). $$

Consequently, if $\epsilon\gt0$, $\epsilon n\geq20$, and $n^2H\leq(1-\epsilon)N$, then

$$ |\mathcal F_H|\leq\exp\bigl((1-\epsilon/2)N\log2\bigr). $$

Thus the fraction of all Boolean truth tables represented at these widths is at most $2^{-\epsilon N/2}$. This is an unconditional distributional refinement at the quadratic-denominator scale. It does not prove a positive power saving or the logarithmic fallback.

The exact declarations are `HeadComplexity.QuadraticScaleTypicalComplexity.card_le_exp_at_quadratic_budget` and `HeadComplexity.QuadraticScaleTypicalComplexity.card_le_exp_one_sub_epsilon` in `formalization/HeadComplexity/Research/QuadraticScaleTypicalComplexity.lean`.

## Proof with constants

The hypotheses imply $2nH\leq N$, so the original-model weighted counting theorem applies. Set

$$ U=\frac{n^2H}{N},\qquad C=16e^2,\qquad B=\frac{CN}{U}. $$

Then $0\lt U\leq u\leq1$ and $|\mathcal F_H|\leq2B^{nH}$. Its logarithmic upper certificate is

$$ \log2+nH\log B=\log2+UN\log2+\frac{N}{n}U(\log C-\log U). $$

The elementary estimates $\log C\leq5$ and $-U\log U\leq1-U$ give

$$ U(\log C-\log U)\leq1+4U\leq5. $$

Since $n\leq N$ and $5+\log2\leq10\log2$,

$$ \log2+5N/n\leq(5+\log2)N/n\leq10N\log2/n. $$

The first bound follows. The condition $\epsilon n\geq20$ gives $10/n\leq\epsilon/2$, proving the second. The displayed argument, including the original-model counting bridge and all numerical inequalities, is kernel checked. An independent audit of the entropy simplification found no additional hypothesis.

## Verification and limits

`quadratic-typical-build.txt` records the successful module build. `quadratic-typical-axioms.txt` records the transitive `#print axioms` results for both declarations; only `propext`, `Classical.choice`, and `Quot.sound` occur. No existing model definition or theorem statement was weakened.

The estimate gives useful entropy below any fixed leading constant less than one. At $n^2H\geq N$, the separate `WeightedCountBarrier` and `AnisotropicWeightBarrier` results show that this counting certificate already exceeds the number of all truth tables. Crossing the requested scale therefore requires a different ingredient.
