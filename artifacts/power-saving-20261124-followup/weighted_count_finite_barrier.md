# A finite barrier for the optimized weighted certificate

## Kernel-checked obstruction

Set $N=2^n$. Suppose $n\geq4$, $H\geq2$, $2nH\leq N$, and $n^2H\geq2N$. Define

$$ B=\frac{16e^2N^2(H-1)}{n^2H^2}. $$

Then

$$ 2B^{nH}\gt 2^N. $$

This is `HeadComplexity.WeightedCountBarrier.optimal_certificate_exceeds_all_tables` in `formalization/HeadComplexity/Research/WeightedCountBarrier.lean`. It concerns the numerical value of an upper-bound certificate. It does not assert that all truth tables are representable.

The same module proves a stronger statement for arbitrary positive real block weights. If denominator weights are $w_h\gt0$, numerator weights are $u_h\gt0$, and a degree cap $D$ satisfies

$$ u_h+\sum_jw_j-w_h\leq D\qquad\text{for every }h, $$

then

$$ 2\frac{(4eDN/(2nH))^{2nH}}{(\prod_hw_h\prod_hu_h)^n}\geq2B^{nH}\gt2^N. $$

The declarations are `every_block_certificate_ge_optimal` and `every_block_certificate_exceeds_all_tables`. The premise is necessary for the indicated normalized cleared-score monomials. Any extra degree requirement only strengthens the obstruction.

## Proof

The finite elementary inequality $n^2\leq2^n$ holds for $n\geq4$. The width restriction and $H\geq2$ imply $B\geq N/n$, hence $B^2\geq N$. Consequently

$$ nH\log B\geq\frac{n^2H\log2}{2}\geq N\log2. $$

Thus $B^{nH}\geq2^N$, and the outer factor $2$ makes the desired inequality strict.

For general weights, `WeightedDegreeOptimization.degree_ratio_lower` gives

$$ (\prod_hw_h\prod_hu_h)^n[4(H-1)]^{nH}\leq D^{2nH}. $$

Substitution into the weighted Warren expression yields exactly the optimized expression $2B^{nH}$.

## Application to the requested scales

For each fixed $c\gt0$, the integer widths $H=\lfloor cN/n^{3/2}\rfloor$ and $H=\lfloor cN\log n/n^2\rfloor$ eventually satisfy all four hypotheses. For the first width, $c\sqrt n$ grows without bound; for the second, $c\log n$ grows without bound. The floor costs at most one head, and $N/n^2$ also grows without bound. Both widths are eventually below $N/(2n)$ because $c/\sqrt n$ and $c\log n/n$ tend to zero.

These last asymptotic specializations are written deductions from the finite theorem, not separate Lean declarations. The finite theorem pinpoints why changing positive block weights cannot make the existing certificate prove either target. Crossing the barrier requires new information beyond that degree-and-weight calculation, such as the missing whole-table margin repair or a valid restricted-class access theorem.

## Verification

`weighted-count-barrier-build.txt` records the module build. `weighted-count-barrier-axioms.txt` records transitive axiom checks for all five theorems. Each uses only `propext`, `Classical.choice`, and `Quot.sound`.
