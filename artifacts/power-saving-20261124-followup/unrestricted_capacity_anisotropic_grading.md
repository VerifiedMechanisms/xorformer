# Arbitrary coordinate weights do not improve the cleared-chart bound

## Exact obstruction

The normalized unrestricted chart has $nH$ numerator variables and $nH$ denominator variables. Its cleared predicates are

$$ P_s(x)=s\prod_hB_h(x)+\sum_hU_h(x)\prod_{j\neq h}B_j(x),\qquad B_h(x)=1+\sum_i b_{hi}x_i,\qquad U_h(x)=\sum_i a_{hi}x_i. $$

Here $s\in\lbrace-1,1\rbrace$ is discrete, and the coefficients $a_{hi},b_{hi}$ are formal parameter variables. Give the numerator variable $a_{hi}$ any positive weight $u_{hi}$ and the denominator variable $b_{hi}$ any positive weight $w_{hi}$. Let $U_h=\max_i u_{hi}$ and $W_h=\max_i w_{hi}$.

The predicate at the all-one Boolean row contains, with coefficient one, every monomial consisting of one numerator variable from head $h$ and one denominator variable from each other head. The numerator variable identifies its summand uniquely, so neither the other heads nor the bias term cancel it. A weighted degree cap $D$ therefore requires

$$ U_h+\sum_jW_j-W_h\leq D\qquad\text{for every }h. $$

This is a written support calculation for the exact normalized polynomial, not an assumption about feasible parameter values. Positivity of admissible denominators cannot remove these formal monomials from this polynomial chart.

The existing kernel-checked block optimization in `WeightedDegreeOptimization.lean` gives

$$ \left(\prod_hW_h\right)\left(\prod_hU_h\right)\leq\left(\frac{D^2}{4(H-1)}\right)^H\qquad(H\geq2). $$

Each coordinate weight is at most its block maximum. Consequently,

$$ \left(\prod_{h,i}w_{hi}\right)\left(\prod_{h,i}u_{hi}\right)\leq\left(\frac{D^2}{4(H-1)}\right)^{nH}. $$

Equality is attained by uniform numerator weights $D/2$ and uniform denominator weights $D/(2(H-1))$. Thus the optimal numerator-to-denominator weight ratio is exactly $H-1$, already used by `WeightedNormalizedCounting.card_le_optimal`. Arbitrary head-dependent or coordinate-dependent positive weights cannot improve that certificate.

## Finite failure at the quadratic scale

For $n\geq4$, $H\geq2$, $2nH\leq2^n$, and $n^2H\geq2^n$, the numerical weighted Warren expression for every such coordinate grading is strictly larger than $2^{2^n}$. It cannot exclude even one truth table. This is a failure of that upper-bound expression, not a lower bound on the number of representable tables.

`HeadComplexity.AnisotropicWeightBarrier.every_coordinate_certificate_exceeds_all_tables` is the precise kernel-checked comparison. It retains the positive-weight, block-envelope, degree-cap, and finite-width hypotheses explicitly. Its proof combines `product_coordinates_le` with the parent run's `WeightedCountBarrier.optimal_certificate_exceeds_all_tables_at_quadratic_scale`. The intermediate `coordinate_degree_ratio_lower` and `every_coordinate_certificate_ge_optimal` expose the exact optimization inequality.

The formal module does not duplicate the polynomial support calculation from the first section: its interface takes the resulting block-envelope degree caps as hypotheses. That calculation is elementary and audited above. No original head or worst-case-complexity definition changes, and this obstruction does not rule out a different chart, positivity-sensitive counting, or a truth-table-preserving representation theorem.
