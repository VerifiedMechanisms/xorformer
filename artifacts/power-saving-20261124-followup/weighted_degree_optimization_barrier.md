# Optimality of the block-weighted degree count

## Scope

The unrestricted count in `WeightedNormalizedCounting.lean` improves the leading constant in the lower bound for the original worst-case complexity. A natural next attempt is to assign different weights to different heads or coordinates. The following optimization shows that this cannot improve the degree-to-weight ratio for the same cleared polynomial chart.

This is a limitation of that particular counting certificate. It is not an upper bound on head complexity, and it does not rule out a more precise count of real feasible parameter points.

## Scalar optimization

Let $n\geq1$ and $H\geq2$. Give the denominator variables of head $h$ positive block weight $w_h$ and its numerator variables positive block weight $u_h$. Write $W=\sum_h w_h$. Any weighted degree bound $D$ for the normalized cleared score must satisfy

$$ W\leq D,\qquad u_h+W-w_h\leq D\quad\text{for every }h. $$

The bias monomial gives the first inequality and a numerator monomial from head $h$ gives the second. At the all-one input, these monomials have nonzero coefficients and distinct numerator-variable supports. Thus cancellation cannot remove them.

Summing the second inequalities gives

$$ U=\sum_hu_h\leq HD-(H-1)W. $$

Finite AM-GM applied separately to the two blocks gives

$$ \left(\prod_hw_h\right)\left(\prod_hu_h\right)\leq\left(\frac{WU}{H^2}\right)^H\leq\left(\frac{D^2}{4(H-1)}\right)^H. $$

For the last inequality, multiply the bound on $U$ by $4(H-1)W$ and use

$$ H^2D^2-4(H-1)W\bigl(HD-(H-1)W\bigr)=\bigl(HD-2(H-1)W\bigr)^2\geq0. $$

Repeating each block weight for its $n$ coordinate variables therefore yields

$$ \frac{D^{2nH}}{\prod_hw_h^n u_h^n}\geq\bigl(4(H-1)\bigr)^{nH}. $$

The choice $w_h=1$, $u_h=H-1$, $D=2(H-1)$ attains equality. It is precisely the choice already used by `WeightedNormalizedCounting.card_le_optimal`. In the uniform numerator-weight family, the same conclusion is the elementary identity

$$ \frac{(H+k-1)^2}{k}=4(H-1)+\frac{(k-(H-1))^2}{k}. $$

## Coordinate weights

Allow positive weights $w_{h,i}$ and $u_{h,i}$ depending on the coordinate. Set $w_h=\max_iw_{h,i}$ and $u_h=\max_i u_{h,i}$. The weighted degree of the all-one cleared score still gives exactly the preceding block inequalities: choose a coordinate realizing each maximum in the relevant product monomial. Meanwhile,

$$ \prod_{h,i}w_{h,i}u_{h,i}\leq\prod_hw_h^n u_h^n. $$

Consequently, coordinate-dependent weights cannot reduce the ratio below the displayed optimum either. This coordinate-to-block reduction and the all-one monomial argument are written proofs. The scalar optimization under its explicit hypotheses is kernel checked.

## Failure at the requested widths

For $p=2nH$, weighted Warren gives the numerical upper bound

$$ \frac{2}{\prod_{h,i}w_{h,i}u_{h,i}}\left(\frac{4eDN}{2nH}\right)^{2nH}. $$

Every weight choice in this chart makes that numerical expression at least

$$ 2\left(\frac{16e^2N^2(H-1)}{n^2H^2}\right)^{nH}. $$

For $H\geq2$, its base is at least $8e^2N^2/(n^2H)$. At either requested width, with any fixed $c\gt0$, the logarithm of this base is eventually at least $(\log2)n/2$. At $H\asymp cN/n^{3/2}$, the resulting exponent divided by $N$ grows as a positive constant times $\sqrt n$. At $H\asymp cN\log n/n^2$, it grows as a positive constant times $\log n$. Thus the optimized numerical bound eventually exceeds the total $2^N$ truth tables in both regimes. Integer rounding of these exponentially growing widths does not change these conclusions.

This identifies the failed inequality: weight optimization alone cannot make the same Warren exponent smaller than $N\log2$. A new argument must use more than the weighted degree and product of variable weights.

## Verification

The file `formalization/HeadComplexity/Research/WeightedDegreeOptimization.lean` contains five kernel-checked declarations:

- `product_le_mean_pow` proves the finite AM-GM form used here.
- `mean_product_le` proves the quadratic optimization under the displayed degree inequalities.
- `product_blocks_le` bounds the product of all head-block weights.
- `degree_ratio_lower` proves the repeated-block degree ratio inequality.
- `uniform_weight_identity` proves the exact one-variable optimization identity.

All names have namespace `HeadComplexity.WeightedDegreeOptimization`. The successful module build and transitive axiom outputs are in `weighted-optimization-build.txt` and `weighted-optimization-axioms.txt`. Every declaration uses only `propext`, `Classical.choice`, and `Quot.sound`. The coordinate reduction, polynomial-support discussion, and asymptotic failure at the two requested widths remain written arguments. No original definition or model hypothesis was changed.
