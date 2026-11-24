# A margin-free comparison class with degree independent of width

## Finite count

Consider scores on the Boolean cube of the form

$$ T(x)=b+\sum_{h=1}^K\left(a_{h0}+\sum_{i=1}^n a_{hi}x_i\right)\prod_{i:x_i=1}z_{hi}. $$

All coefficients and factors are arbitrary real numbers. In particular, the count includes positive exponential factors. The parameter count and parameter degree are

$$ p=1+(2n+1)K,\qquad D\leq n+1. $$

When $p\leq N=2^n$, the number of strict sign tables is at most

$$ \left(\frac{4e(n+1)N}{p}\right)^p. $$

For every integer $n\geq32$, this is at most $2^{N/2}$ whenever

$$ K\leq\frac{N}{100n\log(n+1)}. $$

Here and below, $\log$ is the natural logarithm. The last estimate is proved using the previously checked entropy budget, giving the stronger intermediate bound $\exp(7N/25)$. This class imposes no margin assumption, sign restriction on the coefficients, or bound on their magnitude.

## Exact and approximate bridges

The following statements are kernel checked, with the compiler hypothesis explicit.

1. If every truth table of original width $H$ has a representation with $K$ terms of the displayed form and $K$ satisfies the displayed budget, then $H\lt W(n)$.

2. The same conclusion holds if each truth table of original width $H$ differs on at most $N/16$ inputs from some table with $K$ terms in this class.

The second assertion uses the independently checked Hamming-ball bound. A union of at most $2^{N/2}$ balls of radius $N/16$ has fewer than $2^N$ elements. The centers may depend on the complete target. The compiler may choose all replacement numerators and product directions jointly.

A sufficient compiler budget at the aimed original width $H=\lfloor cN/n^{3/2}\rfloor$ is an overhead of order $\sqrt n/\log n$, with a sufficiently small constant. In particular, an overhead bounded by any fixed power of $\log n$ would suffice for the benchmark. At a general width $H=\lfloor cN/n^{2-\delta}\rfloor$, the sufficient overhead is of order $n^{1-\delta}/\log n$.

These are sufficient conditions, not compiler theorems. No unrestricted gain follows from the comparison-class count alone.

## An elementary compiler that is too wide

Write an original score, after absorbing the bias into one numerator, as

$$ S(x)=\sum_{h=1}^H\frac{A_h(x)}{B_h(x)},\qquad B_h(x)\gt0. $$

For $H\geq1$, clearing denominators gives a strict sign-equivalent polynomial

$$ P(x)=\sum_{h=1}^H A_h(x)\prod_{g\neq h}B_g(x). $$

For positive $\varepsilon$, replace every factor $B_g$ by $(\exp(\varepsilon B_g)-1)/\varepsilon$. The resulting expression converges to $P$ at every vertex, hence preserves the entire strict sign table for sufficiently small $\varepsilon$. Expanding and grouping by proper subsets $U\subsetneq\lbrace1,\ldots,H\rbrace$ gives

$$ P_\varepsilon(x)=\varepsilon^{1-H}\sum_{U\subsetneq\lbrace1,\ldots,H\rbrace}(-1)^{H-1-|U|}\left(\sum_{h\notin U}A_h(x)\right)\exp\left(\varepsilon\sum_{g\in U}B_g(x)\right). $$

Every summand is an affine function times a separable positive product. Thus a written proof gives $K\leq2^H-1$. This is useful for fixed $H$ and entirely inadequate when $H$ is exponential in $n$. It also shows why preserving the numerators and directions of the individual reciprocal terms is an unnecessarily restrictive requirement: cancellation is reorganized before approximation.

This finite-difference compiler is a written proof only. It is not used in the Lean comparison-class count or either conditional bridge.

## Existing obstructions and the surviving question

The inherited [adaptive product compiler obstruction](../power-saving-20261124/adaptive_product_compiler_logarithmic_obstruction.md) constructs genuine original tables requiring $K=\Omega(H\log H)$ even when the replacement terms are chosen jointly with arbitrary real factors. Its dimension can be $n=\Theta(H\log H)$. It rules out constant overhead uniformly over every dimension and width. It does not rule out the budgets above in the regime $H\asymp N/n^{3/2}$.

The inherited [signed quadrature obstruction](../power-saving-20261124/signed_exponential_quadrature_obstruction.md) needs exponentially many quadrature nodes for a two-head score when the original numerators and denominator directions are retained. That restriction is essential. The elementary finite-difference compiler above allows three jointly chosen affine-product terms for two heads, so the quadrature obstruction cannot be applied to a free joint compiler.

The inherited [cleared-numerator border-rank obstruction](../power-saving-20261124/cleared_numerator_border_rank.md) shows that approximation of the particular cleared table can require exponentially many terms. For every $H\geq1$, it constructs an admissible score in dimension $n=4H$ whose cleared numerator has balanced matrix rank $2^{H+1}-2$. Every entrywise limit of $K$ affine-product terms and a bias has matrix rank at most $2K+1$, so $K\geq2^H-1$. This matches the elementary compiler above for that exact table. Its strict sign table is an OR function and has a one-term representation. Therefore the obstruction does not exclude a sign compiler using a different table, equivalently a target-dependent positive multiplier on the vertices. It is a written proof only and does not itself give an obstruction in the critical-width regime.

The first missing lemma for this route is consequently precise: prove, at widths comparable to $N/n^{3/2}$, an exact compiler or a compiler with at most $N/16$ errors whose width is at most $N/[100n\log(n+1)]$. A bound valid only for balanced denominators, fixed directions, or scores with a given relative margin does not meet this lemma.

## Verification

The file is `formalization/HeadComplexity/Research/AffineProductCapacity.lean`, namespace `HeadComplexity.AffineProductCapacity`. The finite and asymptotic count declarations are `card_represented_le` and `card_represented_le_half_tables`. The conditional original-model bridges are `worstCase_gt_of_compiler` and `worstCase_gt_of_approximate_compiler`. Their definitions explicitly quantify over the original `headComputableFunctions` or `computableWithHeadsN` class.

`lake build HeadComplexity.Research.AffineProductCapacity` passed with 4028 jobs. `AffineProductCapacityAudit.lean` checks ten declarations transitively; all report only `[propext, Classical.choice, Quot.sound]`. The original definition of `worstCaseHeadComplexity` and every original head definition are unchanged.
