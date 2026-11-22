# Separated Scales of Positive Affine Boolean Tables

## Statement

Let $w_1,\ldots,w_d$ be nonnegative real numbers. A family of nonempty subsets $S_j\subseteq\lbrace1,\ldots,d\rbrace$ has at most $d$ members if every pair of its subset sums differs by a multiplicative factor strictly greater than $d$. Explicitly, for distinct $j,k$, require

$$ d\sum_{i\in S_k}w_i\lt\sum_{i\in S_j}w_i\qquad\text{or}\qquad d\sum_{i\in S_j}w_i\lt\sum_{i\in S_k}w_i. $$

For ratios of subset sums from $d$ nonnegative numerator weights and $e$ positive denominator weights, the corresponding statement has separation factor $de$ and at most $de$ members.

Both assertions are Lean checked as `HeadComplexity.PositiveSubsetScales.separated_subset_sums` and `HeadComplexity.PositiveSubsetScales.separated_ratios`. They apply to a specific affine-table compatibility question, not to the number of head representations or their labels.

## Proof

Choose a largest summand $w_{i_j}$ in each nonempty subset. Nonnegativity gives

$$ w_{i_j}\leq\sum_{i\in S_j}w_i\leq d w_{i_j}. $$

If two subsets have the same chosen index, each of their sums is at most $d$ times the other. The required strict separation therefore forces the chosen indices to be distinct. There are only $d$ indices.

For ratios, choose a largest numerator summand $a$ and largest denominator summand $b$. If two ratios $A_1/B_1,A_2/B_2$ share this pair, then

$$ a\leq A_i\leq da,\qquad b\leq B_i\leq eb,\qquad B_i\gt0. $$

Consequently

$$ A_1B_2\leq(da)(eb)=deab\leq deA_2B_1,\qquad \frac{A_1}{B_1}\leq de\frac{A_2}{B_2}. $$

The reverse comparison follows by swapping the indices. Strict separation forces distinct pairs, of which there are at most $de$. $\blacksquare$

## Consequences for admissible denominators

Every admissible affine denominator on $n$ bits can be written as a subset sum of at most $n+1$ fixed positive weights, with a mandatory positive constant weight. For positive slopes this is the original expression. For negative slopes, use

$$ B(x)=\left(b_0+\sum_i b_i\right)+\sum_i(-b_i)(1-x_i). $$

The parenthesized constant is positive by evaluation at the all-one vertex. A constant denominator uses one weight.

It follows that a single admissible denominator has at most $n+1$ values with pairwise multiplicative separation strictly greater than $n+1$. A ratio of two admissible denominators has at most $(n+1)^2$ values with separation strictly greater than $(n+1)^2$.

For any fixed $R\gt1$, an increasing $R$-separated sequence of subset sums has at most

$$ d\left(1+\lfloor\log_R d\rfloor\right) $$

members. Indeed, those with one chosen largest summand lie in an interval of multiplicative length at most $d$. If that class has $k$ elements, its first and last differ by at least $R^{k-1}$, so $k\leq1+\lfloor\log_R d\rfloor$. Summing over the largest-summand index proves the assertion. This logarithmic corollary is a written consequence of the Lean-checked dominant-summand bounds.

## What this excludes

The [reciprocal Hall selector](reciprocal-matching-shattering.md) uses geometrically increasing poles over $q(q+1)/2$ groups. For large $q$, neither one admissible affine table nor a ratio of two such tables on only logarithmically many bits can give those poles: the number of groups exceeds the square of the number of available summands, while the geometric separation exceeds that square.

This proves that those literal pole tables cannot be inserted into the small-dimensional Boolean architecture by the indicated affine or affine-ratio substitutions. It does not exclude a different construction, a nonlinear reparameterization, or cancellations among arbitrarily close values. No norm or margin assumption has been added to the head model. A deduction of an asymptotic sign count from this scale invariant would need a new argument and remains blocked.
