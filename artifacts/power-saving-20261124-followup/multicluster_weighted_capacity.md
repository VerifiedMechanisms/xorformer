# Weighted capacity for several reciprocal jet clusters

## Status and scope

The unequal-length cluster parameterization and the exponential simplification below are written proofs. The equal-length parameterization, exact finite product count, and positive-denominator score bridge are now kernel checked in [UniformClusterCapacity.lean](../../formalization/HeadComplexity/Research/UniformClusterCapacity.lean). The weighted sign-count ingredient is now kernel checked as `HeadComplexity.weightedStrictPolynomialSignPatterns_card_le` in [WeightedPolynomialSignCount.lean](../../formalization/HeadComplexity/Polynomial/WeightedPolynomialSignCount.lean). It proves the stronger factor $4eD$ where the inherited written [weighted-degree theorem](../power-saving-20261124/weighted_degree_sign_capacity.md) used $8eD$. The weaker constant is retained below. The new formal chain uses weighted diagonal quotient reduction and the existing generic-minimum wrappers; it assumes no sign-pattern bound.

The new bookkeeping gives the base denominator coefficients much smaller weights than the higher jet coefficients. Uniformly scaling all these rational weights converts them to positive integer weights, so the inherited theorem applies without changing its degree-to-weight ratio. This avoids charging the total cluster length to every higher jet parameter.

The resulting class is unrestricted in all its real coefficients, signs, and cancellation. Each base denominator must be positive on the full Boolean cube. The class is a strict reciprocal-jet class; no theorem here places all original representations, or all universally low-margin truth tables, in this class.

## The finite class

Put $N=2^n$ and $d=n+1$. Fix positive integer cluster lengths $q_1,\ldots,q_G$, and let $K=\sum_gq_g$. At cluster $g$, choose arbitrary real affine forms $B_{g,0},\ldots,B_{g,q_g-1}$ and $L_{g,0},\ldots,L_{g,q_g-1}$, requiring only $B_{g,0}(x)\gt0$ at every Boolean vertex.

Define reciprocal coefficients by the finite formal-series recurrence

$$ R_{g,0}=B_{g,0}^{-1},\qquad R_{g,r}=-B_{g,0}^{-1}\sum_{j=1}^{r} B_{g,j}R_{g,r-j}. $$

Thus $R_{g,r}(x)$ is the coefficient of $t^r$ in the reciprocal of $B_{g,0}(x)+\sum_{j\geq1}B_{g,j}(x)t^j$. Consider scores

$$ S(x)=c+\sum_{g=1}^G\sum_{r=0}^{q_g-1}L_{g,r}(x)R_{g,r}(x),\qquad S(x)\neq0\text{ for every }x\in\lbrace0,1\rbrace^n. $$

There are $p=1+2dK$ real parameters, including the bias $c$. Let $T(q_1,\ldots,q_G)$ be the number of strict truth tables represented by these scores. If $p\leq N$, then

$$ T(q_1,\ldots,q_G)\leq\left(\frac{16e^2N}{p}\right)^p K^{dG}. $$

Only the $dG$ base-coefficient blocks retain the indicated length penalty. There is no factor $K^{dK}$ on the higher jet coefficients.

## Proof of the finite count

### Clearing positive denominators

Multiply $S$ by the everywhere-positive quantity

$$ Q(x)=\prod_{g=1}^G B_{g,0}(x)^{q_g}. $$

This preserves every strict label. Iterating the recurrence shows that each monomial in $B_{g,0}^{q_g}R_{g,r}$ has the form

$$ (-1)^{\ell}B_{g,0}^{q_g-1-\ell}\prod_{j=1}^{r}B_{g,j}^{k_j},\qquad \sum_j k_j=\ell,\qquad\sum_jj k_j=r. $$

Here $0\leq\ell\leq r\leq q_g-1$, so the displayed exponent of $B_{g,0}$ is nonnegative. Multiplicities of these monomials have no effect on their weights.

### Rational weights

Every coefficient of the indicated affine form receives the following weight:

$$ w(B_{g,0})=\frac1K,\qquad w(B_{g,j})=\frac j{q_g}+\frac1K\quad(j\geq1),\qquad w(L_{g,r})=1-\frac r{q_g},\qquad w(c)=1. $$

All weights are positive and at most two. The contribution of one cluster term to the cleared polynomial has weight

$$ \begin{aligned} w\left(L_{g,r}B_{g,0}^{q_g-1-\ell}\prod_jB_{g,j}^{k_j}\prod_{h\neq g}B_{h,0}^{q_h}\right)&=1-\frac r{q_g}+\frac{q_g-1-\ell}{K}+\frac r{q_g}+\frac\ell K+\frac{K-q_g}{K}\cr &=2-\frac1K. \end{aligned} $$

The bias term $cQ$ has weight two. Evaluating affine forms at a Boolean vertex does not change these weighted-degree bounds. Every one of the $N$ cleared evaluation polynomials therefore has weighted degree at most $D=2$.

The weights are rational. Choose a common positive integer multiple $M$ making $Mw_\ell$ integer for every parameter, and apply the inherited theorem with degree $2M$. Its factor $D^p/\prod_\ell w_\ell$ is invariant under this common scaling. Thus the rational-weight version follows directly from the stated integer-weight theorem.

### The factorial product

For each of the $d$ affine coefficient positions at a cluster of length $q$, the product of its denominator and numerator weights is at least

$$ \begin{aligned} \frac1K\left(\prod_{j=1}^{q-1}\frac jq\right)\left(\prod_{j=1}^{q}\frac jq\right)&=\frac1K\left(\frac{q!}{q^q}\right)^2\cr &\geq\frac1K e^{-2q}. \end{aligned} $$

The first product is empty when $q=1$, and the identity remains valid. The last step is $q!\geq(q/e)^q$. Consequently

$$ \prod_{\ell=1}^p w_\ell\geq e^{-2dK}K^{-dG}. $$

The weighted theorem, followed by $2dK=p-1\leq p$, now gives

$$ \begin{aligned} T(q_1,\ldots,q_G)&\leq\left(\frac{16eN}{p}\right)^p e^{2dK}K^{dG}\cr &\leq\left(\frac{16e^2N}{p}\right)^p K^{dG}. \end{aligned} $$

The positivity restriction on base denominators only decreases the set of parameter points relative to the polynomial sign-count theorem. No noncancellation condition was used. $\blacksquare$

## Kernel-checked uniform cluster formula

For $G\geq1$ clusters, each of length $q\geq1$, set $K=Gq$ and $p=1+2(n+1)Gq$. The declaration `UniformClusterCapacity.card_represented_le_product` proves the following exact finite bound whenever $p\leq N$:

$$ T(q,\ldots,q)\leq\frac{(8eKN/p)^p}{K\left(\prod_{j=0}^{q-1}(Gj+1)\prod_{j=0}^{q-1}G(q-j)\right)^{(n+1)G}}. $$

The formal polynomial family permits every real coefficient. The actual reciprocal coefficients satisfy the defining recurrence by `reciprocalCoefficient_succ`. The declaration `eval_scorePoly` proves exact multiplication by the common positive denominator, and `mem_represented_of_score` transfers every full strict truth table with positive base denominators into the counted class. The recurrence numerator has weighted degree $(G+1)r$; after the remaining base powers are inserted, the complete cleared score has degree $2Gq$ under the integer weights $Gj+1$, $G(q-r)$, and $Gq$.

The finite product formula is kernel checked. The factorial simplification and the following two uniform asymptotic consequences remain written proofs. Neither form asserts an unrestricted compiler or a lower bound for the original worst-case head complexity.

## Explicit bounds at the two requested widths

Let $n\geq32$, and let $K_{\max}\geq1$ be an integer. Allow arbitrary ordered compositions of any total length $1\leq K\leq K_{\max}$, subject to a lower bound $q_g\geq q_{\min}$ on every cluster. Constants are also permitted as length-zero scores.

Each of the following two sets of hypotheses implies that the union of all these strict truth tables has size at most $2^{N/2}$:

1. $K_{\max}\leq N/(100n\sqrt n)$ and $q_{\min}\geq\sqrt n$.

2. $K_{\max}\leq N\log n/(100n^2)$ and $q_{\min}\geq\log n$.

Logarithms in these hypotheses and the proof are natural. The stronger proposed thresholds $q_{\min}\geq\exp(\sqrt n)$ or $q_{\min}\geq\exp(n/\log n)$ also suffice, whenever such compositions exist.

**Proof.** For $K\geq1$, $p=1+2(n+1)K\leq5nK$. In both cases, using $\log n\leq\sqrt n$ for $n\geq32$ gives

$$ \frac pN\leq\frac1{20\sqrt n}\lt1. $$

The function $u\mapsto u\log(16e^2/u)$ is increasing on $(0,1]$. Hence the logarithm of the first factor in the finite count is at most

$$ \frac{N}{20\sqrt n}\log(320e^2\sqrt n)\leq N\left(\frac8{20\sqrt n}+\frac1{40}\right)\leq\frac{21}{200}N. $$

Here $\log(320e^2)\lt8$, $\log n\leq\sqrt n$, and $\sqrt n\geq5$ were used. For the base penalty, $G\leq K/q_{\min}$, $d\leq2n$, $K\leq N$, and $\log K\leq n\log2$ give

$$ dG\log K\leq\frac{2nK}{q_{\min}}\log K\leq\frac{2n^2K\log2}{q_{\min}}\leq\frac{N\log2}{50}. $$

The last inequality follows separately from either stated pair of width and cluster-size bounds. There are $2^{K-1}$ ordered positive compositions of $K$. Summing this number over $1\leq K\leq K_{\max}$, and including one empty composition, gives $2^{K_{\max}}$ charts. The two constant sign tables fit the same uniform upper bound used for the nonempty charts. Since $K_{\max}\leq N/100$, the additional logarithm from the chart union is at most $N\log2/100$.

The total logarithm is therefore at most

$$ \left(\frac{21}{200}+\frac{3\log2}{100}\right)N\lt\frac{N\log2}{2}. $$

For the last strict inequality, $\log2\gt1/2$ already suffices. $\blacksquare$

## Width overhead and the remaining access lemma

The count charges the total jet length $K$, including all clusters. If an original representation of width $H$ is mapped into this class with $K\leq CH+B$, one must impose $CH+B\leq K_{\max}$ before using the finite estimate. A fixed multiplicative factor is absorbed into the constant in the original width, and a fixed additive overhead is eventually negligible. No free width increase is implicit in the statement.

For the margin route, the useful missing statement is about truth tables: every table representable at the original width but having insufficient relative margin at every comparable width must admit one of these strict multicluster representations, or the tables not admitting one must receive a separate upper count. One badly conditioned representation does not establish this statement.

The class also excludes a residual collection of arbitrary simple poles unless their total contribution is separately counted. Length-one clusters are valid finite-class parameters, but then the base penalty restores a factor $K^{dK}$. Declaring all such poles to be a single cluster requires a proved sign-preserving degeneration or repair. Neither the weighted calculation nor an arbitrarily small coefficient margin supplies it.

The finite formula is therefore a new restricted capacity estimate. It does not yet improve the original unrestricted lower bound.

## Audit correction

The first committed version overstated the factorial product by a factor of $q$ per affine coefficient position. The correct identity is $(q-1)!/q^{q-1}=q!/q^q$. The finite prefactor above is therefore $K^{dG}$. Both displayed half-entropy corollaries are unchanged, since their proofs already used the larger bound $dG\log K$ for this contribution. This correction was found by independently clearing the rational weights to integer weights.
