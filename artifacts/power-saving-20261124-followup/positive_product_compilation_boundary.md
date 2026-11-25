# Positive product compilation and its first obstruction

## Constant-numerator products

Consider any finite product of normalized nonnegative constant-numerator original heads. For a positive-orientation factor, write

$$ g_h(x)=\frac{c_h}{c_h+\sum_iw_{h,i}x_i},\qquad c_h\gt0,\quad w_{h,i}\gt0. $$

Every factor has full-cube norm one. The positive reciprocal expansion in `margin_repair_anchored_atomic_decomposition.md` gives

$$ g_h(x)=\sum_{S\subseteq[n]}p_{h,S}\prod_{i\in S}(1-x_i),\qquad p_{h,S}\geq0,\quad\sum_Sp_{h,S}=1. $$

If all factors have the same orientation, their product is again a probability mixture of anchored-face indicators. Indeed multiplication replaces the selected sets by their union. The product length does not enter the coefficient-mass bound. The negative-orientation case follows by complementing every coordinate simultaneously.

For $0\lt\epsilon\lt1$, choose an integer

$$ m\gt\frac{2\log(2^{n+1})}{\epsilon^2}. $$

Sample $m$ face indicators from this mixture. Hoeffding's inequality and a union bound over the entire cube show that some empirical average has uniform error less than $\epsilon/2$: the failure probability is at most $2^{n+1}\exp(-m\epsilon^2/2)\lt1$. Approximate each sampled anchored indicator within $\epsilon/2$ by one genuine head of norm at most one, and scale it by $1/m$. The resulting original score has width $m$, zero bias, total full-cube amplitude at most one, and uniform error less than $\epsilon$.

Thus products of arbitrarily many normalized constant-numerator heads of one orientation admit an $O(n/\epsilon^2)$-head value approximation with amplitude one. The exact product probability-mixture statement is kernel checked as `HeadComplexity.PositiveReciprocalExpansion.normalized_product_probability_expansion` in `Research/PositiveReciprocalExpansion.lean`, committed as `c580b9b2`.

The entire sampling and genuine-head assembly is now kernel checked in `Research/ProbabilityMixtureApproximation.lean`. The declaration `normalized_product_approximation_of_width` gives exactly $m$ genuine heads, zero bias, total full-cube amplitude at most one, and uniform error strictly below $\epsilon$ under the displayed sample threshold. `normalized_negative_product_approximation_of_width` proves the common-negative-orientation version by simultaneously complementing every input bit. The proof constructs the finite probability measure from the nonnegative coefficients, duplicates coordinates for two-sided control, and centers unit-interval features to retain the sharp range constant. `exists_normalized_atom` rescales each approximating genuine head to norm at most one while retaining arbitrarily small error. No bound on the number of product factors is assumed. The mixed-orientation assembly in the next section remains written mathematics.

## Mixed denominator orientations

When both orientations occur, multiplying the positive expansions produces a nonnegative combination of mixed-cylinder indicators. Inconsistent literal assignments contribute zero. The total coefficient mass is at most one; adding a zero feature fills the missing probability mass.

The same sampling argument gives $m=O(n/\epsilon^2)$ mixed cylinders. By `scalar_cylinder_exponential_mass.md`, each sampled cylinder is approximable using at most $n+1$ genuine heads with amplitude at most

$$ (n+1)32^{n/2}. $$

Consequently arbitrary-orientation products of normalized constant-numerator heads have width $O(n^2/\epsilon^2)$ and amplitude at most this exponential bound, independently of the product length. The output coefficients may have either sign. The high-order mixed-point obstruction shows why a polynomial amplitude bound independent of tolerance cannot hold for this general product class, even with unlimited output width.

## Affine numerators defeat a positive output compiler

The positive mixture mechanism does not extend to arbitrary affine numerators while keeping every output head nonnegative. A concrete two-factor example already has a common denominator orientation.

On four bits, put $z=x_3+x_4$, $t=x_1+x_2$, and for $i=1,2$ define

$$ \phi_i(x)=\frac{\rho x_i}{\rho+z+\eta t},\qquad \rho,\eta\gt0. $$

Every denominator slope is strictly positive, each numerator is affine, and $0\leq\phi_i\leq1$ on the entire cube. Thus both factors are genuine nonnegative original heads of positive orientation and norm at most one. As $\rho\to0^+$ and $\eta/\rho\to0^+$, their product converges uniformly to the mixed-point indicator $\mathbf1_{1100}$.

Yet every nonnegative sum of nonnegative original heads, even with a nonnegative bias, has uniform error at least $1/5$ from this indicator. This is the cone inequality proved in `unrestricted_capacity_coherent_edge_variation.md`. For completeness, if $p$ has $r\geq2$ one-coordinates, a nonnegative positive-orientation head $A/B$ satisfies

$$ (r-1)A(p)=\sum_{i:p_i=1}A(p-e_i)-A(0_P)\leq\sum_{i:p_i=1}A(p-e_i). $$

Here $0_P$ means that all $r$ selected coordinates are set to zero, with the other coordinates unchanged. Since $B(p-e_i)\leq B(p)$, this implies

$$ \phi(p)\leq\frac1{r-1}\sum_{i:p_i=1}\phi(p-e_i). $$

A negative-orientation head has the complementary upward inequality with $s$ zero-coordinates. For a nonnegative sum $S$, enlarge both orientation-specific sums by nonnegativity. If $\|S-\mathbf1_p\|_\infty\leq\epsilon$, then

$$ 1-\epsilon\leq S(p)\leq\left(\frac r{r-1}+\frac s{s-1}\right)\epsilon\leq4\epsilon. $$

Hence $\epsilon\geq1/5$. A nonnegative bias also satisfies the enlarged inequality. Arbitrary signed bias or signed output heads are outside this cone and are not covered by the obstruction.

Therefore a rational Bernstein or positive-integral compiler that replaces products by nonnegative combinations of nonnegative genuine heads fails already for two common-orientation factors with affine numerators. Increasing the output width or amplitude does not repair this particular failure. Allowing signed output cancellation is essential.

## What remains missing with signed output

The existing scalar-feature expansion of an arbitrary normalized head has absolute coefficient mass at most $2n+1$. Expanding a product of $q$ such heads gives a signed mixed-cylinder expansion with mass at most

$$ (2n+1)^q. $$

After normalizing that mass, empirical sampling to absolute error $\epsilon$ gives only the sufficient sample budget

$$ m\gt\frac{2(2n+1)^{2q}\log(2^{n+1})}{\epsilon^2}. $$

The bound can be very loose; no necessity is claimed. It fails to prove polynomial overhead in product degree. More fundamentally, inserting any independently approximated product into a globally canceling score requires error smaller than the complete score's signed gap. A positive mass estimate or an absolute approximation theorem does not supply a lower bound on that gap.

The missing statement is a joint sign-preserving compiler, or a bound on all truth tables lacking such a compiler. The positive product theorem above and the nonnegative-cone counterexample do not establish either statement. They identify exactly where positive quadrature works and where the original model's affine numerators and arbitrary signed cancellation require a different argument.

## Independent audit

A second agent checked the probability-mixture closure, the full-cube Hoeffding union budget and error allocation, the norm-preserving genuine anchored approximants, mixed-cylinder zero padding, and the nonnegative-cone inequality including its bias condition. The written argument passed that audit.
