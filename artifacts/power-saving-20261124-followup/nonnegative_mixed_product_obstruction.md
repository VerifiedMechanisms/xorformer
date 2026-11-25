# A Mixed Reciprocal Product Obstructs Nonnegative Compilation

## Exact original-model theorem

Let $v$ be a Boolean vertex with at least two one coordinates and two zero coordinates. If $G=b+\sum_h\phi_h$ has $b\geq0$ and every original head is nonnegative on the entire cube, then

$$ \max_x|G(x)-\mathbf1_{\lbrace x=v\rbrace}|\geq\frac15. $$

This holds at every width, with arbitrary real coefficients and target-dependent denominators subject to the displayed nonnegativity assumptions. The declaration is `HeadComplexity.NonnegativePointApproximation.point_error_ge_one_fifth` in [NonnegativePointApproximation.lean](../../formalization/HeadComplexity/Research/NonnegativePointApproximation.lean).

**Proof.** Select two downward and two upward neighbors of $v$. The actual-head theorem `SelectedNegativeControl.sum_four_neighbors_le` bounds the sum of head values at $v$ by their sum at those four neighbors. Nonnegative bias preserves the same inequality for $G$. If the uniform approximation error is at most $\epsilon$, this gives

$$ 1-\epsilon\leq G(v)\leq\sum_{u\text{ selected}}G(u)\leq4\epsilon. $$

Thus $\epsilon\geq1/5$. Every head retains its original admissibility. The two orientation cases use downward and upward neighbors respectively; no individual coordinate flip is applied to a head.

## Two genuine reciprocal factors

In dimension four set $v=(1,1,0,0)$ and define

$$ P(x)=\frac1{1+(x_0+x_1)/100+100(x_2+x_3)}\cdot\frac1{1+100(2-x_0-x_1)+(2-x_2-x_3)/100}. $$

Each factor is a genuine original reciprocal head. The first has strictly positive denominator slopes. The second is the simultaneous bit complement of another head with strictly positive slopes, so its slopes are all negative and its denominator is positive on the full cube. Both factors take values in $(0,1]$.

At $v$ the product is $2500/2601$, whose distance from one is $101/2601\lt1/25$. At every other vertex, some penalized literal occurs and one denominator is at least $101$, while the other is at least one. Consequently

$$ \max_x|P(x)-\mathbf1_{\lbrace x=v\rbrace}|\leq\frac1{25}. $$

The definitions `positiveFactor`, `negativeFactor`, and `mixedProduct` construct these actual heads. `mixedProduct_formula` checks the displayed formula; `mixedProduct_point_error` checks all sixteen rational inequalities in the Lean kernel.

If a nonnegative-head sum with nonnegative bias approximates $P$ uniformly to error $\epsilon$, the triangle inequality and the preceding point theorem imply

$$ \frac15\leq\epsilon+\frac1{25},\qquad \epsilon\geq\frac4{25}. $$

This is `HeadComplexity.NonnegativePointApproximation.mixedProduct_nonnegative_compiler_error`.

## Scope of the obstruction

The common-orientation normalized-product compiler in `ProbabilityMixtureApproximation` cannot be extended to arbitrary mixed orientations while retaining nonnegative output heads and arbitrarily small uniform error. This exact example already has two factors.

The theorem does not exclude signed output heads or negative bias. It does not obstruct a truth-table repair: a point-indicator truth table itself has a healthy narrow original representation. The restriction to nonnegative output functions is explicit, and no unrestricted lower bound follows from this compiler obstruction.

## Verification

The module builds with 4,031 jobs. Its four theorem declarations and the explicit `#print axioms` audit use only `propext`, `Classical.choice`, and `Quot.sound`. The finite Boolean evaluation is kernel checked, not floating numerical evidence. The original head and complexity definitions are unchanged.
