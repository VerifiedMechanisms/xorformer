# Positive partitions do not by themselves restrict truth tables

## The proposed access route

Shift every original head by its full-cube minimum and move the constants to the bias. The resulting heads are nonnegative, each has minimum zero, and the score has the form $\sum_h g_h-T$. When $T\gt0$, normalize $T=1$. Every negative input then has $\sum_h g_h(x)\lt1$.

Control of nonnegative heads from their values on negative inputs can therefore give a useful amplitude estimate. It does not by itself give a signed gap. The remaining possibility $\sum_hg_h\approx1$ cannot be discarded merely by counting all representations near a positive partition: that class still contains every original truth table at an overhead of two heads.

## An exact original two-head partition

On $n\geq1$ bits, choose one coordinate and put

$$ B(x)=1+\sum_{i=1}^n x_i,\qquad q(x)=\frac{2x_1}{B(x)},\qquad r(x)=1-q(x)=\frac{1-x_1+\sum_{i=2}^n x_i}{B(x)}. $$

Both ratios are genuine admissible original heads, with strictly positive denominator intercept and slopes. They are nonnegative on the full cube and sum to one. The first has minimum zero on $x_1=0$ and maximum one at the singleton $e_1$. The second has minimum zero at $e_1$ and maximum one on $x_1=0$. In particular, each has full-cube norm one. Their common denominator permits an obvious exact simplification, so this first example does not refute a theorem that first removes such dependencies.

The construction and all these properties are kernel checked in `HeadComplexity.MinZeroPositivePartition`, file `formalization/HeadComplexity/Research/MinZeroPositivePartition.lean`.

## Every original table has bounded-amplitude representatives near a partition

Let $S=b+\sum_{h=1}^H\phi_h$ be any strict original representation, let $A=|b|+\sum_h\|\phi_h\| _\infty$, and let $m_h=\min_x\phi_h(x)$. Put $C=b+\sum_hm_h$. Then $|C|\leq A$ and each shifted head $\phi_h-m_h$ is nonnegative, has minimum zero, and has norm at most $2\|\phi_h\| _\infty$.

Choose any $\epsilon\gt0$ with $\epsilon A\leq1/4$. The scalar $a=1+\epsilon C$ is positive. The following $H+2$ genuine heads are nonnegative and all have minimum zero:

$$ a q,\qquad a r,\qquad \epsilon(\phi_1-m_1),\ldots,\epsilon(\phi_H-m_H). $$

Their total is exactly $1+\epsilon S$. With bias $-1$, their full truth table is therefore the original truth table. Moreover, including that bias, their actual requested amplitude is at most

$$ 1+2a+2\epsilon\sum_h\|\phi_h\| _\infty\leq3+4\epsilon A\leq4. $$

Their sum can be made uniformly as close to one as desired, since $|\epsilon S(x)|\leq\epsilon A$. For any tolerance $\delta\gt0$, take

$$ \epsilon=\min\left(\frac{1}{4A},\frac{\delta}{A}\right). $$

Strict representation implies $A\gt0$, so this is legitimate and positive. Every head remains admissible: translating or scaling its readout does not alter the positive attention parameters, and the two additional partition heads are explicit original atoms. No rescaling claim about relative margin is made. The construction intentionally creates a small-margin representation of the same labels.

The complete actual-model assembly is in `HeadComplexity.NonnegativePartitionEmbedding.exists_bounded_near_partition`. Its hypotheses and conclusion retain the full-cube norm, arbitrary bias, arbitrary real coefficients, both orientations of the source heads, exact score identity, minimum-zero condition for every head, and all truth-table labels.

The corollary `exists_bounded_near_partition_of_computable` starts directly from the original `computableWithHeadsN` predicate. It uses the inherited same-width strictification and needs no margin hypothesis. The module builds successfully in 3287 jobs; all 13 declarations have only `propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom reports. An independent semantic review checked the admissibility, norm budget, and quantifiers.

## Three-head partitions survive pairwise dependency tests

A more structured rigidity claim can already fail at three heads. Write $x,y\in\lbrace0,1\rbrace$ and let $z$ be a nonnegative sum of the other Boolean coordinates. Set

$$ B_1=1+2x+3y+3z,\qquad B_2=1+2x+y+2z,\qquad B_3=1+x+3y+2z. $$

The previously checked collective relation has numerators $A_1=3x$, $A_2=-6x-4y-4z$, and $A_3=2x+8y+4z$, and satisfies $\sum_iA_i/B_i=0$ on the full cube. Hence

$$ g_1=\frac{2A_1}{5B_1},\qquad g_2=1+\frac{2A_2}{5B_2}=\frac{5-2x-3y+2z}{5B_2},\qquad g_3=\frac{2A_3}{5B_3} $$

are nonnegative genuine heads with total one. Each has minimum zero: use $x=0$ for $g_1$, $x=y=1,z=0$ for $g_2$, and $x=y=z=0$ for $g_3$. Each is nonconstant. On five bits, all three pairs of normalized affine-ratio feature spaces are independent by `CollectiveThreeHeadRelation.pair_01_injective`, `pair_02_injective`, and `pair_12_injective`. Thus removing only shared-denominator pairs or pairwise zero relations does not classify all positive partitions. The three-head conversion here is written algebra; the underlying exact zero relation and pair independence are kernel checked in `CollectiveThreeHeadRelation.lean`.

This example uses only three shared affine statistics. It does not disprove a low-parameter classification after quotienting all exact dependencies, nor a truth-table-preserving repair with a constant width overhead.

## First failed lemma and remaining possibility

The failed statement is that admitting a minimum-zero, nonnegative-head, bounded-amplitude representation arbitrarily close to the constant partition forces a small family of truth tables. Every original width $H$ table admits such a representation at width $H+2$. At the critical widths, the overhead is negligible.

A useful replacement would have to select a representation after removing exact partition dependencies, and then either give a quantitative separation from the remaining partition strata or count every possible truth table carried by their degenerations. This is an existential access problem over complete representations. One artificial near-partition representation proves neither that the target has small optimal margin nor that every comparable-width representation remains near a partition. The proposed negative-vertex control can remain valid, but the step from that control to a healthy whole-table margin is still missing.
