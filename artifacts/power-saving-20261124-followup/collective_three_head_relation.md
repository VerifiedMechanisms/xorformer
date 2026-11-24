# A collective three-head Boolean cancellation

## Statement

A collective linear dependence among admissible head feature spaces need not contain a nontrivial dependence between any two of them. This invalidates a proposed reduction of all cancellation strata to pairwise denominator coincidences. It does not disprove a margin repair that changes the heads.

Let $x,y\in\lbrace0,1\rbrace$ and $z\geq0$. Define

$$ \begin{aligned} B_1&=1+2x+3y+3z,& A_1&=3x,\cr B_2&=1+2x+y+2z,& A_2&=-6x-4y-4z,\cr B_3&=1+x+3y+2z,& A_3&=2x+8y+4z.\end{aligned} $$

Then all denominators are positive and

$$ \frac{A_1}{B_1}+\frac{A_2}{B_2}+\frac{A_3}{B_3}=0. $$

Taking $z=x_3+x_4+x_5$ gives three genuine admissible heads on the five-dimensional Boolean cube. Their normalized numerator features, together with the shared bias, have a collective dependence. Every pair of the normalized feature spaces is independent: the eleven columns $1,x_i/B_a,x_i/B_b$, for $1\leq i\leq5$, have rank eleven for each pair $a\neq b$.

## Exact proof

The cleared numerator has the following polynomial identity over the reals:

$$ A_1B_2B_3+A_2B_1B_3+A_3B_1B_2=(x^2-x)(2x+7y+4z+1)+(y^2-y)(-11x-12y-12z-4). $$

Both Boolean ideal generators vanish. Division by $B_1B_2B_3\gt0$ proves the relation. At $(x,y,z)=(1,0,0)$ the three summands are $1,-2,1$, so none is identically zero. All five denominator slopes are strictly positive. The constructor `FracAtom.ofPositiveAffineRatio` therefore supplies admissible heads without changing the original model.

For pairwise independence, select eleven cube rows for each pair and use the exact inverse matrices in `three_head_pair_certificates.json`. Each asserted coefficient is an explicit rational linear combination of the eleven vanishing evaluation equations. These linear combinations are checked independently by Lean, so the conclusion does not depend on trusting a numerical rank calculation.

## Verification

`formalization/HeadComplexity/Research/CollectiveThreeHeadRelation.lean` contains the following kernel-checked declarations in namespace `HeadComplexity.CollectiveThreeHeadRelation`:

- `cleared_identity`, the real polynomial identity.
- `scalar_zero`, the identity for arbitrary nonnegative tail statistic.
- `sum_atom_eval_zero` and `atom_nonzero`, genuine nonzero heads with zero total score on the full cube.
- `pair_01_injective`, `pair_02_injective`, and `pair_12_injective`, exact independence of all three pair feature systems.

`verify_collective_three_head.py` is a separate exact rational computation. It checks all 32 evaluations, the three inverse certificates, and the full feature ranks. Its triple rank of fifteen, among sixteen columns, is a finite computation; the Lean claims only require the explicit nonzero dependence and pairwise independence.

The search transcript `three-head-relations-n5-q3.json` records a search stopped at the first candidate. Its `complete: false` field is intentional. It is not an exhaustive classification.

## Scope of the obstruction

The first failing lemma is: every dependence of normalized head features contains a dependent pair. The displayed example refutes it in the original model, with positive denominators in the interior of the admissible cone.

The tail statistic can be replaced by any nonnegative linear form on additional Boolean variables. The resulting denominator slopes still lie in the span of the two distinguished coordinates and the tail statistic. Thus this construction itself belongs to a low-dimensional denominator family. It does not refute a capacity argument that explicitly counts such families, a collective circuit classification, or a repair that changes denominator directions.
