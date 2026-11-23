# Full-Cube Unit Margins Do Not Force Active Rank Defect

## Statement

There is an explicit admissible three-head score on eighteen Boolean inputs with origin value one and signed margin at least one at every cube vertex. Among its active constraints, 108 have independent gradients in the 108 normalized numerator and denominator parameters. The retained point is nevertheless not a local minimum of the squared numerator norm.

This disproves a rank-defect assertion based on full-cube unit margins alone. It does not disprove an assertion that additionally requires a canonical minimum, and it proves no asymptotic head lower bound.

## Arithmetic construction

Use the integer arrays $U_{hi}$ and $b_{hi}$ in `integer-binary-fiber-18.json`, where $1\leq h\leq3$ and $1\leq i\leq18$. Every $b_{hi}$ is positive. Set

$$ B_h(x)=1+\sum_i b_{hi}x_i,\qquad A_h(x)=\sum_i U_{hi}x_i,\qquad P(x)=\sum_{h=1}^3 A_h(x)\prod_{g\neq h}B_g(x),\qquad D(x)=3\prod_{h=1}^3B_h(x). $$

Define

$$ T(x)=1+69300\frac{P(x)}{D(x)}=1+23100\sum_{h=1}^3\frac{A_h(x)}{B_h(x)}. $$

Each ratio is a genuine admissible head by the manuscript's positive-affine-ratio realization. The origin value is one. Label a vertex positive exactly when $P(x)\geq0$.

The following integer statement holds at every one of the 262,144 cube vertices:

$$ P(x)\geq0\quad\text{or}\quad34650P(x)\leq-D(x). $$

It is proved by complete kernel enumeration in `IntegerUnitCube.lean`. The enumeration splits a binary vertex into two nine-bit halves, checks the packed affine sums against their definitions, and checks all 512 choices of the lower half for each of the 512 upper halves. `IntegerUnitMargin.integer_gap` transfers the cached computation back to the original affine forms.

Since $D(x)\gt0$, the first alternative implies $T(x)\geq1$ and the second implies $T(x)\leq-1$. Thus every cube constraint has unit signed margin. `IntegerUnitMargin.full_cube_unit_margin` checks this deduction in Lean.

The minimum negative magnitude of $P/D$ is exactly $1/34650$. Its unique vertex is the binary encoding $92746$. There the three denominators are $25,22,21$, the three unscaled numerators are $-23,37,-16$, and $P=-1$. The zero layer has 128 vertices, including the origin. Consequently there are 128 active nonorigin constraints: 127 positive constraints and one negative constraint. These counts and the minimum are independently checked with exact integer arithmetic; the theorem about full-cube margins does not depend on the counts.

## Active rank

Take the 108 indices of the earlier integer fiber and replace index 53, counting from zero, by 92746. The other selected vertices lie on $P=0$. Therefore the new selected scores are positive one except for row 53, whose score is negative one. `UnitRank.active_scores` and `newIndices_injective` check these assertions.

For the unscaled numerator coefficients $U/3$, multiply each Jacobian row by $3\prod_hB_h^2$ to obtain an integer matrix $M$. The earlier matrix has determinant nine modulo 101. The new row is a linear combination of the old rows whose coefficient at row 53 is fourteen. Hence the replacement matrix $M'$ satisfies

$$ \det M'\equiv14\cdot9\equiv25\pmod{101}. $$

All 108 coefficients of that row combination are checked in `UnitRank.replacement_row`. The determinant identity is applied in `newCleared_det_ne_zero`. An independent calculation gives determinant 50,748 modulo 65,537 as well.

Passing from numerator coefficients $U/3$ to $23100U$ multiplies every denominator-parameter column of the Jacobian by 69,300 and leaves every numerator-parameter column unchanged. There are 54 columns of each kind. Thus the actual Jacobian determinant remains nonzero. `UnitRank.scaledJacobian_det_ne_zero` checks this final step. Multiplying rows by the corresponding labels also preserves independence.

## Exact descent and its significance

The rational vector $d\in\mathbb{Q}^{54}$ in `rescaled-binary-descent.json` has every coordinate in $[-1,1]$ and satisfies

$$ \sum_{h,i}U_{hi}d_{hi}=-\frac{8879174}{32593}\lt-1. $$

Keep the denominators fixed and change the normalized numerator coefficients from $23100U$ to $23100U+\varepsilon d$, where

$$ \varepsilon=\frac1{28839240}. $$

The independent verifier checks all 262,144 signed margin inequalities for this perturbed score with Python integers after clearing positive denominators. It also checks the exact identity

$$ \lVert23100U+\varepsilon d\rVert_2^2-\lVert23100U\rVert_2^2=46200\varepsilon\sum_{h,i}U_{hi}d_{hi}+\varepsilon^2\sum_{h,i}d_{hi}^2\lt0. $$

For fixed denominators, every signed margin is affine in the numerator coefficients. The entire segment between these two feasible points is therefore feasible. Strict convexity of the squared norm, or its displayed quadratic expansion, shows that every sufficiently small positive displacement along this segment decreases the norm. The retained point is not a local minimum.

The descent calculation is an independently verified rational certificate and the segment argument is a written proof. It is not presented as a Lean theorem. The full-cube margin theorem and active-rank theorem are kernel checked with only the standard foundational axioms.

## Remaining scope

Full-cube feasibility and full active rank can coexist in the exact model. A lower-bound argument that depends on minimum properties still needs a theorem about those properties, including unrestricted target-dependent denominators. This construction does not settle that theorem or the selected unboundedness target. No manuscript definition or target statement has changed.
