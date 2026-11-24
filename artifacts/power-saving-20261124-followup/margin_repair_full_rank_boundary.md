# Tiny optimal margin does not imply a feature-rank defect

## The attempted implication

A possible route to counting small-margin truth tables is to argue that a representation with tiny optimal relative margin must lie near a linear dependence among its head feature columns. One could then try to classify those dependencies into a small number of denominator clusters.

The implication fails even for one admissible head. The example below has a uniformly invertible feature submatrix, no collision between heads, and an exactly computed optimum margin tending to zero. The degeneration occurs at the boundary of the target orthant. It does not occur at a loss of column rank.

The exact margin upper bound, its full-cube attaining witness, and the original admissibility bridge are kernel checked in `formalization/HeadComplexity/Research/FullRankMarginDegeneration.lean`. The feature-matrix and limiting-space discussion is a written proof. No unrestricted lower bound is claimed.

## One denominator and one truth table

Use three Boolean coordinates and write $k=x_1+x_2+x_3$. Fix $\varepsilon\gt0$ and the admissible denominator

$$ B_\varepsilon(x)=\varepsilon+k. $$

Its constant and every slope are strictly positive. Let the target $F$ be negative at weights zero and one, and positive at weights two and three. This is three-bit majority.

Consider all scores

$$ S(x)=b+\frac{a+c_1x_1+c_2x_2+c_3x_3}{\varepsilon+k}. $$

The bias and every affine numerator coefficient are arbitrary reals. Write

$$ M=|b|+\left\|\frac{a+\sum_i c_ix_i}{B_\varepsilon}\right\|_\infty,\qquad m=\min_xF(x)S(x),\qquad\gamma=m/M. $$

**Theorem 1.** The maximum relative margin over all strict representations of three-bit majority using this denominator is exactly

$$ \gamma_{\mathrm{best}}(\varepsilon)=\frac{\varepsilon}{4+3\varepsilon}. $$

The same upper bound holds if arbitrary copies of the fixed denominator are allowed and all numerators and the bias are refitted.

### Proof. Upper bound

Absorb the bias into the numerator and write

$$ S(x)=\frac{\alpha+\beta_1x_1+\beta_2x_2+\beta_3x_3}{\varepsilon+k}. $$

The triangle inequality gives $\|S\|_\infty\leq M$. At the zero vertex the score is negative, so $\alpha\lt0$, and

$$ -\alpha\leq\varepsilon M. $$

The negative labels at $e_1,e_2$ and positive label at $e_1+e_2$ give

$$ \alpha+\beta_1\leq-m(1+\varepsilon),\qquad \alpha+\beta_2\leq-m(1+\varepsilon),\qquad \alpha+\beta_1+\beta_2\geq m(2+\varepsilon). $$

Adding the first two inequalities and subtracting the third yields

$$ m(4+3\varepsilon)\leq-\alpha\leq\varepsilon M. $$

Since $M\gt0$, division proves the upper bound. For repeated copies, first combine all numerators. The original amplitude sum is at least the norm of the combined head, so the same inequality applies.

### Proof. Attainment

Set $b=0$ and use the symmetric numerator

$$ A_\varepsilon(x)=\varepsilon\left(-1+\frac{3+2\varepsilon}{4+3\varepsilon}k\right). $$

Its scores at weights zero, one, two, and three are respectively

$$ -1,\qquad-\frac{\varepsilon}{4+3\varepsilon},\qquad\frac{\varepsilon}{4+3\varepsilon},\qquad\frac{\varepsilon(5+3\varepsilon)}{(4+3\varepsilon)(3+\varepsilon)}. $$

The last quantity lies between $\varepsilon/(4+3\varepsilon)$ and $1$. All other absolute values are at most one. Therefore the full-cube head norm is exactly one, and the smallest signed score is exactly $\varepsilon/(4+3\varepsilon)$. This attains the upper bound. $\blacksquare$

## A uniformly invertible normalized feature matrix

Parameterize a head by its values $v_0$ at the zero vertex and $v_i$ at the three singleton vertices. The exact affine-numerator interpolation formula is

$$ \phi_\varepsilon(x)=\frac{\varepsilon(1-k)v_0+(1+\varepsilon)\sum_i x_iv_i}{\varepsilon+k}. $$

At the zero vertex, cancel the common positive factor to get $\phi_\varepsilon(0)=v_0$. At a singleton $e_i$, the formula gives $\phi_\varepsilon(e_i)=v_i$. Thus the four feature columns corresponding to $v_0,v_1,v_2,v_3$ contain an identity submatrix on these four input rows for every $\varepsilon\gt0$.

The remaining rows have finite limits as $\varepsilon\to0$. The limiting feature map is

$$ \phi_0(0)=v_0,\qquad \phi_0(x)=\frac1k\sum_i x_iv_i\quad(k\gt0). $$

Its same four-row submatrix is again the identity. The feature matrices have rank four throughout and at the limit. In Euclidean norm their smallest singular value is at least one, because the identity rows alone contribute the squared norm of the coefficient vector. All entries remain bounded as $\varepsilon\to0$. The constant table is already in this span, obtained by setting every $v_i$ and $v_0$ equal to one; separately adding the bias creates no new direction.

Nevertheless majority has no strict representation in the limiting space. Its negative singleton labels require each $v_i\lt0$, while the score at a positive pair would be $(v_i+v_j)/2\lt0$. The normalized maximizing scores instead converge to the nonzero weak representative which equals $-1$ at the zero vertex and zero everywhere else.

## What this rules out, and what it leaves open

This example rules out the implication that small optimal margin, even after all linear coefficients are optimized, forces loss or near-loss of feature-column rank in a compact head chart. It also rules out a proof which only stratifies by maximal minors of the feature matrix and treats full rank as sufficient for strict sign stability.

There is no obstruction to repairing this truth table with a different denominator. Taking $\varepsilon=1$ in the explicit construction gives a genuine one-head representation of the same majority table with relative margin $1/7$. Thus the example is not a counterexample to a width-preserving repair that may change heads.

A cluster or degeneration count must also control the target orthants reached through vanishing *coordinate* margins, including weak limiting tables with zeros. Full column rank and a bounded inverse on selected rows do not supply that control. The missing argument is a quantitative count of the additional strict label vectors admitted near these boundary configurations, uniformly over every target-dependent denominator family.

## Lean verification boundary

The declaration `HeadComplexity.FullRankMarginDegeneration.margin_upper` proves the upper bound with arbitrary numerator coefficients and bias. Its norm hypothesis only asks that $M$ bound the absolute full score at the zero vertex, so the required original head-amplitude norm satisfies a stronger hypothesis than needed. The signed margin is required at every cube vertex.

The declaration `optimal_full_cube_bounds` proves the displayed numerator has full-cube norm at most one and signed margin at least $\varepsilon/(4+3\varepsilon)$. The declarations `optimal_at_zero` and `optimal_at_singleton` give equality for the norm and minimum margin. The declaration `score_has_genuine_atom` realizes every displayed positive-denominator ratio by an actual `FracAtom 3`.

All these declarations have transitive axiom output `[propext, Classical.choice, Quot.sound]`. They do not assert that a fixed denominator's optimum is the optimum over other denominator choices. The example with $\varepsilon=1$ is exactly such a different choice.
