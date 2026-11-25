# The actual full-cube norm optimization problem

## Exact norm constraints

Write $A(x)=a_0+\sum_i a_i x_i$ and $B(x)=b_0+\sum_i b_i x_i$, and assume $B(x)\gt0$ on the entire Boolean cube. For any real $m$,

$$ \left\lVert\frac AB\right\rVert_\infty\leq m \quad\Longleftrightarrow\quad a_0-mb_0+\sum_i\max\lbrace a_i-mb_i,0\rbrace\leq0\quad\text{and}\quad -a_0-mb_0+\sum_i\max\lbrace-a_i-mb_i,0\rbrace\leq0. $$

Indeed, multiply the two absolute-value inequalities by the positive denominator. The maximum of an affine form on the cube is its constant coefficient plus the sum of its positive variable coefficients. This verifies the norms on every cube vertex, without replacing them by coefficient norms.

If $b_i\geq0$ and $m\geq0$, the two residual-maximizing vertices can be chosen with disjoint supports: the inequalities $a_i-mb_i\gt0$ and $-a_i-mb_i\gt0$ cannot both hold. There are at most $3^n$ such pairs of selected residual faces for one positively oriented head. This observation counts the norm constraints, not the target-contact constraints.

The equivalence and the disjointness statement are kernel checked in `HeadComplexity.Research.FullCubeNormOptimization` as `ratio_norm_bound_iff` and `residual_positive_parts_disjoint`. The equivalence allows arbitrary affine numerator coefficients and arbitrary denominator coefficients subject only to full-cube positivity, so it applies to both admissible coherent orientations.

## Optimal redistribution of constants

For an original score $S=b+\sum_h\phi_h$, let $l_h=\min_x\phi_h(x)$ and $u_h=\max_x\phi_h(x)$. For arbitrary constants $t_h$, replace each head by $\phi_h-t_h$ and the bias by $b+\sum_h t_h$. This preserves the score and admissibility exactly.

The smallest possible amplitude under all such redistributions is

$$ K=\max\left\lbrace b+\sum_hu_h,-b-\sum_hl_h\right\rbrace. $$

To prove the lower bound, the amplitude of every redistributed representation is at least each of the two displayed interval endpoints. For attainment, set $t_h=(l_h+u_h)/2$. Each centered head has norm $(u_h-l_h)/2$, so the resulting amplitude is

$$ \left|b+\sum_h\frac{l_h+u_h}{2}\right|+\sum_h\frac{u_h-l_h}{2}=K. $$

The earlier `MidrangeMarginCentering.lean` proved that centering does not increase amplitude. The new declarations `centered_amplitude_eq_intervalBudget` and `optimal_constant_redistribution` prove its exact value and optimality against every constant redistribution. All heads in these declarations are the original `FracAtom`s. No definition of relative margin or head complexity changes.

For unit signed constraints $f(x)S(x)\geq1$, minimizing $K$ is therefore the actual relative-margin optimization problem after constant redundancy has been removed. A minimum of a squared numerator coefficient norm does not establish a minimum of this objective.

## Smooth first-order conditions

Here is a written analytic calculation, with its final signed-gap identity kernel checked. Suppose all denominators and their coherent slopes are strictly inside the admissible domain. Suppose also that the upper branch $K=b+\sum_hu_h$ strictly dominates the lower branch and that each head has a unique maximizing vertex $p_h$. These assumptions make this branch of the objective smooth locally. The lower branch has the analogous calculation after reversing signs.

Let $\lambda_x\geq0$ be unit-constraint multipliers supported on active rows, and put $\mu_x=\lambda_x f(x)$. Bias stationarity gives $\sum_x\mu_x=1$. With $z_x=(1,x)$, numerator and denominator stationarity for head $h$ give

$$ \sum_x\frac{\mu_xz_x}{B_h(x)}=\frac{z_{p_h}}{B_h(p_h)},\qquad \sum_x\frac{\mu_x\phi_h(x)z_x}{B_h(x)}=\frac{u_hz_{p_h}}{B_h(p_h)}. $$

Consequently the nonnegative head gaps $g_h(x)=u_h-\phi_h(x)$ satisfy

$$ \sum_x\frac{\mu_xg_h(x)z_x}{B_h(x)}=0. $$

The declaration `stationary_gap_identity` verifies this implication algebraically. It does not assert a multiplier-existence or constraint-qualification theorem.

The weights in this identity are signed. The nonnegativity of $g_h$ and $B_h$ does not permit a sum-of-nonnegative-terms argument. Taking affine test forms $B_h$ and $A_h$ also gives $\sum_x\mu_xg_h(x)=\sum_x\mu_xg_h(x)^2=0$, but the same sign obstruction remains.

Equivalently, for each head define a shifted logarithmic master function

$$ F_h(v)=\sum_x\mu_x\log(z_x\cdot v)-\log(z_{p_h}\cdot v). $$

At its denominator vector $b_h$, stationarity gives $\nabla F_h(b_h)=0$ and $\nabla^2F_h(b_h)a_h=0$. Homogeneity already gives $\nabla^2F_h(b_h)b_h=0$. Thus a nonconstant head supplies another Hessian-kernel direction, but this is a signed master function, not a concave positive likelihood. The explicit positive-domain signed-gradient counterexample in `PositiveReciprocalGradient.lean` explains why positive-weight uniqueness cannot be imported.

## A stronger test after duplicating a head

There is a useful distinction between a local minimum at width $H$ and one that remains a local minimum after every head is duplicated at half weight. Assume the smooth hypotheses above and linearly independent active unit-constraint gradients. The duplicated point retains this row independence, so the usual second-order necessary condition uses the same unique multiplier vector.

For one head, write $u=u_h$, $A=A_h$, $B=B_h$, and $g=u-A/B$. Choose arbitrary affine forms $D,E$ with $E(p_h)=0$. Put $C=uD+E$, and replace the head by the two half-weight heads with numerators $A\pm\varepsilon C$ and denominators $B\pm\varepsilon D$. For sufficiently small $\varepsilon$, both heads remain admissible, and their common maximum stays at $p_h$ with value $u$. The averaged score is

$$ \frac12\left(\frac{A+\varepsilon C}{B+\varepsilon D}+\frac{A-\varepsilon C}{B-\varepsilon D}\right)=\frac AB-\varepsilon^2\frac{gD^2+ED}{B^2-\varepsilon^2D^2}. $$

The first-order score and objective changes cancel on every row. Second-order optimality at the duplicated point therefore requires

$$ \sum_x\frac{\mu_xg(x)D(x)^2}{B(x)^2}+\sum_x\frac{\mu_xE(x)D(x)}{B(x)^2}\geq0. $$

Scaling $E$ by every real number forces its mixed coefficient to vanish. Take $E_i(x)=z_{x,i}-z_{p_h,i}B(x)/B(p_h)$ and $D(x)=z_{x,j}$. Numerator stationarity then yields

$$ \sum_x\frac{\mu_xz_{x,i}z_{x,j}}{B(x)^2}=\frac{z_{p_h,i}z_{p_h,j}}{B(p_h)^2}\qquad\text{for every }i,j. $$

Thus the entire Hessian of $F_h$ vanishes at a smooth regular local minimum that survives duplication, a stronger requirement than having the numerator in its kernel. The algebraic implication from the displayed second-order inequality is kernel checked in `split_second_moment`; the analytic local-minimum and constraint-qualification bridge is a written argument, not hidden in that declaration's hypotheses.

This does not yet repair a narrow representation. A strict improvement after doubling can be arbitrarily small, and an optimum at width $2H$ may use all $2H$ heads. No bound is proved on how many doublings are needed, on their quantitative improvement, or on the truth tables whose best comparable-width margin stays small. A theorem that merely excludes generic duplication-stable local minima does not establish the required all-representations quantifier.

## Numerical audit of the inherited local minimum

The independent branch `origin/ar/7485202da367` contains a certified eighteen-variable, three-head strict local minimum for a squared numerator coefficient norm, with 108 independent nonorigin unit contacts. Its written scope is explicit: it is not a global minimum or an actual full-cube norm optimum.

Evaluating the new interval budget at its rational center gives approximately $151290.486$, with the upper branch exceeding the lower branch by about $50.874$. The formal unit-root certificate lies within $10^{-40}$ of that center, but the following test is only floating-point evidence. Solving the actual-budget stationarity system gives 48 negative nonorigin multipliers and a negative origin multiplier. Therefore this computation does not furnish a local-minimum certificate for the actual norm objective. It does not rule out other actual-norm local minima.

`probe_actual_norm_dual.py` and `actual-norm-dual-n18-h3.json` record the computation. The input source and hash are included in the report. The exact norm identities and algebraic implications above do not depend on this computation.

## Verification scope

`FullCubeNormOptimization.lean` contains the kernel-checked finite identities and conditional algebraic implications. `FullCubeNormAudit.lean` and `full-cube-norm-axioms.txt` record their transitive axioms; only the standard foundational axioms occur. `full-cube-norm-build.txt` records the module build. No unrestricted power-saving lower bound follows from this checkpoint.
