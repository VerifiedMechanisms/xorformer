# Jet rank alone does not measure exceptional complexity

## Scope

The generic radial theorem in `artifacts/power-saving-20261124/generic_radial_initial_degree.md` controls bounded limits once a squarefree derivative interpolation matrix has full rank. A proposed extension would stratify its rank-deficient locus and charge exceptional directions by their codimension. The simple rank-defect version of that proposal is false, including for strictly positive coherent directions.

This note gives a complete counterexample, distinguishes contact order from intrinsic initial-table complexity, and states the additional geometric information needed for a counting argument. It gives no improved unrestricted lower bound.

## A positive coordinate-line family

Fix $n\geq2$ and $H\geq2$. Choose positive real numbers $u_2,\ldots,u_n$ and pairwise distinct positive real numbers $\lambda_1,\ldots,\lambda_H$. Set

$$ c_h=(\lambda_h,u_2,\ldots,u_n). $$

For a squarefree monomial indexed by a nonempty subset $S\subseteq[n]$, let

$$ J_{S,(h,i)}=\mathbf 1_{i\in S}\prod_{j\in S\setminus\lbrace i\rbrace}c_{hj}. $$

These are exactly the coefficients of the derivative functional $P\mapsto\partial_iP(c_h)$ on the space of multilinear polynomials. For every degree truncation, the rank is at most $2n-1$. For every truncation including degree two, it is exactly $2n-1$.

**Upper bound.** When $i=1$, the displayed entry is independent of $\lambda_h$. When $i\neq1$, it is affine in $\lambda_h$. Hence the columns are contained in the span of one vector for coordinate one and two vectors for each other coordinate. There are $2n-1$ such vectors.

**Matching lower bound.** Put $y_1=x_1$ and $y_i=x_i-u_i$ for $i\neq1$. All of $y_1,y_i,y_1y_i$ are multilinear polynomials of degree at most two. On the coordinate line, $y_i=0$ for $i\neq1$. Derivative evaluation of $y_1$ isolates the common coordinate-one functional. Evaluation of $y_i$ isolates the constant coordinate $i$ functional, and evaluation of $y_1y_i$ isolates its coefficient of $\lambda_h$. Two distinct values of $\lambda_h$ distinguish the latter two functionals. Thus the $2n-1$ spanning vectors are independent. $\blacksquare$

All radial denominators

$$ B_h(t,x)=1+t\left(\lambda_hx_1+\sum_{i=2}^nu_ix_i\right),\qquad t\gt0, $$

are strictly positive on the full Boolean cube and have strictly positive slopes. The example lies inside the original admissible direction cone, not merely its boundary.

## The exact codimension inequality that fails

The space of ordered direction configurations has dimension $nH$. The displayed positive family has dimension $H+n-1$: its parameters are the $H$ separate values of $\lambda_h$ and the $n-1$ common coordinates. The parameterization is injective, and positivity together with pairwise distinctness describes an open subset of this parameter space.

Let $\mathcal R_r$ be the locus where the full squarefree derivative matrix has rank at most $r$. At $r=2n-1$, the preceding family implies

$$ \mathrm{codim}\mathcal R_{2n-1}\leq nH-H-n+1. $$

The tempting rank-defect estimate would instead require

$$ \mathrm{codim}\mathcal R_r\geq nH-r. $$

For $H\gt n$, these inequalities are incompatible, because

$$ nH-H-n+1\lt nH-2n+1=nH-r. $$

Consequently a rank drop of $nH-r$ cannot simply be charged as that many lost free parameters. A generic-matrix determinantal codimension formula does not apply to this structured derivative matrix.

The obstruction is compatible with a finer capacity bound. On the face $x_1=0$ all denominators coincide. On the face $x_1=1$ they form a one-parameter family with common remaining statistic $\sum_{i=2}^nu_ix_i$. This special family is controlled by restriction and pencil arguments; its large kernel does not produce unrestricted sign capacity. The point is that this additional structure must be proved and used, rather than inferred from rank deficiency alone.

## Raw contact order is also insufficient

There is a separate reparameterization obstruction. Fix affine forms $A,C,D$ with $AD$ not identically zero on the cube, and an arbitrary integer $M\geq2$. Choose $C$ with strictly positive slopes. For all sufficiently small $t\gt0$, both $1+tC$ and $1+tC+t^MD$ have strictly positive slopes and positive cube values, provided $M\geq2$. Their difference gives the exact identity

$$ \frac{A}{1+tC}-\frac{A}{1+tC+t^MD}=\frac{t^MAD}{(1+tC)(1+tC+t^MD)}. $$

The score has arbitrarily high order $M$ at $t=0$, even though its first nonzero table is the fixed quadratic table $AD$. All heads remain admissible for small positive $t$ and the numerator coefficients can have arbitrary signs. Thus an upper bound on contact order in a chosen time parameter cannot follow from the number of heads or the dimension of a direction stratum. One must use an invariant such as the weighted jet span after removing redundant time parameterizations.

This example concerns vanishing of a whole score family. It neither proves a small optimal relative margin for its Boolean target nor says that every representation of that target is ill-conditioned.

## What a useful replacement would have to prove

A viable stratification would have to include at least three kinds of data: denominator faces, relations between distinct limiting head features on the Boolean cube, and the intrinsic jet directions that resolve those relations. Repeated heads, coordinate-line families, common pencils, and algebraic curves with full affine span must all be covered.

The needed conclusion is a bound on the number of Boolean signs realized by the union of those charts. For example, it would suffice to cover all original width $H$ sign tables by weighted polynomial charts whose total logarithmic chart cost and sign-count cost are $O(nH\log n)$ at $H=2^n/\mathrm{poly}(n)$. The chart parameter count must account for redundant parameters like those in the coordinate-line family. The weighted degrees must account for nested rates like $t^M$ without charging $M$ directly. Neither such a cover nor its required total cost is established here.

This formulation is stronger than a statement about one badly conditioned representation. It would count every target obtainable at the original width, including all alternative representations, arbitrary real coefficients, and signed cancellation.

## Verification boundary

`formalization/HeadComplexity/Research/CoordinateLineJetRank.lean` defines the complete derivative matrix, proves its explicit factorization through two columns per input coordinate, and proves the sharper rank bound $2n-1$ by removing the identically zero column. The declarations are `HeadComplexity.CoordinateLineJetRank.derivativeMatrix_factor` and `HeadComplexity.CoordinateLineJetRank.derivativeMatrix_rank_le_sub_one`. It also proves positivity of every coordinate and injectivity when the selected coordinate parameters are injective.

The matching rank lower bound, dimension and codimension calculations, contact-order example, and required chart-cost formulation are written mathematics. No finite computation is used for those conclusions. None of these statements changes the original model or settles either requested unrestricted target.
