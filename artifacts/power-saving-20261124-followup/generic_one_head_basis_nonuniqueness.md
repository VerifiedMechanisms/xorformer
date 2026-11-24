# Open feasible branches for one actual active basis

## Statement and scope

One admissible original head can have two different full Boolean truth tables on two nonempty open sets of positive denominator coefficients, while retaining the same values in $\lbrace-1,+1\rbrace$ on one full affine basis of actual Boolean observations. Thus restricting a proposed uniqueness theorem to generic feasible branches does not repair it, even at width one.

This is a branch-count obstruction, not an obstruction to margin repair. Both explicit representations below have small integer coefficients and good relative margin. Two branches are compatible with the sought bound on the total number of feasible branches at the critical width.

The exact declarations are in `formalization/HeadComplexity/Research/GenericOneHeadBasisNonuniqueness.lean`, namespace `HeadComplexity.GenericOneHeadBasisNonuniqueness`. The original model and worst-case definitions are unchanged.

## Exact data

List the seven-bit cube in increasing lexicographic order, with the first bit most significant. Select the ordered eight rows

$$ I=(98,117,50,30,123,124,119,67),\qquad g=(-1,-1,1,-1,-1,1,1,1). $$

For $z_x=(1,x_1,\ldots,x_7)$, let $Z$ have these eight rows. Its determinant is $-1$, so the actual observations form a full affine basis. Put $T=Z^{-1}\mathrm{diag}(g)Z$. The two positive denominator vectors and their numerator vectors $a^{(k)}=Tb^{(k)}$ are

$$ \begin{aligned} b^{(0)}&=(1,1,1,1,1,1,4,1),\cr a^{(0)}&=(-53,117,-87,131,-61,-41,16,-73),\cr b^{(1)}&=(1,1,1,1,1,3,1,1),\cr a^{(1)}&=(-53,107,-75,115,-51,-35,17,-67). \end{aligned} $$

Each score $S_k(x)=(z_xa^{(k)})/(z_xb^{(k)})$ is one admissible original head, because the constant and every slope of its denominator are strictly positive. On the common basis, $S_k(x_j)=g_j$. On the entire cube, $|S_k(x)|\geq1$.

The two label tables differ exactly at lexicographic vertex $17=(0,0,1,0,0,0,1)$. The respective numerators there are $5$ and $-5$, and both denominators equal $3$, so the respective scores are $5/3$ and $-5/3$.

The integer residual $|z_xa^{(k)}|-z_xb^{(k)}$ is at least $2$ outside the nine rows

$$ J=(30,50,67,72,98,117,119,123,124). $$

For each $x$ in $J$, the identity $z_xT=\sigma_xz_x$, with $\sigma_x\in\lbrace-1,+1\rbrace$, holds for every denominator vector. All eight basis rows belong to $J$; the extra structural row is $72$.

## Open feasible neighborhoods

Write $f_k(x)=\mathrm{sign}(S_k(x))$. Define

$$ U_k=\lbrace b\in\mathbb R^8: b_i\gt0 \text{for every }i,\quad f_k(x)z_xTb-z_xb\gt0 \text{for every }x\notin J\rbrace. $$

Each $U_k$ is open, being a finite intersection of strict linear inequalities. The explicit point $b^{(k)}$ belongs to $U_k$. At a structural row, the signed residual is identically zero for all $b$. Therefore every $b\in U_k$ gives an admissible original one-head ratio $z_xTb/(z_xb)$ satisfying the same full-cube unit inequalities and the same full label table $f_k$.

The common unit values on the selected basis hold identically in $b$, because $ZT=\mathrm{diag}(g)Z$. The two open neighborhoods are disjoint, since their labels at vertex $17$ are opposite. Their intersections with the normalization slice $b_0=1$ are also relatively open and nonempty, so the distinction survives removal of the common scale parameter.

The Lean declarations `basis_affine_injective` and `basis_ratio_injective` establish full basis rank by explicit linear-combination certificates. `basis_identity`, `structural_identity`, `base_strict_residual`, `neighborhood_isOpen`, `neighborhood_signed_gap`, `neighborhood_basis_values`, and `two_open_feasible_branches` prove the stated algebraic and topological claims. `atom` and `atom_eval` connect every neighborhood point to the original admissible `FracAtom` definition.

## Failure of the proposed Minkowski decomposition

The earlier dimension-six example in `feasible_basis_nonuniqueness.md` also rules out a tempting convex decomposition lemma. For fixed labels $f$, set

$$ P_f(b)=\lbrace a\in\mathbb R^{n+1}: f(x)z_xa\geq z_xb \text{for every cube vertex }x\rbrace. $$

The proposed identity was

$$ P_f(b)=\sum_{i=0}^n b_iP_f(e_i)\qquad\text{for every coefficient vector }b\gt0. $$

Here the right side denotes the Minkowski sum of the positively scaled polyhedra. One inclusion always holds by adding the inequalities. The reverse inclusion fails.

Use the dimension-six second branch, with denominator $b=(1,1,4,1,1,1,1)$ and numerator $a=(15,-13,-28,-13,-17,-13,19)$. Let $f$ be its full label table. This point lies in $P_f(b)$, with equality at the seven common affine-basis rows. If $a=\sum_i b_i a^{(i)}$ with $a^{(i)}\in P_f(e_i)$, then the nonnegative residuals of each component must vanish on every basis row: their positive weighted sum is zero there. In particular $a^{(0)}$ must be the unique affine interpolant to the common unit labels,

$$ L(x)=3-2x_1-4x_2-2x_3-2x_4-2x_5+2x_6. $$

At $v=(0,0,0,1,0,0)$, however, $f(v)=-1$ and $L(v)=1$. The required inequality for $P_f(e_0)$ would read $-1\geq1$, which is false. This is a written corollary of the kernel-checked exact dimension-six data; no convex-set identity is assumed by any Lean theorem.

## Verification and the remaining question

`check_generic_one_head_basis.py` verifies all $128$ vertices, the exact affine determinant, the structural-row identities, the strict residuals, and the unique disagreement using integers and rational arithmetic. Its output is `generic-one-head-exact.json`. The computation corroborates the Lean proofs; it is not used as an axiom. The target build passed with 3226 jobs. The all-declaration audit checked 59 declarations and found only `propext`, `Classical.choice`, and `Quot.sound`; the stored build and axiom logs accompany this note.

A useful replacement must bound the number of feasible extensions, rather than assert uniqueness. At critical width, the missing count has to retain the full Boolean observation constraints and reduce the additional entropy to $O(nH\log n)$, up to the already controlled sample-selection term. The one-head examples prove neither a matching branch lower bound nor an upper bound of this size.
