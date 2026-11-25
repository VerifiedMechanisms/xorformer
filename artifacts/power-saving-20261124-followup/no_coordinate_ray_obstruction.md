# A full-dimensional unit-gap branch without a coordinate ray

## Exact obstruction

A fixed actual Boolean basis can have a strictly positive, full-cube unit-gap feasible branch whose closed denominator coefficient cone contains no coordinate ray. Thus one cannot prove the proposed denominator balancing lemma by assigning every feasible branch to a vertex of the coefficient simplex.

This counterexample does **not** refute inverse-polynomial balancing of the denominator's constant coefficient. The separate branch-count bound in `one_head_branch_packing.md` remains conditional on such balancing. Even that bound would need a further joint-head argument before it could improve unrestricted xorformer capacity.

Let $z(x)=(1,x_1,\ldots,x_{10})$. Number cube vertices lexicographically from zero, with the first coordinate the most significant bit. Select the eleven basis vertices and their prescribed unit values

$$ I=(67,150,196,256,284,358,519,554,568,708,886),\qquad g=(-1,-1,1,1,-1,-1,1,1,-1,-1,1). $$

Let $Z$ be the matrix with rows $z(x)$ at these vertices and put $T=Z^{-1}\mathrm{diag}(g)Z$. The determinant of $Z$ is one, so this basis is affinely independent. The following integer numerator and strictly positive denominator coefficients obey $a=Tb$:

$$ b=(2,2,2,6,2,12,2,2,11,2,2),\qquad a=(1286,-44,-1282,-1944,304,-864,110,-508,375,150,-1748). $$

Set $f(x)=\mathrm{sign}(z(x)a)$. On every cube vertex,

$$ f(x)z(x)a\geq z(x)b\gt0. $$

Equality holds exactly at the eleven selected basis vertices. The minimum slack at all other vertices is two. In particular, the ratio $z(x)a/z(x)b$ is one admissible original head, its absolute value is at least one throughout the cube, and its values at the selected basis are exactly $g$.

## Failure of every coordinate ray

Consider the closed fixed-label feasible cone

$$ \mathcal C_f=\lbrace u\in\mathbb R_{\geq0}^{11}:f(x)z(x)Tu\geq z(x)u\text{ for every cube vertex }x\rbrace. $$

For the coordinate rays $e_j$, in order $j=0,\ldots,10$, choose the witness vertices

$$ (858,782,270,858,858,21,21,21,270,782,5). $$

At the corresponding witness for every $j$, the exact violation is

$$ f(x)z(x)Te_j-z(x)e_j=-2. $$

Therefore no $e_j$ belongs to $\mathcal C_f$. Positive homogeneity excludes every nonzero point of every coordinate ray. There is no alternate numerator that repairs this failure while retaining the prescribed basis values: affine independence forces that numerator to be $Te_j$.

This does not result from a branch supported only on a lower-dimensional boundary. The eleven basis inequalities are identities for every $u$. At the displayed $b$, every other inequality has strictly positive slack and every coefficient of $b$ is strictly positive. By continuity of the finitely many linear inequalities, an open Euclidean neighborhood of $b$ lies in $\mathcal C_f$ and in the positive coefficient orthant.

## Verification and scope

`HeadComplexity/Research/FeasibleConeNoCoordinateRay.lean` kernel-checks the positive original atom, its full-cube unit gap, its basis values, basis injectivity, and the exclusion of every coordinate ray. The principal declarations are `atom_full_gap`, `atom_basis_values`, `basis_affine_injective`, and `no_coordinate_ray`, all in namespace `HeadComplexity.FeasibleConeNoCoordinateRay`.

The targeted `lake build HeadComplexity.Research.FeasibleConeNoCoordinateRay` passed with 3226 jobs. The all-declaration audit checked 65 theorem declarations, and the five public `#print axioms` checks list only `propext`, `Classical.choice`, and `Quot.sound`. Logs are saved beside this note.

The saved `no-coordinate-ray-exact.json` contains the entire integer matrix $T$. The independent standard-library checker `check_no_coordinate_ray.py` verifies its basis equation, determinant, all 1024 unit-gap inequalities, the exact contact set, and all eleven violations using integer and rational arithmetic. The exact-contact and open-neighborhood assertions above are written consequences of this finite certificate; they are not advertised as additional Lean declarations.

The exploratory floating search is preserved separately in `search_balance_vertex_cone.py` and `balance-vertex-cone-sparse-n10.json`. Its output is not used as a proof.

The remaining balancing question is whether every nonempty positive branch admits some $u$ with $u_0/\sum_j u_j\geq n^{-C}$ for a fixed absolute $C$. This example only invalidates the stronger coordinate-ray recursion. Moreover, choosing a separate Boolean basis for every head costs approximately $n^2H$ bits. A useful unrestricted capacity argument would have to choose contacts jointly and control arbitrary residual targets under signed cancellation, not merely multiply one-head unit-basis counts.
