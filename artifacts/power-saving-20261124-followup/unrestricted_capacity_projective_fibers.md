# Capacity from projective denominator observations

## Kernel-checked statement

Write $N=2^n$, $d=n+1$, and $p=1+d^4$. Consider all strict Boolean truth tables represented by any positive number of original admissible heads, with arbitrary real numerators, bias, and signed cancellation. Retain those representations for which the full denominator observation vector

$$ B(x)=(B_1(x),\ldots,B_H(x))\in\mathbb R_{\gt0}^H $$

assumes at most $K$ distinct positive rays as $x$ ranges over the full cube. The denominators, ray classes, and head count can all depend on the target.

For $K\geq1$, $p\leq N^2$, and $dK\leq N$, the number of these truth tables is at most

$$ \left(\frac{4eN^2}{p}\right)^p\left(\frac{4eN}{dK}\right)^{dK}. $$

The precise declarations are `HeadComplexity.ProjectiveFiberCapacity.card_originalFunctions_le` and `mem_represented_of_original` in `formalization/HeadComplexity/Research/ProjectiveFiberCapacity.lean`. A simpler integral bound is

$$ 2^{(2n+4)(1+(n+1)^4)+(n+4)(n+1)K}. $$

It is kernel checked as `card_originalFunctions_le_pow`. The declaration `card_originalFunctions_le_half_tables` gives the $2^{N/2}$ bound whenever its explicit exponent budget holds.

This is a restricted class count, not a bound for unrestricted worst-case head complexity. No access theorem placing every narrow truth table in this class is asserted. The property asks for one representation with few projective fibers; it does not classify a target by one selected badly conditioned representation.

## Affine scores after positive rescaling

Fix one reference head $h_0$. On a projective class, choose a representative vertex $y$. For every $x$ in that class,

$$ \frac{B_h(x)}{B_{h_0}(x)}=\frac{B_h(y)}{B_{h_0}(y)}. $$

For the original score $S(x)=c+\sum_h A_h(x)/B_h(x)$, multiplication by the positive reference denominator therefore gives

$$ B_{h_0}(x)S(x)=cB_{h_0}(x)+\sum_h A_h(x)\frac{B_{h_0}(y)}{B_h(y)}. $$

This is affine in $x$ on the entire class. Its sign is the sign of $S(x)$. In particular the original bias is handled exactly, by the affine term $cB_{h_0}(x)$.

The declaration `exists_projective_fiber_affine_score` proves this identity using the exact affine numerator and denominator coefficients of genuine `FracAtom` heads. `denominator_pos` proves positivity on every cube point. The original coefficients are neither rounded nor bounded, and no cancellation assumption is imposed.

For a fixed partition with at most $K$ classes, the resulting class of signs has $dK$ unrestricted affine coefficients. The degree-one Warren theorem gives the second factor in the count.

## Counting all ray partitions without charging the head count

Set $u_x=(1,x)$ and write the denominator coefficient matrix as $b_{hi}$, so $B_h(x)=\sum_i b_{hi}u_{xi}$. Two observation vectors are on the same ray exactly when every two by two minor vanishes:

$$ B_h(x)B_k(y)-B_h(y)B_k(x)=0\qquad\text{for every }h,k. $$

Define the $d^2$ fixed wedge features

$$ v_{ij}(x,y)=u_{xi}u_{yj}-u_{yi}u_{xj}. $$

Each displayed minor is a linear form in these features, with coefficient $b_{hi}b_{kj}$. The sum of squares of all minors is consequently a quadratic form $v^{\top}Gv$ on this fixed feature space. Allow all $d^4$ matrix entries of $G$ to vary independently; this enlarges the family.

On the finite set of pairs $(x,y)$, choose a positive threshold $\varepsilon$ smaller than every nonzero squared-minor sum. The strict sign of $\varepsilon-v^{\top}Gv$ then records exactly the ray-equivalence relation. This polynomial is linear in the $1+d^4$ free parameters and is tested on $N^2$ row pairs. Warren gives the first factor.

`gram_identity`, `denominatorWedge_dot`, and `observationRelation_mem` check these steps. The proof charges unlabeled equivalence relations and chooses one canonical class coding for each relation. It does not multiply by $K!$ or by the number of arbitrary class labels.

A smaller written parameterization uses the ordinary $d$ by $d$ Gram matrix and the quadratic expression

$$ \|B(x)\|^2\|B(y)\|^2-\langle B(x),B(y)\rangle^2. $$

That would reduce the partition overhead from $O(n^5)$ to $O(n^3)$. The implemented linear parameterization is already negligible relative to $N$ and avoids introducing an additional Gram-determinant identity. The sharper overhead is not claimed as a Lean declaration here.

## Relevance and limitation

At either benchmark width, a hypothetical reduction to at most $K\leq H/D$ projective query classes, with $D=\exp(\sqrt n)$ or $D=\exp(n/\log n)$, would make this class extremely small. The theorem remains valid even if the number of heads used after such a reduction is unbounded, since its count depends only on the projective observation classes.

The projective condition is strictly more flexible than equality of denominator observations. For example, all denominators can be positive multiples of a single affine form whose values are distinct on the whole cube. There are then $N$ exact observation fibers but only one projective fiber, and every resulting score has the sign of one affine function after denominator clearing.

The unresolved inverse statement is that every narrow target should admit either a counted structured representation or sufficiently few projective observation classes. Finite Boolean moment cancellation alone has not been shown to imply either alternative. Generic-rank heuristics for the moment evaluation matrix are insufficient: the exceptional configurations are precisely the ones requiring a uniform argument.

## Verification

The module build and the transitive audit of eighteen declarations are saved in `projective-fiber-build.txt` and `projective-fiber-axioms.txt`. The audit reports only `propext`, `Classical.choice`, and `Quot.sound`. The original definitions of heads, admissibility, computability, and worst-case head complexity are unchanged.
