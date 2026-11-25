# A boundary obstruction to coefficient-box packing

## The proposed reduction

For an actual one-head unit-contact basis, let $Z$ be its invertible Boolean affine evaluation matrix, $g$ its contact labels, and $T=Z^{-1}\mathrm{diag}(g)Z$. If $b$ is a positive affine denominator coefficient vector, its forced numerator is $a=Tb$. A full-cube unit gap gives

$$ |z(x)\cdot a|\geq z(x)\cdot b\qquad\text{for every Boolean }x. $$

Consequently the open axis-aligned coefficient box centered at $a$ with coordinate radii $b_i$ lies entirely in one strict linear-threshold chamber. Indeed, every perturbation satisfying $|\delta_i|\lt b_i$ has $|z(x)\cdot\delta|\lt z(x)\cdot b$. Distinct full truth tables therefore give disjoint boxes.

An actual Boolean matrix $Z$ has integral determinant of absolute value at least one. Cauchy-Binet and the complementary-minor identity bound every exterior power of $T$ by $\exp(O(n\log n))$. This suggests a packing argument that uses collective singular-value expansion instead of the largest condition number in every direction.

The following exact counterexample shows why that suggestion needs an additional Boolean-specific ingredient.

## A fixed involution with infinitely many disjoint boxes

Take

$$ T=\begin{pmatrix}1&4\cr0&-1\end{pmatrix},\qquad T^2=I,\qquad b(t)=(t,1-t),\qquad Tb(t)=(4-3t,t-1). $$

For $0\lt t\lt1$, let $Q_t$ be the open box with this center and radii $t,1-t$. Its first-coordinate interval is

$$ (4-4t,4-2t). $$

If $0\lt s\leq t/4$, then the first interval of $Q_s$ starts at or to the right of $4-t$, whereas that of $Q_t$ ends at $4-2t$. The boxes are disjoint. Thus the choices $t_j=4^{-(j+1)}$ give infinitely many nonempty pairwise disjoint boxes, all with positive radii summing to one and all for the same fixed involution.

The reflection, center formula, nonemptiness, scale inequality, and pairwise disjointness are kernel checked in `formalization/HeadComplexity/Research/ScaledBoxPackingObstruction.lean`. In particular, `HeadComplexity.ScaledBoxPackingObstruction.boxes_pairwise_disjoint` rules out a finite packing bound that depends only on the dimension and exterior norms of an arbitrary involution.

## Exact scope

This matrix is not asserted to arise from an actual Boolean unit-contact basis. The boxes are not asserted to belong to different chambers of a fixed Boolean evaluation arrangement. They merely refute the proposed intermediate reduction that discards the Boolean normal rows and tries to count arbitrary disjoint boxes.

The remaining route must use those rows, or a boundary decomposition whose total entropy remains controlled. A cover of the image simplex at one fixed Euclidean resolution only controls labels where the denominator stays quantitatively positive. It does not automatically control labels on a face where the denominator tends to zero. No original-model lower-bound consequence is claimed here.

`scaled-box-packing-build.txt` records the build; `scaled-box-packing-axioms.txt` records the transitive axiom output. The original definitions are unchanged.
