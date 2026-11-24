# A linear head budget for affine mixed cylinders

## Statement and formal status

Let $P,Q\subseteq\lbrace 1,\ldots,n\rbrace$ be disjoint, and let $A$ be an arbitrary real affine function. The score

$$ G(x)=A(x)\prod_{i\in P}x_i\prod_{i\in Q}(1-x_i) $$

is uniformly approximable on the full Boolean cube by $\min(|P|,|Q|)+1$ original admissible heads. Every finite strict sign representation by a sum of such blocks therefore compiles into the original unrestricted model using the sum of these linear budgets. All affine coefficients and signed cancellation are allowed.

This is kernel checked in `formalization/HeadComplexity/Research/LinearCylinderCompiler.lean`. The main declarations are `HeadComplexity.LinearCylinderCompiler.uniformlyAtomsApproximable_cylinder_affine_min` and `HeadComplexity.LinearCylinderCompiler.computableWithHeadsN_of_cylinder_affine_sum`. The stronger `uniformlyAtomsApproximable_negativeFace_profile_affine` permits an arbitrary scalar profile of the selected Hamming weight, multiplied by an arbitrary affine score and gated to a negative face.

The inherited `CubeCylinder.cost`, which uses the cheaper of the two exponential inclusion-exclusion expansions, is unchanged. The new budget improves that estimate when both literal sets are sufficiently large. It does not assert a lower bound for unrestricted head complexity.

The first coefficient bound below is a written proof. A second explicit bound and the resulting full-cube relative-margin theorem are now kernel checked in `formalization/HeadComplexity/Research/LinearCylinderMargin.lean`. The earlier approximation logs are `linear_cylinder_build.txt` and `linear_cylinder_axioms.txt`; the quantitative compiler logs are `linear-cylinder-margin-build.txt` and `linear-cylinder-margin-axioms.txt`.

## Interpolation and admissible gating

Put $p=|P|$ and $t(x)=\sum_{i\in P}x_i$. Then $t(x)\in\lbrace 0,\ldots,p\rbrace$, and the positive literal product is the indicator of $t(x)=p$. For $p\geq 1$, choose the distinct positive shifts $s_j=p+1+j$, where $0\leq j\lt p$. The existing theorem `exists_exact_hamming_reciprocals` provides coefficients $c,b_j\in\mathbb R$ satisfying

$$ c+\sum_{j=0}^{p-1}\frac{b_j}{t+s_j}=\mathbf 1_{t=p}\qquad(0\leq t\leq p). $$

Multiplication by $A(x)\prod_{i\in Q}(1-x_i)$ gives one affine negative-face term and $p$ gated affine ratios. The former has a one-head approximation by `AnchoredAtomicDecomposition.uniformlyOneAtomApproximable_negativeFace_affine`. Each latter term has a one-head approximation by `CoherentFaceGating.uniformlyOneAtomApproximable_negativeFace_ratio`: its base denominator is $s_j+\sum_{i\in P}x_i$, whose slopes are nonnegative and whose constant term is positive. The gate replaces it by

$$ s_j+\sum_{i\in P}x_i+R\sum_{i\in Q}x_i+\delta\sum_{i=1}^{n}x_i,\qquad R\gt 0,\quad\delta\gt 0. $$

Every slope is strictly positive, so every approximating head is admissible in the original model. The numerator is still affine. Taking $R$ large and $\delta$ small gives the required full-cube approximation. The case $p=0$ is the existing one-head affine negative-face compiler. Simultaneously complementing every input exchanges $P$ and $Q$ and preserves the original atom class, which gives the minimum of the two budgets.

## Explicit coefficient bound

For the indicator profile, an explicit interpolation polynomial is

$$ Q_p(t)=\prod_{j=0}^{p-1}(t+s_j),\qquad P_p(t)=\frac{Q_p(p)}{p!}\prod_{k=0}^{p-1}(t-k). $$

The quotient $P_p(t)/Q_p(t)$ takes the desired values at all $p+1$ nodes. Its polynomial part is the constant $c=Q_p(p)/p!$, and its residues are $b_j=P_p(-s_j)/Q_p'(-s_j)$. All differences between distinct shifts are nonzero integers. For $p\geq1$, this gives

$$ |c|\leq(3p)^{p},\qquad |b_j|\leq(3p)^{2p},\qquad |c|+\sum_{j=0}^{p-1}\frac{|b_j|}{s_j}\leq C_p,\qquad C_p=(p+1)(3p+1)^{2p}. $$

The same formula gives $C_0=1$. If $\|A\|_\infty\leq M$, the sum of the full-cube norms of the exact gated target terms is at most $C_pM$. The coherent-face gate also bounds each approximating ratio pointwise by the corresponding ungated ratio. Alternatively, arbitrary uniform error controls each norm by the target norm plus that error, as in `UniformMarginCompiler`.

Consequently, suppose a strict unit-margin score consists of a bias $b$ and finitely many affine mixed-cylinder blocks indexed by $\ell$. Let $p_\ell$ be the smaller literal count of block $\ell$, and let $M_\ell$ bound the full-cube norm of its affine numerator. Applying the quantitative uniform compiler gives a representation with

$$ H\leq\sum_\ell(p_\ell+1),\qquad \gamma\geq\frac{1}{2\left(|b|+\sum_\ell C_{p_\ell}M_\ell\right)+1}. $$

This norm bound uses the entire Boolean cube, including points outside each cylinder. A bound only on the cylinder would not justify the displayed estimate for the gated reciprocal terms without another argument.

## Kernel-checked quantitative variant

The quantitative module uses $p+1$ reciprocals with poles $a_h=h+1$, where $0\leq h\leq p$, instead of a constant plus $p$ reciprocals. Put

$$ \widetilde Q_p(t)=\prod_{h=0}^{p}(t+a_h),\qquad \widetilde P_p(t)=\frac{\widetilde Q_p(p)}{p!}\prod_{j=0}^{p-1}(t-j). $$

The ratio takes value one at $p$ and zero at every smaller nonnegative integer. Integer pole separation gives the kernel-checked bounds

$$ |r_h|\leq(2p+2)^{2p+1},\qquad \widetilde C_p=(p+1)(2p+2)^{2p+1}. $$

Here $r_h$ is the residue at $-a_h$. This bound is slightly looser than the written $C_p$ estimate, but still has logarithm $O(p\log(p+1))$. It includes $p=0$ without a separate theorem. `bounded_decomposition_min` supplies the exact sum of $p+1$ bounded target functions, each uniformly approximable by one genuine head. Every target norm is bounded by $(2p+2)^{2p+1}M$ on the entire cube.

The declaration `HeadComplexity.LinearCylinderMargin.hasRelativeMargin_of_cylinder_affine_sum` proves that a full-cube unit signed gap and affine bounds $M_\ell$ imply

$$ H=\sum_\ell(p_\ell+1),\qquad \gamma\geq\frac{1}{2\left(|b|+\sum_\ell\widetilde C_{p_\ell}M_\ell\right)+1}. $$

The sum can contain arbitrary real coefficients and arbitrary signed cancellation. The proof uses exact partial fractions, coherent-face gating, global input complementation, and the existing quantitative uniform compiler. It does not rescale away relative margin. All seventeen public theorem declarations have transitive axiom output `[propext, Classical.choice, Quot.sound]`.

## Relation to the open repair step

The compiler permits mixed faces and new denominator directions, so the earlier exact sparse anchored-affine obstruction does not apply to it. However, it supplies no bound on how many mixed cylinders are needed to preserve the sign of an arbitrary narrow rational score. An arbitrary point cylinder can already require a linear budget under this construction. Applying it separately to all truth-table points is therefore too expensive.

The unresolved sufficient statement would bound the sum of smaller literal counts of a suitable affine-cylinder sign representation by a small overhead over the original head width, while controlling the affine coefficient mass. Neither the original width nor the bounded-mass anchored decomposition currently implies that statement. The high-margin count alone remains an intermediate theorem.
