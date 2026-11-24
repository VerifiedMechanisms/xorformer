# An exact finite-difference compiler with exponential width

## Statement

Every truth table computed by $H$ original unrestricted heads belongs to the affine-product comparison class with $2^H-1$ terms and a free bias. This holds in every dimension, including $H=0$, with no margin restriction, coefficient bound, conditioning hypothesis, or restriction on signed cancellation.

The comparison terms have the form

$$ \left(a_0+\sum_{i=1}^n a_i x_i\right)\prod_{i:x_i=1}z_i. $$

All factors produced by this compiler are positive exponentials. These terms are members of the comparison class, not a proposed repair by original heads. The original certificate consists entirely of admissible `FracAtom` heads, and their denominator positivity is checked before clearing. Original definitions are unchanged.

The theorem is now kernel checked as `HeadComplexity.FiniteDifferenceProductCompiler.original_compiler` in `formalization/HeadComplexity/Research/FiniteDifferenceProductCompiler.lean`. The width is exponential in $H$ and is inadequate for the requested asymptotic gain.

## Proof

The original false class may initially include zero scores. The inherited `exists_strict_fracCertificate` theorem shifts the bias so every label is strict. For $H\geq1$, absorb that bias into one affine numerator. This gives a score with the same complete truth table,

$$ S(x)=\sum_{h=1}^H\frac{A_h(x)}{B_h(x)},\qquad B_h(x)\gt0. $$

The affine normal form uses the original atom's exact numerator and denominator coefficients. In particular, the denominator may depend on the target, and no sign condition is imposed on numerator coefficients. Clearing the positive product gives

$$ P(x)=S(x)\prod_{h=1}^H B_h(x)=\sum_{h=1}^H A_h(x)\prod_{g\neq h}B_g(x). $$

For positive $t$, define

$$ D_t(x)=\sum_{h=1}^H A_h(x)\prod_{g\neq h}\frac{\exp(tB_g(x))-1}{t}. $$

The elementary derivative limit $(\exp(tb)-1)/t\to b$ gives $D_t(x)\to P(x)$. The cube is finite and all labels of $P$ are strict. Consequently one positive $t$ preserves every label simultaneously. No quantitative lower bound on that $t$ is asserted or needed.

Multiplication by the positive scalar $t^{H-1}$ preserves signs. The grouped product expansion is

$$ t^{H-1}D_t(x)=\sum_{\varnothing\neq V\subseteq\lbrace1,\ldots,H\rbrace}(-1)^{|V|-1}\left(\sum_{h\in V}A_h(x)\right)\exp\left(t\sum_{g\notin V}B_g(x)\right). $$

Each summand is an affine function times a positive separable product, because its exponent is affine on the cube. There are exactly $2^H-1$ nonempty subsets. The formal proof obtains the grouped identity by differentiating the elementary product expansion, which avoids counting duplicate exponential directions separately. When $H=0$, the original score is constant and the comparison class's free bias suffices.

## Scope of the result

The inherited [exact cleared-table obstruction](../power-saving-20261124/cleared_numerator_border_rank.md) proves that the exponential term count can be necessary for approximating the particular cleared numerator. The obstruction's sign table itself is easy. Thus this verified compiler does not settle whether a different sign-equivalent score, or a target-dependent positive multiplier on the vertices, permits much fewer terms.

At the aimed width $H\asymp 2^n/n^{3/2}$, the comparison-class count requires only $K\leq2^n/[100n\log(n+1)]$. The proved value $K=2^H-1$ is far larger. The missing lemma is still a compiler into that smaller budget, exactly or with at most $2^n/16$ label errors, or an independently justified unrestricted capacity argument.

## Verification

`lake build HeadComplexity.Research.FiniteDifferenceProductCompiler` passed with 4029 jobs. The transitive audit checked all 31 theorem declarations, and five explicit `#print axioms` checks reported only `[propext, Classical.choice, Quot.sound]`. The build and transitive axiom results are recorded in `finite-difference-product-build.txt`, `finite-difference-product-axioms.txt`, and `finite-difference-product-print-axioms.txt`. The exact original-model declaration is `original_compiler`; its premise class is the unchanged `headComputableFunctions`, via the existing `AffineProductCapacity.HasCompiler` definition. The main bridge `mem_represented_of_original` directly assumes `computableWithHeadsN n H f`.
