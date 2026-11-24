# Independent Audit of the Fixed-Direction Joint Compilation Separation

## Verdict

I independently checked `fixed_direction_joint_compilation_separation.md`, the full proof source `formalization/HeadComplexity/Research/RadialSpanSeparation.lean`, and the affine-ratio-to-head bridge used by its final theorem. The claims hold with the stated restrictions. They do not prove a lower bound for unrestricted worst-case head complexity.

## Mathematical checks

The cleared numerator of the exact two-head reciprocal witness is correct after the Boolean identity $a\Delta=a$. Its signs agree strictly with the displayed sixteen-entry target, and every denominator slope and constant is strictly positive. The original model therefore permits both arbitrary affine numerators.

For the comparison exponential family, the normalized row difference between prefixes $(1,0)$ and $(0,1)$ is independent of the last two coordinates. The target forces opposite strict orders at suffixes $(0,0)$ and $(1,0)$. This proves impossibility for every real common scale, every bias, and arbitrary affine recalibration of both numerators, including the convention that false inputs may have score zero.

The bounded analytic numerator family has the asserted cleared numerator and preserves its strict signs for $0\lt t\lt1/2$. The reciprocal and exponential Grassmannian limit spaces both have dimension nine. Their additional directions modulo the common eight-dimensional space are respectively $a(x_3+x_4)$ and $x_3x_4$. In the exponential expansion, the suffix-linear approximation error is of order $t^3$, so it disappears after division by $t^2$. These limit calculations are written mathematics, not Lean-verified limit statements.

## Lean verification and model bridge

An independent execution of `lake env lean HeadComplexity/Research/RadialSpanSeparation.lean` completed successfully. Its axiom output for both final declarations contains only `propext`, `Classical.choice`, and `Quot.sound`.

The declaration `HeadComplexity.RadialSpanSeparation.target_computableWith_two_heads` concludes `computableWithHeadsN 4 2 target`. It applies `computableWithHeadsN_of_positiveAffineRatios`, whose explicit construction produces a `FracAtom` from each prescribed positive affine denominator and arbitrary affine numerator. The atom evaluation equals that affine ratio exactly. The subsequent `computable_of_fracComputable` theorem constructs actual attention heads with a common readout. The shared-embedding bridge is also present in `FracAtomHead.lean`. No restricted surrogate head model is substituted in this chain.

The declaration `HeadComplexity.RadialSpanSeparation.not_exponentialScore_represents_target` quantifies over the bias, both affine numerators, and the common real scale. Its rectangle identity and contradiction are algebraic consequences of the real exponential addition rule. There is no new axiom or `sorry` in the checked proof.

## Exact limitation

The exponential directions are the two directions prescribed by the reciprocal configuration. A compilation allowed to choose arbitrary new directions, separate scales, or additional atoms remains open. The two formal declarations certify this obstruction and the exact original-model witness. They do not assert the user's requested asymptotic lower bound.
