# Independent audit of radial contraction and fixed radial transfer

## Radial contraction

I read `formalization/HeadComplexity/Research/RadialContraction.lean` and the corresponding mathematical note `radial_contraction_label_loss.md`. I independently reconstructed the coefficient matrix of the cleared score and verified the nine-weight annihilation identity over rational polynomials. I also recomputed the sixteen cleared values of the finite two-head witness.

The two declarations are `HeadComplexity.RadialContraction.target_computableWith_two_heads` and `HeadComplexity.RadialContraction.not_small_scale_represents_target`. The first uses the existing positive-affine-ratio bridge to the original head model. Both witness denominators have strictly positive constants and slopes. The second permits arbitrary real affine numerator coefficients and bias and rules out every scale strictly between zero and one tenth, including one tenth. Its contradiction remains valid with weak nonpositive scores at false vertices because a positive target vertex has a strictly positive certificate weight.

An independent invocation of `lake env lean HeadComplexity/Research/RadialContraction.lean` succeeded. The declarations report only `propext`, `Classical.choice`, and `Quot.sound`.

The theorem keeps the two displayed denominator directions fixed. It does not rule out a path changing those directions, and it implies no asymptotic head lower bound.

## Fixed radial moment transfer

I read the complete file `formalization/HeadComplexity/Research/RadialMomentTransfer.lean` and independently checked the scope of its final theorem `HeadComplexity.RadialMomentTransfer.uniform_radial_sign_transfer`.

The theorem quantifies over arbitrary finite input and head index types, arbitrary real functions $A_h,C_h,B$, and an arbitrary real bias $c$. Its sole substantive assumption is $B(x)\gt 0$ at every input. All functions and the bias are fixed independently of the scale. It concludes that one positive scale threshold works simultaneously at every input, preserves denominator positivity, and gives

$$ \mathrm{sgn}\left(c+\sum_h\frac{A_h(x)}{B(x)+tC_h(x)}\right)=\mathrm{sgn}\left(cB(x)+\sum_h A_h(x)e^{-tC_h(x)}\right) $$

for every smaller positive scale.

The geometric remainder identity is exact. Its scaled limit requires only the vanishing of all earlier moments. The exponential remainder uses the library Taylor remainder estimate. Their leading coefficients differ by positive factors, so the first nonzero moment gives matching strict signs. The proof chooses this first moment with `Nat.find`, imposing no fixed cancellation-order bound.

When every moment vanishes, finite polynomial interpolation proves that the weighted sum of every function of the shifts vanishes. This handles repeated shifts and identically zero coordinates without a genericity assumption. The finite input type then permits one common neighborhood. The final `Option` index construction adds the fixed bias as the zero-shift weight $cB(x)$ and negates the shifts to obtain the displayed positive-denominator convention.

An independent invocation of `lake env lean HeadComplexity/Research/RadialMomentTransfer.lean` succeeded. The final declaration reports only `propext`, `Classical.choice`, and `Quot.sound`. There is no new axiom and no `sorry`.

This is a kernel-checked analytic auxiliary theorem. It does not assert that a finite-scale arbitrary representation can be moved to the fixed radial family while preserving its labels. The contraction counterexample above demonstrates that such a reduction cannot simply retain the denominator directions and vary the affine numerators.
