# Independent audit of the conditioned reciprocal approximation

## Verdict and scope

I independently read and compiled `formalization/HeadComplexity/Research/ConditionedReciprocalApproximation.lean`. The compilation finished successfully on 2026-11-24. Every printed declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.

The file proves an exact reciprocal approximation identity, quantitative relative error estimates, and a finite-sum sign-preservation theorem. It does not prove a margin repair, a sign-count theorem, or an unrestricted head lower bound.

## Checked declarations

The theorem `exact_error` proves the finite geometric identity without approximation. Its hypotheses explicitly require the three divisors to be nonzero.

The theorem `geometric_relative_error` assumes $q\gt0$, $m\geq1$, and $q\leq B\leq mq$. These hypotheses imply $B\gt0$ and put the geometric ratio in $[0,1-1/m]$. The theorem `exponential_relative_error` then uses $1-u\leq e^{-u}$ and obtains

$$ \left|\frac AB-\mathrm{headApprox}(A,B,q,m,d)\right|\leq\left|\frac AB\right|\exp\left(-\frac{d+1}{m}\right). $$

The theorem `sign_preserved_of_relative_error` handles an arbitrary finite index type of summands. Its hypotheses explicitly include a positive relative margin, a positive total amplitude, and a per-summand approximation error at most half the margin times the supplied amplitude bound. It assumes $|F|=1$, which is exactly the scalar form of a Boolean target value. The triangle inequality then leaves at least half of the positive original margin.

The theorem `conditioned_score_preserves_sign` combines these ingredients for a score $c+\sum_h A_h/B_h$. The amplitude assumptions $|A_h/B_h|\leq M_h$ imply the required nonnegativity of every $M_h$, so this property is not missing. The theorem permits arbitrary signs of numerators and arbitrary cancellation among heads. Its conclusion is the strict inequality

$$ F\left(c+\sum_h\mathrm{headApprox}(A_h,B_h,q_h,m,d)\right)\gt0. $$

This is a pointwise theorem. Applying it independently at each Boolean input requires the written coefficient-order chart construction, the global per-head supremum bounds, and the common margin hypothesis in `margin_sensitive_polynomial_capacity.md`. That construction permits a different selected coefficient $q_h(x)$ at each input and head. No Lean declaration in this file asserts that the original model automatically has a useful lower bound on its margin.

## Original-model scope

For a denominator with positive slopes, its positive constant and nonnegative slopes provide the selected-maximum chart directly. A denominator with negative slopes is first written in the reflected coordinates $y_i=1-x_i$. A constant denominator is already conditioned. These are exact algebraic rewritings used by the written counting proof; the formal theorem itself assumes the resulting scalar inequalities and does not encode the coherent-slope definition.

The final original-model exponent improvement remains open. The formal result verifies the approximation and sign-error bridge under an explicit margin assumption.
