# Independent audit of the conditioned reciprocal count

## Verdict

Root independently checked the proof in `margin_sensitive_polynomial_capacity.md`. The stated margin-sensitive count and its sparse-width dichotomy are valid. They do not prove a bound on unrestricted head complexity. The missing margin repair is a substantive additional assertion.

## Checks

The denominator chart is exact. Complementing all coordinates separately for a negative-slope head gives a positive constant and nonnegative slopes. Ordering these coefficients fixes, at every Boolean input, the largest present coefficient. The always-present constant ensures that this coefficient is positive, including for constant denominators. Its reciprocal can be introduced as an independent parameter without increasing the claimed degree.

The geometric remainder is a *pointwise relative head error*. It is not an absolute error multiplied by an uncontrolled denominator ratio. For $q\leq B\leq mq$, $q\gt0$, and $m\geq1$, define

$$ G_d(A,B,q,m)=\frac{A}{mq}\sum_{k=0}^d\left(1-\frac{B}{mq}\right)^k. $$

Then

$$ \left|\frac AB-G_d(A,B,q,m)\right|=\left|\frac AB\right|\left(1-\frac{B}{mq}\right)^{d+1}\leq\left|\frac AB\right|\exp\left(-\frac{d+1}{m}\right). $$

Consequently the sum of head errors is controlled by the sum of their actual table amplitudes. The bias is retained exactly. A relative head-amplitude margin of at least $\gamma$ therefore permits the polynomial substitution once the final exponential factor is at most $\gamma/2$.

For each fixed list of orders and orientations, the score predicates have $p=1+3(n+1)H$ parameters and degree at most $2d+2$. The new reciprocal parameters are shared across every query in that head; they are not introduced separately at every vertex. There are at most $[2(n+1)!]^H$ lists. Zero-head padding justifies the monotonicity in width used in the asymptotic corollary.

At $H=\lfloor cN/n^{1+\beta}\rfloor$ and $\gamma=\exp(-\exp(n^\beta))$, the leading normalized logarithmic count is $3c/\log2$. All ordering and residual entropy terms are $o(1)$. Thus $c=1/100$ is sufficient for the stated eventual $2^{N/2}$ bound.

## Kernel verification

`formalization/HeadComplexity/Research/ConditionedReciprocalApproximation.lean` proves, in namespace `HeadComplexity.ConditionedReciprocalApproximation`:

- `selected_max_sum_bounds`, the finite-sum bounds supplied by a largest present coefficient;
- `exact_error`, the exact geometric remainder identity;
- `geometric_relative_error` and `exponential_relative_error`;
- `sign_preserved_of_relative_error` and `conditioned_score_preserves_sign`, the finite signed-sum bridge.

The checked declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry` or new axiom. The Lean file does not formalize Warren's theorem, the discrete order enumeration, or the asymptotic count. It also does not assert the missing margin repair or the original worst-case head lower bound.
