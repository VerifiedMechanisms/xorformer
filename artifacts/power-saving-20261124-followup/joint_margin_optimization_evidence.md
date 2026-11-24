# Joint original-head margin optimization evidence

## Scope

This is a finite computational checkpoint, not an unrestricted lower bound or a proof about the globally optimal margin. The search varies the denominators as well as all affine numerator coefficients. Its output consists of explicit lower certificates for the best margin of particular truth tables. Failed restarts and omitted targets give no nonrepresentability conclusion.

The search uses genuine positive coherent denominators

$$ B_h(x)=w_{h,0}+\sum_{i=1}^n w_{h,i}u_{h,i}(x),\qquad w_{h,i}\gt0,\qquad u_{h,i}(x)=x_i\text{ for all }i\text{ or }u_{h,i}(x)=1-x_i\text{ for all }i. $$

Every numerator is an arbitrary affine function of the original input coordinates. Strictly positive denominator coefficients put these ratios within the original admissible-head normal form. The two orientations may differ between heads. Denominator coefficients are softmax coordinates during the numerical search, with logits restricted to the box $[-6,6]$. This restriction only limits the certificates the search can find; no unrestricted optimality claim is made.

## Exact full-cube objective

For fixed denominators, the search solves the linear program maximizing $\gamma$, subject to

$$ f(x)\left(b+\sum_h\frac{A_h(x)}{B_h(x)}\right)\geq\gamma,\qquad -t_h\leq\frac{A_h(x)}{B_h(x)}\leq t_h,\qquad -t_b\leq b\leq t_b,\qquad t_b+\sum_h t_h\leq1. $$

Every Boolean vertex occurs in both the signed-margin constraints and the head-norm constraints. Thus the objective is the requested relative margin, with the full-cube norm and the bias contribution included. The head midpoint is then moved into the bias, using the exact centering operation proved in `MidrangeMarginCentering.lean`.

The outer search uses the LP dual-envelope derivative and multiple denominator restarts. A finite-difference derivative check on a separate random four-bit instance had maximum absolute discrepancy below $5.3\cdot10^{-11}$. This numerical derivative check is not used to certify any final representation.

A zero optimum for a fixed denominator list gives a flat outer objective, even when other denominator lists represent the same labels. To escape those plateaus, the refinement script first minimizes average hinge slack at a prescribed positive target gap, then returns to margin maximization. Neither phase is a global optimizer.

## Exact rational verification

After searching, every numerator coefficient, denominator coefficient, and bias is rounded to a rational with denominator $10^9$. The independent checker uses Python `Fraction` arithmetic to verify strictly positive coherent denominator coefficients, every cube label, every full-cube head extremum, the bias contribution, and the centering amplitude inequality. The following lower margins are rounded down to multiples of $10^{-6}$.

| Cube and width | Retained certificates | Candidate sampling | Smallest exactly checked margin |
| --- | ---: | --- | ---: |
| Five bits, two heads | 40 | Witness-generated labels | $0.134524$ |
| Five bits, two heads | 24 | 137 uniform random label candidates | $0.004799$ |
| Six bits, four heads | 24 | 103 uniform random label candidates | $0.006945$ |
| Five bits, two heads, refined target | 1 | 100 hinge-continuation restarts | $0.022977$ |

Only candidates for which the search found a positive certificate were retained in the two uniform-label experiments. The other candidates were not proved unrepresentable. The refined target is index 20 in the five-bit uniform-label file. Its initial retained certificate had margin $0.004799$, and its improved certificate has margin $0.022977$. This is direct evidence that a difficult fixed-denominator optimization state need not reflect the best representation of its truth table.

The optimized denominators are not uniformly close to one another. Some solutions approach a constant-denominator affine limit; others remain separated. These observations do not rule out a different favorable clustered representation.

## Reproduction and status

The search is `search_joint_relative_margin.py`; the hinge refinement is `refine_joint_relative_margin.py`; the exact finite checker is `check_joint_relative_margin_exact.py`. Their JSON outputs are committed beside this note. Run the searches through `heavy` on the shared machine. The exact checker is small and does not require a compute slot.

The certificate arithmetic is finite and exact after rounding, but it is not Lean kernel checked. The corresponding general centering theorem is kernel checked separately. No original definition, lower-bound statement, or model hypothesis was changed.

The next mathematical question is the one-head full-feasible contact geometry: with a fixed Boolean simplex contact basis, a unit-gap score yields two affine functions $U$ and $-V$ in the closure of the same threshold chamber, with complementary contact zeros and $U+V$ a positive coherent denominator. Counting those common chambers may be more informative than counting arbitrary real-value interpolation fibers.
