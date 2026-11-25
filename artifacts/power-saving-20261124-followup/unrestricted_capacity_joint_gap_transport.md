# Joint gap transport across distinct denominators

## The exact same-denominator move

Let two heads have the same strictly admissible affine denominator $B$, numerators $A_1,A_2$, and maxima $u_1,u_2$. Write $g_i=u_i-A_i/B\geq0$ and $D=u_2B-A_2\geq0$. The one-head replacement

$$ \phi_{1,t}=\frac{A_1+t u_1D}{B+tD}=\phi_1+\frac{t g_1g_2}{1+t g_2} $$

is admissible for all sufficiently small signed $t$ when the original denominator parameters lie in the strict interior. Its value at every maximum of $\phi_1$ remains $u_1$. For $t\geq0$, it moves every value toward $u_1$, so neither interval-budget branch increases. For sufficiently small negative $t$, the maximum is still $u_1$, while the lower branch may increase; an upper-branch slack is therefore needed to call the amplitude unchanged.

The first derivative is exactly $g_1g_2$. Thus first-order stationarity in an upper-branch interior chart already forces the corresponding signed dual cross moment to vanish. A negative cross moment relevant to the duplication analysis must involve distinct denominator functions.

`SharedDenominatorGapPath.transport_identity` kernel checks this identity. `transport_interval`, `transport_at_max`, and `transport_norm_le` check the interval, attained-maximum, and full-cube norm conclusions. `exists_admissible_path` constructs an actual `FracAtom` for every step whose perturbed positive affine denominator coefficients remain positive. `eventually_admissible_path` also kernel checks the entire small signed neighborhood from strict positivity in finitely many coordinates. These declarations do not provide a global access theorem. Heads with identical denominators can also be merged directly, so their presence cannot by itself be the decisive minimal-width obstruction.

## The first failed extension

For distinct denominators, the analogous proposed perturbation would require

$$ D=B_1g_2=u_2B_1-\frac{A_2B_1}{B_2}. $$

This is generally not affine. Replacing it by an affine form is not a justified operation on the original model.

The finite-cube counterexample in `PencilMoebiusTangentObstruction.lean` already rules out a universal first-order tangent repair of this type: even two denominators on a shared scalar pencil, with arbitrary affine numerators, can have a product direction outside the full original-head tangent space. The counterexample uses an explicit finite row functional annihilating every tangent direction and not annihilating the proposed nonlinear correction. A common scalar denominator pencil is therefore insufficient to justify the desired joint tangent inclusion.

## Why adding product heads does not resolve the failure

The nonnegative-cone theorem in `unrestricted_capacity_nonnegative_cone.md` gives a more specific obstruction to a cost-free addition. A score $T=b+\sum_h\phi_h$ whose upper interval contribution is zero has

$$ T=-\sum_h(u_h-\phi_h),\qquad u_h=\max_x\phi_h(x). $$

Hence $-T$ is a sum of nonnegative original heads. Such sums cannot approximate a mixed-point indicator below error $1/5$, regardless of width or amplitude. Products of two nonnegative heads, even of the same coherent orientation, can converge to exactly such an indicator. Thus a universal product compiler preserving zero upper contribution is false.

The amplitude lower bounds in `unrestricted_capacity_coherent_edge_variation.md` and `mixed_point_high_order_amplitude.md` separately show that arbitrary signed product compilation cannot have dimension-independent, or in the arbitrary-accuracy regime polynomial, amplitude cost. The latter does not rule out exponential amplitude cost, which remains small compared with the target double-exponential margin thresholds.

## The remaining model-specific lemma

A usable replacement theorem must coordinate changes to distinct existing poles and numerators. It must prove all of the following together: admissibility of every resulting head; preservation of every cube label; control of both interval-budget branches; a quantitative margin gain; and no accumulation of width beyond the allowed comparison width. The signed dual cross-moment identity alone proves none of these access statements.

One precise possible target is a norm-preserving replacement at a duplicated stationary point whose distinct-denominator cross moments are negative. The replacement may change several existing heads, rather than adding a nonpositive product score with zero upper contribution. A proof must explain how the change in existing extrema pays for the new product-like terms. No such construction or quantitative inequality has been established.

This identifies the first failure of the current joint route without asserting that arbitrary signed cancellation can be removed. The unrestricted capacity target remains open.

## Validation

`lake build HeadComplexity.Research.SharedDenominatorGapPath` completed successfully with 3226 jobs. All six declarations above were checked transitively by `SharedDenominatorGapPathAudit.lean`; the only axioms reported are `propext`, `Classical.choice`, and `Quot.sound`. The derivative and KKT interpretations remain written consequences under the stated interior and stationarity hypotheses.
