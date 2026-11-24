# Power-saving research outcome

## The requested result remains unproved

This run did not prove the requested statement

$$ \exists\delta\gt0\quad\exists c\gt0\quad\exists n_0\in\mathbb N\quad\forall n\in\mathbb N,\qquad n\geq n_0\implies W(n)\geq c\frac{2^n}{n^{2-\delta}}. $$

No explicit exponent below two was obtained for the unrestricted original model. The existing lower-bound exponent was not improved here. There is no Lean declaration in this run proving the requested statement, and none of the auxiliary results below should be substituted for it.

The work started from `f4781ed`, the canonical `origin/autoresearch` baseline, on `ar/47c1ff45613b`. The [research clock and activity record](RESEARCH_LOG.md) records the new run separately from prior work. Previous branches were inspected selectively. Other runs were not modified.

## Original-model fidelity

The original definitions of heads, admissible affine ratios, computability, and worst-case complexity were unchanged. The score remains an affine bias plus a sum of affine ratios. Denominators are positive on the cube with the original coherent slope conditions; constant-denominator numerator restrictions remain in place. Arbitrary real coefficients, dimensions, target-dependent denominators, and cancellation remain permitted.

The new definitions are confined to research modules: moment and remainder expressions, comparison scores, explicit counterexamples, matrix-rank predicates, and stability predicates. Some auxiliary upper counts deliberately enlarge a comparison class; their conclusions are explicitly restricted to that class and are not transferred back without a proved bridge.

## Lean-checked auxiliary results

All declaration names in this table begin with `HeadComplexity.`. Each source file is under `formalization/HeadComplexity/Research/`.

| File | Main declarations and exact scope |
| --- | --- |
| [RadialMomentTransfer.lean](../../formalization/HeadComplexity/Research/RadialMomentTransfer.lean) | `RadialMomentTransfer.uniform_radial_sign_transfer`: fixed radial rational and exponential germs have the same eventual signs, including every cancellation order and exact zeros, on one common finite-input interval. |
| [RadialMovingNumeratorTransfer.lean](../../formalization/HeadComplexity/Research/RadialMovingNumeratorTransfer.lean) | `RadialMovingNumeratorTransfer.uniform_moving_numerator_sign_transfer`: the specified transfer with polynomial numerator jets of a fixed finite degree. It is not an arbitrary-path reduction. |
| [RadialJetAlgebra.lean](../../formalization/HeadComplexity/Research/RadialJetAlgebra.lean) | `RadialJetAlgebra.tail_identity` and `moment_tail`: the exact finite algebra underlying the jet transfer. |
| [RadialSpanSeparation.lean](../../formalization/HeadComplexity/Research/RadialSpanSeparation.lean) | `RadialSpanSeparation.target_computableWith_two_heads` and `not_exponentialScore_represents_target`: an original two-head target excluded by its specified fixed-direction exponential numerator spaces. |
| [RadialContraction.lean](../../formalization/HeadComplexity/Research/RadialContraction.lean) | `RadialContraction.target_computableWith_two_heads` and `not_small_scale_represents_target`: an exact original-model counterexample to the proposed fixed-direction contraction over a whole scale interval. |
| [ConditionedReciprocalApproximation.lean](../../formalization/HeadComplexity/Research/ConditionedReciprocalApproximation.lean) | `ConditionedReciprocalApproximation.conditioned_score_preserves_sign`: a quantitative geometric approximation bridge under its explicit relative-error hypothesis. No universal margin repair is claimed. |
| [AffineBooleanZeroDivisors.lean](../../formalization/HeadComplexity/Research/AffineBooleanZeroDivisors.lean) | `AffineBooleanZeroDivisors.support_card_le_two`, together with the one- and two-slope classifications of affine Boolean zero divisors. |
| [TwoHeadBooleanDegeneracy.lean](../../formalization/HeadComplexity/Research/TwoHeadBooleanDegeneracy.lean) | `TwoHeadBooleanDegeneracy.denominator_difference_support_le_two`: the stated positive-rescaling support conclusion for exact two-head zero relations in dimension at least five. |
| [TwoHeadProductCompilation.lean](../../formalization/HeadComplexity/Research/TwoHeadProductCompilation.lean) | `TwoHeadProductCompilation.uniform_two_head_sign_compilation` and `affine_exponential_product`: the cancellation-independent two-head to three-product comparison and its Boolean factorization. |
| [TwoHeadOriginalProductBridge.lean](../../formalization/HeadComplexity/Research/TwoHeadOriginalProductBridge.lean) | `TwoHeadOriginalProductBridge.original_two_heads_have_three_affine_exponential_terms`: starts from the actual `computableWithHeadsN n 2 f`, including its permitted dimensions and weak negative-label convention. |
| [AntipodalProductRank.lean](../../formalization/HeadComplexity/Research/AntipodalProductRank.lean) | `AntipodalProductRank.rank_eq_card_of_antipodal` and `product_width_of_antipodal`: the sign-rank certificate and affine-product comparison-class rank bound. |
| [BooleanInterpolationStability.lean](../../formalization/HeadComplexity/Research/BooleanInterpolationStability.lean) | `BooleanInterpolationStability.denominator_product_upperStable`, `interpolation_agrees_on_boolean_cube`, and `multilinear_not_upperStable`: an exact admissible stability counterexample, with an explicit upper-half-plane zero after Boolean interpolation. |
| [FiniteDifferenceCompilation.lean](../../formalization/HeadComplexity/Research/FiniteDifferenceCompilation.lean) | `FiniteDifferenceCompilation.uniform_finite_head_sign_compilation`: the arbitrary finite-head analytic sign bridge. The proper-subset grouping and its exponential atom count are separately proved in writing. |

The [aggregate axiom audit](VerificationAudit.lean) imports these modules and checks the listed conclusions. Its [successful transcript](final-axiom-audit.txt) and [source hashes and machine-readable audit](final-verification.json) are saved. All twenty audited declarations use only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. No `sorry` or new mathematical axiom is used to assert any reported result. Independent builds and mathematical statement audits are recorded in the individual audit files.

## Other useful proved results, with their boundaries

The [weighted partially linear sign count](weighted_partial_linear_capacity.md) and [curvilinear osculating count](curvilinear_osculating_capacity.md) give stronger bounds for explicitly restricted parameter families. The unrestricted class can have one independent cluster per head, which restores the old counting scale. No reduction to a small number of clusters was found.

The [adaptive product-compiler obstruction](adaptive_product_compiler_logarithmic_obstruction.md) shows that arbitrary joint replacement can require a logarithmic increase in width. Its strongest dimension regime is polynomial in the original width, not the exponentially large widths relevant to the target. The [two-head separation](adaptive_two_product_separation.md) has an exact rational certificate and makes the three-product upper bound sharp at width two. Its finite certificate is distinguished from the general Lean rank theorem.

The [signed quadrature obstruction](signed_exponential_quadrature_obstruction.md) rules out a small exact compiler retaining the specified directions and numerator assignments, even with unrestricted signed nodes. Allowing new affine numerators bypasses that obstruction. It is not an unrestricted product-compilation lower bound.

The [positive product dictionary](product_atom_ball_upper_bound.md) exactly spans every real cube table with fewer than twice the dimension-theoretic minimum number of fixed affine-product atoms. The [general finite-difference compiler](general_finite_difference_product_compilation.md) gives an exponential-in-head-count bound. Neither gives the width-sensitive, sublinear-in-dimension overhead needed for the requested lower bound.

The [cleared-numerator rank theorem](cleared_numerator_border_rank.md) makes that exponential bound sharp for convergence to the canonical cleared table. Crucially, its witness can have the Boolean labels of an OR and need only one original head. Thus the exact rank obstruction cannot count actual target labels. The [three-head radial theorem](three_head_radial_compilation.md) separately identifies the limitation of a second-order leading-cubic compiler.

The [log-product duality analysis](log_product_tangents_and_duality.md) gives an exact fixed-denominator alternative, interior signed-potential saddles at valid dual certificates in every dimension at least two, and fixed coherent pencils whose dual certificates must vanish at a prescribed vertex. These results invalidate simple convexity and strictly-positive-dual repairs. They do not exclude nonnegative certificates or supply a uniform count over all denominators.

The [staircase chart analysis](staircase_charts_and_shape_degree.md) shows that monomial diagrams can be counted cheaply, while the natural shape-coordinate resultant still incurs the large degree penalty. The [constant-pencil antipodal calculation](constant_pencil_antipodal_rank.md) gives an exact counterexample to a naive generic interpolation-rank claim.

The [coordinate-restriction constructions](restriction_and_near_constant_obstructions.md) prove arbitrary interpolation on sufficiently small faces with arbitrarily near-constant denominators. They also give an explicit positive moment-curve family for which no three denominators share a pencil on any coordinate face of dimension at least two, even though all denominators are uniformly close to one. A separate independent audit checks the quantitative determinant bound.

All results in this section are written proofs unless a more specific formal or finite status is stated. Numerical searches are recorded as numerical searches. Failed numerical fits were never used as lower bounds.

## What did not resolve the task

Joint radial contraction and fixed-direction replacement fail by exact original-model counterexamples. General moving or curved degenerations are not covered by the fixed radial theorem. Near-constant denominator approximations still require control of cancellations. Shape coordinates and multiblock degree counts retain the large denominator cost. Signed log-potential duality does not inherit log-concavity. Exact table rank, including the new sharp exponential example, does not bound Boolean sign labels. Random restriction loses useful query-to-parameter ratios before it supplies the desired simplification, and small faces can interpolate arbitrary tables using arbitrarily near-constant admissible denominators.

The remaining issue is a theorem about the actual strict Boolean labels of all admissible finite-scale representations. No such improved upper count, no general sign-preserving replacement with sufficient overhead, and no alternative original-model lower-bound mechanism was obtained. A conjectural sufficient statement is not being offered as a solution.

## Prior result kept separate

The earlier branch `ar/0f08fe6fb98a` contains a genuine original-model universal upper bound of order $2^n/(n\log n)$. Its source and saved axiom transcript were inspected selectively and are documented in [the provenance note](prior_universal_log_upper_provenance.md). Its large verification chain was not freshly rebuilt in this run. It is an upper bound, not evidence that the requested lower bound has been proved.
