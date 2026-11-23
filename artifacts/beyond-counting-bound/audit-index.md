# Research Audit and Unresolved Target

## Target status

The selected target is unproved:

$$ \sup_n\frac{n^2W(n)}{2^n}=\infty. $$

No lower bound with a denominator exponent strictly between one and two has been established either. The manuscript's architecture, unrestricted real parameters and embedding dimensions, target-dependent denominators, and definitions of head complexity have not been changed. None of the auxiliary statements below is presented as completion of the target.

## Exact results useful for auditing proposed proofs

| Result | Verification scope | Source |
| --- | --- | --- |
| One extra admissible head gives unit signed margin everywhere and fixes the origin score to its label. | Complete exact-model construction in Lean, including strictification and the finite minimum margin. | `HeadComplexity.OriginMarginRepair.computable_origin_margin_repair`, in `formalization/HeadComplexity/Atoms/OriginMarginRepair.lean`; [writeup](origin-margin-repair.md). |
| Keeping a one-head classifier's signed scores in a fixed positive interval can require linearly many heads. | Exact rational-approximation transfer in Lean, with an explicit hardness hypothesis; the combined result cites Sherstov's external theorem. | `HeadComplexity.BoundedAmplitude.amplitude_ratio_obstruction`; [writeup](bounded-amplitude-obstruction.md). |
| Mixed binary selected evaluations can have full parameter rank. | Exact eighteen-bit scores and rational Jacobian determinants in Lean; extension to every larger input dimension is a written coordinate-cloning proof. | `HeadComplexity.IntegerBinaryFiber.sample_scores`, `jacobian_det_ne_zero`, and `clone_jacobian_det_ne_zero`, in `formalization/HeadComplexity/Atoms/IntegerBinaryFiber.lean`; [writeup](integer-binary-fibers.md). |
| Positive reciprocal queries can shatter an unbounded number of tests per parameter. | General finite-field and selector constructions in Lean. These are freely specified queries, not a full-cube attention representation. | [Hall-selector writeup](reciprocal-matching-shattering.md). |
| Actual admissible heads shatter a two-coordinate Boolean layer with an unbounded number of samples per normalized parameter. | Complete replication and actual-model embedding in Lean; it does not shatter the full cube. | `HeadComplexity.BipartiteReciprocalShattering.unbounded_actual_tests_per_parameter`; [writeup](bipartite-reciprocal-shattering.md). |
| A sign-equivalent polynomial in the original head parameters can require degree at least the number of heads. | Exact admissible parameter-line construction in Lean. | `HeadComplexity.ParameterLineOscillation.admissible_heads_force_parameter_degree`; [writeup](parameter-line-degree.md). |
| Hyperbolicity, positive coefficients, and polynomiality still allow every Boolean tangent sign table. | Complete written construction; interpolation and root-bracketing ingredients in Lean. This relaxation does not retain products of linear factors. | [Hyperbolic tangent writeup](hyperbolic-boolean-tangents.md). |

The recorded kernel checks use standard foundational axioms. The finite binary-fiber example fails the minimum-norm condition: its exact signed dual has both positive and negative coordinates, and a cube vertex violates unit margin. Its full rank is not a minimum certificate.

## Approaches that did not establish the target

The [research ledger](research.md) records the manuscript audit, primary literature checks, explicit counterexamples, and blocked steps. The unresolved steps include a uniform sign count with adaptive denominators, a valid bound on canonical minimum branches, and a realization theorem converting free reciprocal queries or independent quadratic jets into the actual architecture at the required head cost.

Generic coordinate uniqueness, uniformly small critical-point counts, a head-independent polynomial degree, and several monotonicity or hyperbolicity relaxations fail for the explicit reasons in the linked audits. Fixed-denominator counts, bounded-weight neural-network theorems, finite-field phases, and exact tensor-value ranks do not cover the requested unrestricted sign representations.

## Numerical work is not a proof

[Continuation diagnostics](continuation-diagnostics.md) distinguishes the certified small-margin construction from its uncertified continuation. The continued branch lost a necessary multiplier sign far below unit margin. Independent stationarity replays rejected solver-reported successes. Corrected searches use rescaled objectives, stable coherent-denominator formulas, all cube constraints, and a separate head-table energy objective.

`experiments/late-search-diagnostics.json` retains search outcomes and hashes. Finite failures and missing numerical candidates imply neither infeasibility nor the desired asymptotic lower bound. `run.json` records the target status, checked declarations, and actual timing.
