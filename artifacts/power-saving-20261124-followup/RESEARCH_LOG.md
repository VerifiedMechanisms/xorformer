# Beyond the Xorformer Counting Barrier

## Clock and starting state

The active research period began on 2026-11-24 at 15:27:59 UTC. The twelve-hour deadline is 2026-11-25 at 03:27:59 UTC. The final verification hour starts at 02:27:59 UTC.

The starting revision is `aa0cceb140ba75149353f92943b1fba78e7e0ec5`, equal to `origin/ar/47c1ff45613b`. Work is on `ar/4e24baaa5491`. The initial working tree was clean. The original definitions will remain unchanged.

## Initial audit

The inherited `lake build` passed, reporting 3419 jobs. Its transcript is saved in `baseline-build.txt`. This is a baseline check, not verification of a new lower bound.

The existing finite margin-sensitive count is a written theorem. Its reciprocal approximation and conditional sign-preservation step are Lean-checked in `HeadComplexity.Research.ConditionedReciprocalApproximation`. The full polynomial parameter construction, finite union count, and Warren theorem are not supplied there.

The existing declaration `HeadComplexity.worstCaseHeadComplexity_gt_div_of_warren` takes `WarrenStrictSignPatternBound` as an explicit premise. Its standard-axiom audit does not eliminate that premise. It must not be described as an unconditional kernel proof of the analytic counting theorem.

## Parallel investigations

- Audit the finite count and derive the two requested margin regimes with explicit constants and head overhead.
- Seek a truth-table-preserving admissible margin repair; test the first failed structural lemma.
- Seek a different unrestricted capacity bound that uses positivity or the Boolean input structure.
- Formalize the precise original-model relative margin and truth-table quantifiers, while investigating whether singular low-margin strata can be counted separately.

The first substantive checkpoint will record elapsed time, the strongest proved statement, the decisive inequality or obstruction, and the next different attempt. A conditional theorem, an auxiliary margin count, and an inherited green build are checkpoints only.

## Early verified checkpoint, approximately 17 minutes

The finite high-margin audit is committed as `5576475`. Both requested scales have the explicit sufficient threshold and overhead constants recorded in `finite_count_audit.md`.

A complete Warren proof was found in the permitted prior-run repository and imported without changing existing definitions. Its 13-module build and transitive audit of 101 declarations passed. The provenance, exact theorem interface, and evidence are recorded in `warren-provenance.md`. This makes the existing quadratic-denominator lower bound unconditional in this checkout; it is inherited mathematics, not a new exponent gain.

The new module `Research.RelativeMarginQuantifiers` checks the exact full-cube amplitude definition, the existence of a nonquantitative common positive margin at fixed dimension and width, and the precise high-margin plus universally-low-margin counting implication for the original worst-case complexity. It also proves that adding one cancelled constant head makes the relative margin arbitrarily small while preserving the entire score table. Thus an existentially bad representation cannot identify a bad truth table.

The repair route has a stronger written obstruction with a checked approximation lemma: a fixed pencil can force every numerator refit, including arbitrary repeated denominators, to have a margin exponentially small in width divided by dimension. Changing the denominator dictionary is not excluded. The next attempt permits all new poles along a fixed direction, then examines genuinely changing directions. The independent capacity route is examining the Boolean address cost in factorial interpolation examples and a normalized finite count with better constants.
