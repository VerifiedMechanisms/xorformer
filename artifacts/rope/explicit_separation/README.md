# Explicit pure RoPE separation certificate package

[Theorem 22](../../../theorems/03_rotary_attention/022_explicit_pure_rope_separation.md) gives an explicit Boolean function on $14\cdot2^{400000}$ bits with threshold degree three, exactly three pure RoPE heads, and either four or five vanilla heads. The formula, every rational pure atom parameter, the strict full-cube margin, and the scalar-to-architecture bridge are in that theorem.

The lower bound allows arbitrary vanilla parameters within the original model. It does not assume that a competitor shares coefficients within the replicated groups. Averaging is used to obtain a sign polynomial, and only its coefficients on three distinct groups are passed to the unrestricted cubic obstruction.

## Reproduce the arithmetic certificates

Run from the repository root:

```bash
heavy python3 artifacts/rope/explicit_separation/verify.py
```

Only the Python standard library is required. The driver calls the exact certificates below and then checks the rational denominator gap, replicated atom identities, strict-margin constants, and finite-grid inequalities. It does not enumerate an astronomical cube. The full-cube verification is symbolic: the cleared polynomial has a common rational denominator, every attention denominator is positive, and a fixed negative rational readout shift handles zero values.

[construction.json](construction.json) is the machine-readable function and scalar-parameter certificate. It stores the input length as a power expression, all 42 integer numerator coefficients, all 42 integer denominator coefficients, rational base masses and biases, all three atom parameter lists, the replication rules, five explicit vanilla affine fractions giving the improved upper bound, and the earlier seven-head certificate. The driver checks these data against the defining formulas without printing or enumerating the enormous input dimension. The head-count claims in the JSON refer to the mathematical theorem; the driver checks their arithmetic ingredients, not the full lower-bound argument.

| Artifact | Exact checks |
| --- | --- |
| [Construction data](construction.json) | Explicit coefficient arrays, rational atoms, replication count, classifier formula, and threshold shift |
| [Generic cubic verifier](../generic_cubic_completion/verify.py) | Pure mass bounds, all 3003 six-row Vandermonde minors, and 182 cross-Hessian minors |
| [Chart verifier](../generic_cubic_completion/verify_chart.py) | Rational coordinate inverse, zero-chart bounds, denominator bounds, graph-restriction rank 679, interpolation constants, and cleared polynomial bounds |
| [Gap verifier](../quantitative_cubic_gap/verify_gap.py) | Every rational inequality in the uniform tensor exclusion radius |
| [Five-head upper certificate](../five_head_upper/README.md) | Exact oriented denominator combination and five reciprocal fractions |
| [Combined verifier](verify.py) | The preceding checks, exact atom constant identities under replication, full-cube arithmetic gap, and comparison of interpolation error with the tensor exclusion radius |

These scripts independently certify the arithmetic used in the proof. The complete Boolean lower bound is separately Lean-certified, including quantitative tensor recovery, finite sign rigidity, and averaging every admissible untied vanilla representation. The raw gap uses finite determinant estimates, with no spectral argument. The scalar-to-literal-RoPE matrix realization is now also Lean-certified, including standard-frequency interpolation and full residual readout; see the [architecture proof guide](../literal_architecture/README.md).

The actual unshifted formula's pure upper bound, rational tie removal, strict full-cube margin, and non-complement-invariance are Lean-checked in `Results/PureRoPEReplicationStrict.lean`. The improved five-head vanilla bound is checked in `Results/PureRoPEReplicationFive.lean`; the earlier general seven-head compiler remains in `Results/ThreeFractionsSevenHeads.lean`. For the displayed rational five-head step, `Polynomial/PureCubicFiveDenominators.lean` checks every denominator's admissibility, while Theorem 22 supplies the explicit finite-difference error estimate. To rebuild the formalized results and audit the axioms of every headline declaration, run from the repository root:

```bash
cd formalization
lake build HeadComplexity.Results.All
cd ..
python3 artifacts/rope/explicit_separation/audit_lean.py
```

The audit permits only `propext`, `Classical.choice`, and `Quot.sound`. The complete separation is `HeadComplexity.PureRoPEExplicitSeparation.strict_separation` in [PureRoPEExplicitSeparation.lean](../../../formalization/HeadComplexity/Results/PureRoPEExplicitSeparation.lean). That file also proves `not_vanilla_three`, `pureHStar_eq_three`, `vanillaHStar_bounds`, `shared_strict_separation`, and `not_universal_equality` without unproved hypotheses. The exact threshold degree three is `PureRoPEExplicitThreshold.thresholdDeg_eq_three` in [PureRoPEExplicitThreshold.lean](../../../formalization/HeadComplexity/Results/PureRoPEExplicitThreshold.lean).

## Research track and artifact manifest

The successful construction uses replication and finite sign rigidity. The following earlier tracks produced useful certified results, but did not produce the final separation.

| Track | Certified result or precise outcome | Artifacts |
| --- | --- | --- |
| Two pure heads versus three vanilla heads | Universally impossible: every two-pure-head Boolean classifier has a two-vanilla-head representation. A constructive rational compiler checked all 830 prior pure certificates. | [Theorem 16](../../../theorems/03_rotary_attention/016_pure_rope_two_head_equality.md), [compiler](../counterexample_search/compile_pure_two.py) |
| Seven-bit retained example | Its retained separation does not imply a pure separation. Pure obstructions and variants were treated separately. | [Theorem 15](../../../theorems/03_rotary_attention/015_pure_rope_two_heads_complement_invariant.md) |
| Twelve-bit quadratic target | The target has four heads in both models; the proposed pure-three route is rigorously blocked. | [Theorem 17](../../../theorems/03_rotary_attention/017_pure_rope_twelve_bit_obstruction.md), [exact certificates](../prior_obstructions/verify_twelve_pair.py) |
| Mixed conjunction families | Exact matching three-head certificates on 12, 18, and 24 bits, all of threshold degree three. Larger tested continuations remain unresolved. | [Search report and verifiers](../counterexample_search/README.md) |
| Asymmetric parity extensions | Exact vanilla-three certificates for the tested pure-three classifiers, including 56 balanced extensions on 10 or 12 bits. Failed fits and solver timeouts were superseded by exact upper certificates. | [Higher-search certificates](../higher_search/README.md), [balanced certificates](../counterexample_search/exact_balanced_extensions.jsonl) |
| Four-head selector patterns | The original 404-point pattern is impossible for pure four heads by a Gram obstruction. Replacement and complemented patterns had no certified pure realization. A near-fit radial function has an exact vanilla-three representation. | [Theorem 19](../../../theorems/03_rotary_attention/019_four_head_local_orientation_obstruction.md), [radial certificate](../counterexample_search/exact_radial_selector.json) |
| Cubic and quartic face patterns | All-vanilla lower criteria and explicit polynomial completions were certified. Exact pure coefficient matrices meet the desired orientation inequalities, but their actual score labels were not certified on all required faces. | [Theorems 20](../../../theorems/03_rotary_attention/020_three_head_tripartite_face_obstruction.md) and [21](../../../theorems/03_rotary_attention/021_four_head_quartic_face_obstruction.md), [search scope](../three_head_cubic_faces/README.md) |
| Auxiliary contexts | An exact one-hot pure embedding criterion was proved. Independent local fits alone did not establish a joint architecture. | [Context bridge](../pure_context_bridge/README.md) |

The exact cubic and quartic coefficient certificates in [counterexample_search](../counterexample_search/README.md) remain coefficient relaxations. Their large orientation margins do not provide a Boolean lower bound by themselves. No failed numerical fit, bounded mixed-integer infeasibility, or exact-score obstruction is used as the final lower bound.

The original model definitions, strict threshold convention, and admissibility conditions were not changed. New definitions describe constructions, proof intermediates, and search diagnostics.

## Remaining questions

The exact vanilla count of the explicit function is either four or five. A substantially smaller separating truth table remains open. The literal rotary interpolation bridge is fully Lean-certified, so no architectural gap remains in the separation. The earlier small face-pattern targets also remain unresolved where their documentation says no pure realization was certified.
