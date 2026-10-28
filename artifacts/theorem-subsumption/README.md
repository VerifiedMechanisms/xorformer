# Certified Theorem-Selection Audit

This audit applies
[`theorem-subsumption`](https://github.com/pevogam/theorem-subsumption) version
0.2.0 at commit `112d2d977cb3c1daa452a9ed6db6561fd025f128` to the
assumption-generality and conclusion-strength criterion. It consists of a
38-note selection manifest and five normalized-contract spot checks.

## Criterion

For aligned theorem contracts, a source subsumes a target only when both of the
following obligations are certified:

1. The target requirements imply the source requirements.

2. The source guarantee implies the target guarantee without using the target
   requirements.

Strict subsumption additionally requires a certified refutation in the reverse
direction. Failed search remains `UNKNOWN`. A proof that uses the target
requirements is recorded as a contextual adapter and does not establish a
stronger conclusion.

## Certification Boundary

The tool compares Lean declarations rather than Markdown files. Version 0.2.0
does not yet implement semantic-domain plugins or corpus indexing. The audit
therefore uses the explicit numeric contracts in
`HeadComplexity/SelectionSubsumption.lean`. These expose lower bounds, upper
bounds, and exactness assumptions as separate fields before invoking the tool.

The generated comparison certificates are kernel checked and permit only
`propext`, `Classical.choice`, and `Quot.sound`. The normalization itself is
reviewable Lean code, but it has no checked bridge to the original `Results`
declarations. In particular, a reverse refutation may use an abstract numeric
tuple that no Boolean function realizes. The certificates therefore establish
relations between the displayed normalized contracts, not theorem-level strictness
for all 197 Markdown notes.

The file `selection.json` is a curated manifest, not the tool's schema-version-2
JSON output. The Lean module contains regression assertions for every recorded
status, so elaboration fails if a comparison changes. The manifest records this
boundary and the exact selected-note paths.

## Certified Comparisons

| Normalized source | Normalized target | Requirements | Context-free guarantees | Classification | Review effect |
| --- | --- | --- | --- | --- | --- |
| [Theorem 110 chain](../../theorems/04_recursions_and_cost_invariants/110_affine_cylinder_threshold_degree_sandwich.md) | [Theorem 48 headline upper bound](../../theorems/03_function_families_and_affine_geometry/048_affine_free_sparsity_upper_bound.md) | Equivalent | Forward `PROVED`, reverse `REFUTED` | Strict normalized-contract subsumption | Theorem 48 remains selected because its full note also contains sparsity-hierarchy and explicit degree consequences. |
| [Theorem 69 sandwich](../../theorems/03_function_families_and_affine_geometry/069_positive_projection_degree_tight_exact.md) | [Theorem 013 positive-projection upper bound](../../theorems/01_foundations_and_normal_form/013_positive_projection_sign_changes.md) | Equivalent | Forward `PROVED`, reverse `REFUTED` | Strict normalized-contract subsumption | The normalized sandwich formula is stronger. Theorem 013 remains a constructive dependency rather than a competing frontier item. |
| [Theorem 144 sandwich](../../theorems/05_positive_statistic_gates_and_grids/144_positive_order_one_bit_gate_sandwich.md) | [Theorem 141 tight equality](../../theorems/05_positive_statistic_gates_and_grids/141_degree_tight_positive_statistic_gate_classification.md) | Target implies source; reverse `UNKNOWN` | Both directions `REFUTED` | Incomparable; forward contextual adapter `PROVED` | Both remain selected. Equality needs the target's tightness assumption. |
| [Theorem 93 raw-cost bound](../../theorems/04_recursions_and_cost_invariants/093_raw_calibrated_vote_support_bound.md) | [Theorem 85 explicit calibration bound](../../theorems/04_recursions_and_cost_invariants/085_calibrated_threshold_vote_upper_bound.md) | Target implies source; reverse `UNKNOWN` | Both directions `REFUTED` | Incomparable; forward contextual adapter `PROVED` | Both remain selected because their applicability and numerical endpoints trade off. |
| [Theorem 173 optimized multigrid bound](../../theorems/05_positive_statistic_gates_and_grids/173_positive_multigrid_cost_invariant.md) | [Theorem 170 fixed-certificate and fiber bounds](../../theorems/05_positive_statistic_gates_and_grids/170_positive_lexicographic_multigrid_bound.md) | Target implies source; reverse `UNKNOWN` | Both directions `REFUTED` | Incomparable | Both remain selected. Optimization strengthens the upper endpoint, while theorem 170 retains a concrete-certificate premise and fiber lower bounds. |

The five certified spot checks do not justify a membership change in the 38-note
selected frontier. Keeping the selected set unchanged is the review outcome, not
a corpus-wide certificate. The material change is to replace informal
specialization claims with the tool's sharper distinction between logical
subsumption, contextual adaptation, and incomparability.

## Reproduction

From the repository root:

```sh
cd formalization
lake env lean HeadComplexity/SelectionSubsumption.lean
```

This emits the tool's human-readable report and checks the recorded statuses.
It does not regenerate the curated `selection.json`. The command is a small
comparison-only elaboration and does not run the excluded four-bit exhaustive
archive check.
