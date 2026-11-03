# Certified Integration of the Independent Derivation

## Results and Preservation

The integration imports the improvements from the independent `automlr` derivation into the existing attention model. It preserves every pre-existing Lean source from `f4781ed`; `Results/All.lean` only gains imports and aliases.

| Result | Improvement | Proof surface |
| --- | --- | --- |
| [Theorem 199](../../theorems/02_complexity_measure_upper_bounds/199_neighborhood_interpolation_universal_bound.md) | The universal coefficient improves from $11$ to strictly below $3/2$ for $n\geq8$, preserving every earlier numerical endpoint. Fixed positive denominators also interpolate every numerical target. | `AffineZeroSetInterpolation`, `OpenNeighborhoodCover`, `SyndromeCover`, `SyndromeLift`, `SyndromeCoverCertificates`, `UniversalNeighborhoodBound` |
| Fixed-denominator width | The dimension obstruction and the universal cover give order $2^n/n$, with exact value $2^n/n$ at every power-of-two input dimension at least two. | `FixedDenominatorInterpolation` |
| [Theorem 200](../../theorems/06_strict_separations/200_fixed_degree_head_complexity_lower_bounds.md) | Exact-degree functions can require order $n^{d-1}/\log n$ heads for every fixed $d\geq2$. | `RestrictedCounting` and `FixedDegreeCounting` prove the exact finite counting implication, with explicit Warren and budget premises; the asymptotic conversion is in the writeup. |
| [Theorem 201](../../theorems/03_function_families_and_affine_geometry/201_addressing_exact_head_counts.md) | Addressing has threshold degree $r+1$, exact head counts $2,3,4$ for the first three address sizes, and a general data-dependent upper bound $2^r-1$ for $r\geq2$. | `AffineSubstitution`, `Addressing`, and `AddressingCertificates` kernel-check the threshold degree and exact cases. The general perturbation upper bound is proved in the writeup. |
| [Theorem 10 refinement](../../theorems/01_foundations_and_normal_form/010_linear_fractional_normal_form.md) | Shared width becomes at most $\min\lbrace3H,n+2\rbrace$, with a canonical construction using scalar heads. Finite strict polynomial systems have rational witnesses. | `SharedWidthNormalForm` and `RationalStrictWitness` |

All compiled declarations use the unchanged `FracAtom`, `computableWithHeadsN`, shared embedding model, `thresholdDeg`, and `HStar`. Finite certificates use `decide +kernel`, not a native-decision axiom.

## Five Strict Subsumption Comparisons

`HeadComplexity/AutomlrSubsumption.lean` uses the pinned theorem-subsumption package at commit `112d2d977cb3c1daa452a9ed6db6561fd025f128`. Every comparison asserts equivalent requirements, a proved context-free forward implication, a refuted reverse implication, and the classification `source strictly subsumes target under this alignment`.

| New contract | Baseline | Reverse numerical witness |
| --- | --- | --- |
| Joint neighborhood budget | Full previous `universalElevenStarBound`, including every earlier minimum | Dimension $16$, exposed head count $8192$; the new budget is at most $6143$ |
| Two-address-bit exactness | Specialized degree-sensitive interval $3\leq H^{\ast}\leq16$ | Exposed head count $4$ |
| Three-address-bit exactness | Specialized degree-sensitive interval $4\leq H^{\ast}\leq176$ | Exposed head count $5$ |
| Exact-degree maximum with the additional finite counting lower bound | Threshold-degree lower bound on that same maximum | Exposed degree $2$, head cutoff $3$, maximum $2$ |
| Joint shared-width budget | Previous direct-sum width budget $3H$ | Dimension $1$, head count $2$, exposed width $4$ |

These witnesses refute implications between the displayed numerical guarantees. They do not assert that the exposed head counts or widths are realized by Boolean functions. Requirement predicates separately connect each numerical scalar to the actual invariant.

The universal contracts share `HeadCountRealized`. The addressing contracts share equality to the literal `HStar` of `IDX`. The width contracts share `SharedWidthRealized`, which requires a feasible actual model and equality to `sharedWidthAtHeads`.

The fixed-degree comparison is explicitly conditional. Its common requirement bundle contains equality to `degreeClassHeadMaximum`, nonemptiness of the degree class, Warren's estimate, both parameter-dimension inequalities, and the strict combined pattern budget. The baseline lower bound uses only the old general threshold-degree theorem and the realized class. The source adds the newly proved finite lower bound. This certificate does not establish the asymptotic estimates or remove any analytic premise.

## Other Comparisons and Verification Improvements

Fixed-denominator interpolation is stronger data than a head upper bound and compiles through the pre-existing `ClearedSpanCertificate`. Its dimension lower bound does not lower-bound the head count of an individual Boolean function. No misleading strict comparison between these two invariants is asserted.

The self-contained [four-bit covector verifier](../calculations/verify_four_bit_covector_classification.py) independently reproduces theorem 183 using twelve two-head spaces and six three-head spaces. This is an alternative finite verification method for an existing result. It does not discharge the existing Lean archive premise.

The supplemental [construction verifier](../calculations/verify_automlr_constructions.py) checks the multi-coset covers, Cartesian lifts, finite six-target cover optimality, and general addressing perturbation identities. The universal theorem and the small addressing exactness results also have independent Lean proofs.

The re-derived normal form, symmetric formula, sparsity and formula bounds, finite interpolation widths through twelve inputs, and the leading worst-case counting coefficient are not introduced as additional novel theorem entries. The existing tangent matrix and tensor rank bounds are stronger than the corresponding independent inequalities. The new explicit Hadamard family is stated using the stronger existing tangent bound and an external spectral theorem.

## Reproduction

From the repository root:

```sh
bash artifacts/scripts/validate_automlr_improvements.sh
bash artifacts/scripts/validate.sh
```

The focused validator builds the new modules and the result umbrella with warnings treated as errors, rejects placeholders, audits every owned theorem including generated comparison certificates, reruns all five comparisons, checks both exact Python verifiers, and checks preservation of the baseline Lean sources.

The axiom allowlist is exactly `propext`, `Classical.choice`, and `Quot.sound`. Warren's inequality remains a proposition passed to the counting theorems, never a project axiom. No finite archive parser, external numerical verifier, or solver result is trusted by the new Lean theorems.

The [validation record](automlr-improvements-checks.txt) records the completed checks and the Markdown render-audit boundary.
