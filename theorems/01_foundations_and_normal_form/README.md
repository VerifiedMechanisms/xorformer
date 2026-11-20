# Chapter 1. Foundations and normal form

Begin with the [definitions](../../definitions/README.md), then read the theorems in this order.

## Normal form

| Number | Theorem | Content |
|---|---|---|
| 1.1 | [Head-to-atom reduction](01_head_to_atom_reduction.md) | Extract one atom per attention head. |
| 1.2 | [Atom-sum realization](02_atom_sum_realization.md) | Realize an arbitrary atom sum with an explicit model. |
| 1.3 | [Coefficient admissibility](03_coefficient_admissibility.md) | Characterize the affine coefficient tuples obtained from atoms. |
| 1.4 | [Exact linear-fractional normal form](04_exact_linear_fractional_normal_form.md) | Identify realizable scores with sums of admissible ratios. |
| 1.5 | [Head and ratio complexity](05_head_and_ratio_complexity.md) | Identify minimum head and ratio counts. |

Theorems 1.1–1.3 use only the definitions. Theorem 1.4 combines those three results, and Theorem 1.5 applies Theorem 1.4 to classification.

## Zero heads, one head, and checkerboards

| Number | Theorem | Content |
|---|---|---|
| 1.6 | [Zero-head constants](06_zero_head_constants.md) | Characterize functions of head complexity zero. |
| 1.7 | [One-head characterization](07_one_head_characterization.md) | Characterize functions of head complexity one. |
| 1.8 | [Affine checkerboard nonseparability](08_affine_checkerboard_nonseparability.md) | Exclude affine classifiers for both checkerboard orientations. |
| 1.9 | [Intersection of output diagonals](09_intersection_of_output_diagonals.md) | Find a common point of the two projected output segments. |
| 1.10 | [Checkerboard head bound](10_checkerboard_head_bound.md) | Rule out zero and one head for any function containing a checkerboard restriction. |

Theorem 1.7 uses the normal form and Theorem 1.6. Theorems 1.8 and 1.9 use only the definitions. Theorem 1.10 gives an affine proof using Theorems 1.6–1.8 and a geometric proof using Theorems 1.6 and 1.9.

## Polynomial lower bounds

| Number | Theorem | Content |
|---|---|---|
| 1.11 | [Boolean polynomial interpolation](11_boolean_polynomial_interpolation.md) | Represent every cube function by a multilinear polynomial and establish finite threshold degree. |
| 1.12 | [Threshold-degree head bound](12_threshold_degree_head_bound.md) | Bound threshold degree by head complexity using positive denominator clearing. |
| 1.13 | [Two-head denominator clearing](13_two_head_denominator_clearing.md) | Express a two-head classifier's polynomial sign representation as two products of affine forms. |

Theorem 1.11 uses only the definitions. Theorem 1.12 uses the normal form and Theorem 1.11, including zero heads and an empty feasible set. Theorem 1.13 uses the normal form directly to obtain the two-product structure.

## Interpolation and upper bounds

| Number | Theorem | Content |
|---|---|---|
| 1.14 | [Weighted-sum interpolation upper bound](14_weighted_sum_interpolation_upper_bound.md) | Realize arbitrary scores on the levels of a positive weighted statistic and bound the heads needed for Boolean labels. |
| 1.15 | [Universal head bound](15_universal_head_bound.md) | Prove finite head complexity for every Boolean function using binary weights. |

Theorem 1.14 proves the reciprocal interpolation basis inside its proof and uses the normal form to realize the resulting score. Theorem 1.15 applies it to an injective statistic.
