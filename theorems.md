# Theorem index

Read the [definitions](definitions/README.md) first. The current chapter develops the normal form and bounds on head complexity.

## Chapter 1. Foundations and normal form

| Number | Theorem | Dependencies |
|---|---|---|
| 1.1 | [Head-to-atom reduction](theorems/01_foundations_and_normal_form/01_head_to_atom_reduction.md) | Model, score, atoms |
| 1.2 | [Atom-sum realization](theorems/01_foundations_and_normal_form/02_atom_sum_realization.md) | Model, score, atoms |
| 1.3 | [Coefficient admissibility](theorems/01_foundations_and_normal_form/03_coefficient_admissibility.md) | Atoms, admissible ratios |
| 1.4 | [Exact linear-fractional normal form](theorems/01_foundations_and_normal_form/04_exact_linear_fractional_normal_form.md) | Theorems 1.1–1.3 |
| 1.5 | [Head and ratio complexity](theorems/01_foundations_and_normal_form/05_head_and_ratio_complexity.md) | Theorem 1.4; computability and complexity definitions |
| 1.6 | [Zero-head constants](theorems/01_foundations_and_normal_form/06_zero_head_constants.md) | Model, score, classification, head complexity |
| 1.7 | [One-head characterization](theorems/01_foundations_and_normal_form/07_one_head_characterization.md) | Theorems 1.4 and 1.6; linear threshold functions |
| 1.8 | [Affine checkerboard nonseparability](theorems/01_foundations_and_normal_form/08_affine_checkerboard_nonseparability.md) | Classification, linear threshold functions, checkerboard restrictions |
| 1.9 | [Intersection of output diagonals](theorems/01_foundations_and_normal_form/09_intersection_of_output_diagonals.md) | Model, two-coordinate restrictions |
| 1.10 | [Checkerboard head bound](theorems/01_foundations_and_normal_form/10_checkerboard_head_bound.md) | Theorems 1.6–1.9; checkerboard restrictions |
| 1.11 | [Boolean polynomial interpolation](theorems/01_foundations_and_normal_form/11_boolean_polynomial_interpolation.md) | Strict sign representation, threshold degree |
| 1.12 | [Threshold-degree head bound](theorems/01_foundations_and_normal_form/12_threshold_degree_head_bound.md) | Theorems 1.4 and 1.11; computability, strict sign representation, complexity definitions |
| 1.13 | [Two-head denominator clearing](theorems/01_foundations_and_normal_form/13_two_head_denominator_clearing.md) | Theorem 1.4; computability, strict sign representation, real affine forms |
| 1.14 | [Weighted-sum interpolation upper bound](theorems/01_foundations_and_normal_form/14_weighted_sum_interpolation_upper_bound.md) | Model, score, classification, head complexity, positive weighted statistics |
| 1.15 | [Universal head bound](theorems/01_foundations_and_normal_form/15_universal_head_bound.md) | Theorem 1.14; positive weighted statistics, positive-image complexity, head complexity |
| 1.16 | [Symmetric threshold degree](theorems/01_foundations_and_normal_form/16_symmetric_threshold_degree.md) | Symmetric functions, sign-change count, strict sign representation, threshold degree |
| 1.17 | [Exact symmetric head complexity](theorems/01_foundations_and_normal_form/17_exact_symmetric_head_complexity.md) | Theorems 1.4, 1.6, 1.12, and 1.16; symmetric functions, sign-change count, admissible ratios, classification, head complexity |
| 1.18 | [Symmetric threshold complexity](theorems/01_foundations_and_normal_form/18_symmetric_threshold_complexity.md) | Theorem 1.17; model, score, classification, symmetric thresholds, sign-change count, head complexity |
| 1.19 | [Parity complexity](theorems/01_foundations_and_normal_form/19_parity_complexity.md) | Theorems 1.10, 1.12, 1.16, and 1.17; parity, sign-change count, strict sign representation, complexity definitions |
| 1.20 | [Exact-count complexity](theorems/01_foundations_and_normal_form/20_exact_count_complexity.md) | Theorems 1.10 and 1.17; exact-count predicates, sign-change count, head complexity |
| 1.21 | [Symmetric score interpolation](theorems/01_foundations_and_normal_form/21_symmetric_score_interpolation.md) | Theorem 1.14; model, score, positive weighted statistics, Hamming weight |

See the [chapter contents](theorems/01_foundations_and_normal_form/README.md) for the reading order. Theorems 1.5, 1.12, and 1.15 relate [threshold degree (Definition 1.13)](definitions/13_threshold_degree.md) $\deg_{\pm}(f)$, [head complexity (Definition 1.5)](definitions/05_head_complexity.md) $H^{\ast}(f)$, [ratio complexity (Definition 1.8)](definitions/08_ratio_complexity.md) $L(f)$, and [positive-image complexity (Definition 1.21)](definitions/21_positive_image_complexity.md) $M_{+}(f)$:

$$ \deg_{\pm}(f)\leq H^{\ast}(f)=L(f)\leq M_{+}(f)-1\leq2^n-1. $$
