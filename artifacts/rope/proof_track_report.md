# Pure RoPE Separates Every Head Budget Above Two

## Result

The requested universal equality is false in the unchanged xorformer model. The universal reverse implication holds exactly at head budgets at most two. A complete mathematical proof separates every larger head budget. The complete three-head Boolean separation is proved in Lean, including the bridge to literal rotary attention with standard fixed or freely chosen frequencies.

Starting from commit `bdca97f`, [Theorem 23](../../theorems/03_rotary_attention/023_pure_rope_separation_every_head_count.md) constructs an explicit family $f_{H,m}$ on $2H^2m$ bits for every $H\geq3$. For all sufficiently large $m$,

$$ H^{\ast}_{\mathrm{pure\ RoPE}}(f_{H,m})=H,\qquad H+1\leq H^{\ast}_{\mathrm{vanilla}}(f_{H,m})\leq2^H-2. $$

The arbitrary-head mathematical argument has independent audits. Its formalization is partial, with the exact scope listed below. The fully Lean-checked specialization is the family $f_m=f_{3,m}$ on $18m$ bits. For every sufficiently large positive integer $m$,

$$ H^{\ast}_{\mathrm{pure\ RoPE}}(f_m)=3\qquad\text{and}\qquad4\leq H^{\ast}_{\mathrm{vanilla}}(f_m)\leq6. $$

The threshold convention remains strict positivity. The result concerns exact Boolean classification. No equality of pure and vanilla real-valued scores is assumed. Retained positional embeddings are not used.

The main declaration is `PureThreeReplicatedGrid.eventually_complexity_separation` in [PureThreeSeparation.lean](../../formalization/HeadComplexity/Results/PureThreeSeparation.lean). The same file proves:

- `eventually_not_vanilla_three`: the unconditional lower bound for the explicit family.

- `exists_complexity_separation`: existence of a Boolean function with pure minimum three and vanilla minimum between four and six.

- `exists_rotary_three_not_vanilla_three`: the literal rectangular architectures with standard and free frequencies both compute such a function with three heads.

- `not_universal_pureRoPE_to_vanilla_three` and `not_universal_pureRoPEHStar_eq_SharedHStar`: explicit negations of the requested universal implication and minimum-count equality. Corresponding declarations cover `HStar` and the standard-frequency and free-frequency minimum counts.

The complete mathematical proof is [Theorem 22](../../theorems/03_rotary_attention/022_pure_rope_three_head_separation.md). There is no residual unproved lower-bound premise in the final Lean declarations.

`pureRoPE_separation_every_large_input_length` in [PureSeparationAllLargeInputs.lean](../../formalization/HeadComplexity/Results/PureSeparationAllLargeInputs.lean) strengthens this to every sufficiently large input length, by padding with unused bits. [InputPaddingInvariance.lean](../../formalization/HeadComplexity/Results/InputPaddingInvariance.lean) proves that padding preserves all four minimum head counts exactly.

A separately audited [effective bound](research/effective_replication_threshold.md) proves that $m\geq10^{40000}$ suffices. Thus $m=10^{40000}$ gives a specified finite counterexample, albeit an enormous one. This numerical threshold is a mathematical result, not a Lean declaration; the complete Lean theorem proves the existence of a threshold.

## Why the separation works

The source score is a sum of three pure affine fractions on eighteen centered group means. Replication supplies increasingly fine Boolean grids. Each denominator is uniformly positive on the continuous cube, and each atom has strictly positive input and query masses. [PureThreeReplicatedGrid.lean](../../formalization/HeadComplexity/Results/PureThreeReplicatedGrid.lean) proves the exact scalar and literal rotary realizations.

Supposing infinitely many grids had vanilla three-head representations, strictification and denominator clearing would give cubic polynomials. Averaging within replica groups preserves their strict Boolean signs. Normalize the complete polynomial coefficient vectors and pass to a nonzero limit. Dense-grid sign agreement forces this limit to be a positive scalar multiple of the source cubic, using its irreducibility and a local rational parametrization of its zero hypersurface.

Only the mixed cubic coefficients with one coordinate in each of three blocks are retained. They preserve the actual vanilla numerator-denominator factorization exactly under averaging. Every vanilla tensor has a three-dimensional denominator-kernel frame whose contractions have rank at most three. The source tensor identifies that kernel through explicit four-by-four minors. In the limit, the kernel contains the all-ones vector, contradicting the normalized positive denominator row perpendicular to it.

The compactness argument never assumes bounded head parameters or convergence of a chosen rational representation. It normalizes whole polynomials, then separately extracts compact kernel frames and simplex normals.

The principal formal interfaces are:

| Step | Declaration and file |
|---|---|
| Actual vanilla score to strict centered factors | `VanillaThreeCentered.exists_data_of_vanilla`, [VanillaThreeCentered.lean](../../formalization/HeadComplexity/Polynomial/VanillaThreeCentered.lean) |
| Exact grouped averaging and surviving coefficients | `averagedGroupPolynomial_strict_sign`, `averagedGroupPolynomial_coeff_top_squarefree`, [RoPEGroupSymmetrization.lean](../../formalization/HeadComplexity/Polynomial/RoPEGroupSymmetrization.lean) |
| Actual vanilla representation supplies every required witness field | `PureThreeAveragedWitness.averagedWitness_of_vanilla`, [PureThreeAveragedWitness.lean](../../formalization/HeadComplexity/Results/PureThreeAveragedWitness.lean) |
| Nonzero coefficient subsequence and moving evaluations | `normalized_polynomial_subsequence`, `tendsto_eval_of_bounded_coefficients`, [BoundedCoefficientLimit.lean](../../formalization/HeadComplexity/Polynomial/BoundedCoefficientLimit.lean) |
| Source rigidity on the physical cube | `RoPEPhysicalCoordinates.positive_scalar_multiple_of_weak_sign_cube`, [RoPEPhysicalCoordinates.lean](../../formalization/HeadComplexity/Polynomial/RoPEPhysicalCoordinates.lean) |
| Closed tensor obstruction with arbitrary factor sizes | `RoPEThreeTensor.no_tendsto_scaled_physical_source_factorTensor`, [RoPETensorFactors.lean](../../formalization/HeadComplexity/Atoms/RoPETensorFactors.lean) |
| Complete compactness contradiction | `no_averaged_witness_sequence`, [PureThreeSeparationLimit.lean](../../formalization/HeadComplexity/Results/PureThreeSeparationLimit.lean) |

## The arbitrary-head strengthening

The general proof replaces the cubic minor computation with a uniform contraction-rank lemma. Write the homogeneous source as $W_H(D,N)=\sum_i N_i\prod_{j\neq i}D_j$. Its contraction in a direction $(d,a)$ has flattening rank at most $H$ exactly when $d=0$. If $d\neq0$, the kernel has dimension at most two and the rank is at least $2H-2\gt H$. This identifies the same paired denominator kernel in every dimension. Compact orthonormal frames and normalized positive denominator rows then give the general closed obstruction.

Irreducibility and local sign rigidity extend to every degree. Grouped averaging and coefficient compactness turn hypothetical finite Boolean classifiers into a nonzero weak-sign representative of the source. The source must be its positive scalar multiple. The top mixed tensor contradicts the closed obstruction. A separate smaller-degree argument proves that the pure minimum is exactly $H$.

The general Lean components currently include:

- `PureGeneralReplicatedGrid.pure_computable`, `standard_computable`, and `free_computable` in [PureGeneralReplicatedGrid.lean](../../formalization/HeadComplexity/Results/PureGeneralReplicatedGrid.lean): the explicit genuine pure family for arbitrary $H$.

- `RoPEGeneralPolynomial.core_irreducible`, `core_totalDegree`, and `scalar_multiple_of_core_dvd` in [RoPEGeneralIrreducible.lean](../../formalization/HeadComplexity/Polynomial/RoPEGeneralIrreducible.lean).

- `RoPEGeneralPolynomial.core_dvd_of_weak_sign_on_open` and `no_lower_degree_weak_sign_on_open` in [RoPEGeneralLocalDivisibility.lean](../../formalization/HeadComplexity/Polynomial/RoPEGeneralLocalDivisibility.lean), supported by a dimension-independent rational-graph divisibility theorem in [LinearSourceDivisibility.lean](../../formalization/HeadComplexity/Polynomial/LinearSourceDivisibility.lean).

- The coordinate inverse, denominator-kernel dimension, all-ones vector, and nonnegative-cone obstruction in [RoPEGeneralCoordinates.lean](../../formalization/HeadComplexity/Atoms/RoPEGeneralCoordinates.lean).

- `ReplicatedThresholdDegree.eventually_not_thresholdDegLE` in [ReplicatedThresholdDegree.lean](../../formalization/HeadComplexity/Polynomial/ReplicatedThresholdDegree.lean): the complete arbitrary-degree averaging and dense-grid limit pipeline, with an explicit continuous weak-sign obstruction premise.

These components do not by themselves constitute a Lean declaration of the entire arbitrary-head separation. The remaining assembly must connect the physical source, the actual vanilla factor tensors after averaging, their closed rank obstruction, and the final compactness contradiction. The full three-head declarations already contain all of these connections.

## Other proved results

The two-head complement-invariance assumption can be removed. `pureRoPEComputable_iff_vanilla_of_le_two` in [RoPETwoHeads.lean](../../formalization/HeadComplexity/Results/RoPETwoHeads.lean) proves equality at every head budget at most two for every input length. The proof uses the special positive token-endpoint numerator direction and a finite strict-sign perturbation. No antipodal symmetry is required.

`pureRoPEComputable_iff_vanilla_of_input_le_four` in [RoPEFourInputs.lean](../../formalization/HeadComplexity/Results/RoPEFourInputs.lean) proves equality at every head count for at most four input bits. Integer three-head certificates cover every nonparity four-bit truth table; the existing symmetric theory handles parity. These finite certificates are kernel-checked without new axioms.

The all-head structured results include `AffineStatistic.computable_of_collinear_denominators` and `AffineStatistic.computable_of_denominator_plane`. General positive affine ratios admit the finite-difference bound of $2^H-1$ vanilla heads. For pure classifiers and $H\geq2$, `pureRoPEComputable_vanilla_improved_exponential_bound` in [PureFiniteDifference.lean](../../formalization/HeadComplexity/Results/PureFiniteDifference.lean) improves this to $2^H-2$. Complement-invariant three-head pure classifiers use at most four vanilla heads by `vanilla_four_of_pureRoPE_three_complement`.

The first two replications of the three-head family are completely understood. `classifier_one_head_minima` in [PureSourceLinearApproximation.lean](../../formalization/HeadComplexity/Results/PureSourceLinearApproximation.lean) gives minimum one in all models at $m=1$. `classifier_two_head_minima` in [PureSecondReplicationDegree.lean](../../formalization/HeadComplexity/Results/PureSecondReplicationDegree.lean) gives minimum three and threshold degree three at $m=2$. The lower bound uses a balanced antipodal moment certificate; the upper bound uses an explicit denominator reorientation by the common linear statistic. See [the exact small-replication proof](research/small_replication_exact_complexity.md).

The literal architecture is formalized in [RectangularPureRoPE.lean](../../formalization/HeadComplexity/Model/RectangularPureRoPE.lean). `rectangularStandardPureRotaryComputable_iff_scalar` and `rectangularFreePureRotaryComputable_iff_scalar` hold for every input length and head count, including $n=0$ and $H=0$. Standard-frequency interpolation uses common finite width $2(n+2)$. The model has a fixed query attending to every input and itself, shared token embeddings, Q/K-only rotations, unrotated token-only values, explicit output projections, and the query residual. [RoPEBoundaryCases.lean](../../formalization/HeadComplexity/Results/RoPEBoundaryCases.lean) states the boundary cases explicitly: zero heads compute exactly constants, and every classifier on zero inputs has minimum zero in all four models.

[PureRoPEHeadSchedules.lean](../../formalization/HeadComplexity/Model/PureRoPEHeadSchedules.lean) also permits a separate free frequency list for each head. `rectangularHeadwiseFreePureRotaryComputable_iff_standard` proves that this broader convention has exactly the same head budgets. Scalar extraction even permits arbitrary finite head width and linear position schedules; common standard frequencies already realize every extracted score.

## Routes investigated and their limitations

[The research log](research_routes.md) records the distinct approaches and their checked scope. These include endpoint reorientation, strict-margin perturbation, projective denominator shifts, independent denominator shears, reciprocal finite differences, affine-statistic representations, denominator planes, product differences, arrowhead matrix transformations, Boolean zero-family tangents, value tilting, exact score approximation, and direct numerical searches.

Several attractive exact transformations fail. Checked obstructions show that a common projective shift cannot always orient all denominators, independent three-head shears cannot generally preserve the cleared polynomial, a prescribed cubic denominator pencil can be too restrictive, and value tilting can cross a Boolean decision boundary. Those failures alone are not Boolean lower bounds. The final separation instead excludes every alternative vanilla representation through the normalized polynomial limit.

The search campaign produced 353 exact integer certificates of three-head vanilla representations for sampled pure classifiers. Failed searches were not treated as impossibility evidence. An exact dual certificate excludes one fixed endpoint-denominator proposal with arbitrary affine numerators; it does not exclude every three-head representation. See [the search report](search/three_head_search.md).

## Definitions, validation, and remaining questions

The original vanilla architectural and admissibility definitions are unchanged. The original scalar pure and retained atom definitions are also unchanged. New files add the literal pure rotary architecture, supporting lemmas, explicit families, and stronger results. Earlier theorem statements remain available; Theorem 16 strengthens the restricted two-head result, and Theorem 22 settles the previously open universal equality question negatively. Theorem 23 gives the mathematical classification of all head budgets.

All final Lean results are checked without proof placeholders or new axioms. The permitted dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The repository validator builds every tracked Lean source and audits every theorem declaration. Mathematical Markdown is checked statically, with KaTeX, and through the real GitHub Markdown API. A GitLab render audit is unavailable in this environment because `glab` and GitLab authentication are absent.

The first separating $m$, the smallest possible input length, and the exact vanilla minimum within the proved intervals remain open. The complete arbitrary-head separation still needs its final Lean assembly. For the three-head family, $m=1$ and $m=2$ are not separating, and whether sufficiently large members need four, five, or six vanilla heads remains open. The two-head theorem and four-input theorem imply that any strict separation needs at least three pure heads, four vanilla heads, and five input bits. The explicit sufficient threshold $10^{40000}$ is not intended to be sharp. [RoPETensorGap.lean](../../formalization/HeadComplexity/Atoms/RoPETensorGap.lean) also proves the existence of a positive tensor-distance gap. The displayed numerical tensor constant and replication threshold remain mathematical results outside Lean; this does not leave a gap in the fully formalized existential Boolean separation.
