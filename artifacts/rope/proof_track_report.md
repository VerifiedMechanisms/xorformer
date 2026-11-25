# Pure RoPE Separates Every Head Budget Above Two

## Result

The requested universal equality is false in the unchanged xorformer model. The universal reverse implication holds exactly at head budgets at most two. The complete Boolean separation at every larger head budget is proved in Lean, including the bridge to literal rotary attention with standard fixed or freely chosen frequencies.

Starting from commit `bdca97f`, [Theorem 23](../../theorems/03_rotary_attention/023_pure_rope_separation_every_head_count.md) constructs an explicit family $f_{H,m}$ on $2H^2m$ bits for every $H\geq3$. For all sufficiently large $m$,

$$ H^{\ast}_{\mathrm{pure\ RoPE}}(f_{H,m})=H,\qquad H+1\leq H^{\ast}_{\mathrm{vanilla}}(f_{H,m})\leq2^H-2. $$

Every function in the explicit family is coordinatewise monotone. Thus the same universal cutoff holds even when the question is restricted to monotone Boolean functions. Monotone separating functions exist at every sufficiently large input length for each fixed budget above two.

The arbitrary-head proof is fully Lean-checked and independently audited. Its three-head specialization is the family $f_m=f_{3,m}$ on $18m$ bits. For every sufficiently large positive integer $m$,

$$ H^{\ast}_{\mathrm{pure\ RoPE}}(f_m)=3\qquad\text{and}\qquad4\leq H^{\ast}_{\mathrm{vanilla}}(f_m)\leq6. $$

The threshold convention remains strict positivity. The result concerns exact Boolean classification. No equality of pure and vanilla real-valued scores is assumed. Retained positional embeddings are not used.

The main declaration is `PureGeneralReplicatedGrid.eventually_complexity_separation_general` in [PureGeneralSeparation.lean](../../formalization/HeadComplexity/Results/PureGeneralSeparation.lean). It has no residual lower-bound premise. The following declarations give the direct answers to the original question:

- `universal_pure_to_original_vanilla_iff_head_le_two` and `universal_pure_to_vanilla_iff_head_le_two` in [RoPEUniversalBudgets.lean](../../formalization/HeadComplexity/Results/RoPEUniversalBudgets.lean): the universal head-preserving implication holds exactly for $H\leq2$. The same file proves the literal standard-frequency and free-frequency versions.

- `eventually_not_vanilla_general` in [PureGeneralSeparation.lean](../../formalization/HeadComplexity/Results/PureGeneralSeparation.lean): the explicit pure family eventually has no vanilla realization at the same budget, for every $H\geq3$.

- `pureRoPE_separation_every_budget_every_large_input_length` in [PureGeneralSeparationAllLargeInputs.lean](../../formalization/HeadComplexity/Results/PureGeneralSeparationAllLargeInputs.lean): for each $H\geq3$, every sufficiently large input length has a separating function with pure minimum $H$. Exact dummy-input invariance preserves all four minimum counts. `pureRoPE_separation_every_budget_original_minimum` states the same result directly with the original `HStar`.

- `not_universal_pureRoPEHStar_eq_HStar` in [PureThreeSeparation.lean](../../formalization/HeadComplexity/Results/PureThreeSeparation.lean): explicit negation of universal equality with the original vanilla minimum. Corresponding declarations cover shared embeddings and both rotary-frequency minima.

- `universal_monotone_pure_to_vanilla_iff_head_le_two` and `monotone_pureRoPE_separation_every_budget_every_large_input_length` in [PureGeneralMonotoneSeparation.lean](../../formalization/HeadComplexity/Results/PureGeneralMonotoneSeparation.lean): the sharp cutoff and every-large-input separation hold within monotone Boolean functions, using the original vanilla definitions.

The complete mathematical proofs are [Theorem 22](../../theorems/03_rotary_attention/022_pure_rope_three_head_separation.md) and [Theorem 23](../../theorems/03_rotary_attention/023_pure_rope_separation_every_head_count.md).

For the three-head family, a separately audited [effective bound](research/effective_replication_threshold.md) proves that $m\geq10^{40000}$ suffices. Thus $m=10^{40000}$ gives a specified finite counterexample, albeit an enormous one. This numerical threshold is a mathematical result, not a Lean declaration; the complete Lean theorem proves the existence of a threshold.

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

The complete general Lean proof passes through these interfaces:

- `PureGeneralReplicatedGrid.pure_computable`, `standard_computable`, and `free_computable` in [PureGeneralReplicatedGrid.lean](../../formalization/HeadComplexity/Results/PureGeneralReplicatedGrid.lean): the explicit genuine pure family for arbitrary $H$.

- `RoPEGeneralPolynomial.core_irreducible`, `core_totalDegree`, and `scalar_multiple_of_core_dvd` in [RoPEGeneralIrreducible.lean](../../formalization/HeadComplexity/Polynomial/RoPEGeneralIrreducible.lean).

- `RoPEGeneralPolynomial.core_dvd_of_weak_sign_on_open` and `no_lower_degree_weak_sign_on_open` in [RoPEGeneralLocalDivisibility.lean](../../formalization/HeadComplexity/Polynomial/RoPEGeneralLocalDivisibility.lean), supported by a dimension-independent rational-graph divisibility theorem in [LinearSourceDivisibility.lean](../../formalization/HeadComplexity/Polynomial/LinearSourceDivisibility.lean).

- The coordinate inverse, denominator-kernel dimension, all-ones vector, and nonnegative-cone obstruction in [RoPEGeneralCoordinates.lean](../../formalization/HeadComplexity/Atoms/RoPEGeneralCoordinates.lean).

- `ReplicatedThresholdDegree.eventually_not_thresholdDegLE` in [ReplicatedThresholdDegree.lean](../../formalization/HeadComplexity/Polynomial/ReplicatedThresholdDegree.lean): the complete arbitrary-degree averaging and dense-grid limit pipeline, with an explicit continuous weak-sign obstruction premise.

- `VanillaGeneralCentered.exists_averaged_data_of_vanilla` in [VanillaGeneralCentered.lean](../../formalization/HeadComplexity/Polynomial/VanillaGeneralCentered.lean): an actual vanilla classifier supplies strict averaged polynomials, oriented denominator rows, and exactly preserved top squarefree coefficients.

- `VanillaCoefficientLimit.factor_limit_of_vanilla_sequence` in [VanillaCoefficientLimit.lean](../../formalization/HeadComplexity/Polynomial/VanillaCoefficientLimit.lean): arbitrary vanilla representations on unbounded grids give a nonzero scalar multiple of the physical source as a top-coefficient limit.

- `BlockCoefficientLimit.tendsto_contractDiagonal_coeff` in [BlockCoefficientLimit.lean](../../formalization/HeadComplexity/Polynomial/BlockCoefficientLimit.lean): those coefficient limits imply convergence of contractions along moving kernel vectors, without bounded factor parameters.

- `contractMap_scaled_localSource_rank_le_iff` in [RoPEGeneralPhysicalRank.lean](../../formalization/HeadComplexity/Polynomial/RoPEGeneralPhysicalRank.lean) and `no_conditionally_oriented_polynomial_rank_limit` in [RoPESequentialFrames.lean](../../formalization/HeadComplexity/Atoms/RoPESequentialFrames.lean): the source rank locus and compact-frame contradiction, including zero denominator matrices.

- `PureGeneralReplicatedGrid.oriented_factor_limit_excluded` in [PureGeneralSeparation.lean](../../formalization/HeadComplexity/Results/PureGeneralSeparation.lean): unconditional discharge of the complete factor-limit obstruction. The same file assembles the final separation at every budget above two.

- `exists_oriented_top_coefficient_gap` in [PureGeneralCoefficientGap.lean](../../formalization/HeadComplexity/Results/PureGeneralCoefficientGap.lean): a positive uniform coefficient gap from every oriented factor sum, with unrestricted parameter sizes.

The conditional intermediate interfaces are all discharged in the final declarations. The exact pure minimum follows separately from `eventually_exact_degree_and_pure_minima_of_pos` in [PureGeneralThresholdDegree.lean](../../formalization/HeadComplexity/Results/PureGeneralThresholdDegree.lean).

Monotonicity follows from the source coefficients themselves. Each numerator coefficient is at least two, each denominator coefficient has absolute value at most one, and the denominator constant dominates the numerator mass on the whole cube. Cross-multiplication therefore makes every coordinate increase strictly increase each head score. `score_monotone_on_cube` in [PureGeneralMonotonicity.lean](../../formalization/HeadComplexity/Results/PureGeneralMonotonicity.lean) checks this directly, without differentiation. Replicated means and dummy-input padding preserve the pointwise order.

## Other proved results

The two-head complement-invariance assumption can be removed. `pureRoPEComputable_iff_vanilla_of_le_two` in [RoPETwoHeads.lean](../../formalization/HeadComplexity/Results/RoPETwoHeads.lean) proves equality at every head budget at most two for every input length. The proof uses the special positive token-endpoint numerator direction and a finite strict-sign perturbation. No antipodal symmetry is required.

`pureRoPEComputable_iff_vanilla_of_input_le_four` in [RoPEFourInputs.lean](../../formalization/HeadComplexity/Results/RoPEFourInputs.lean) proves equality at every head count for at most four input bits. Integer three-head certificates cover every nonparity four-bit truth table; the existing symmetric theory handles parity. These finite certificates are kernel-checked without new axioms.

The all-head structured results include `AffineStatistic.computable_of_collinear_denominators` and `AffineStatistic.computable_of_denominator_plane`. General positive affine ratios admit the finite-difference bound of $2^H-1$ vanilla heads. For pure classifiers and $H\geq2$, `pureRoPEComputable_vanilla_improved_exponential_bound` in [PureFiniteDifference.lean](../../formalization/HeadComplexity/Results/PureFiniteDifference.lean) improves this to $2^H-2$. Complement-invariant three-head pure classifiers use at most four vanilla heads by `vanilla_four_of_pureRoPE_three_complement`.

The first three replications of the three-head family are completely understood, with respective minima one, three, and one. `classifier_one_head_minima` in [PureSourceLinearApproximation.lean](../../formalization/HeadComplexity/Results/PureSourceLinearApproximation.lean) gives minimum one in all models at $m=1$. `classifier_two_head_minima` in [PureSecondReplicationDegree.lean](../../formalization/HeadComplexity/Results/PureSecondReplicationDegree.lean) gives minimum three and threshold degree three at $m=2$. The lower bound uses a balanced antipodal moment certificate; the upper bound uses an explicit denominator reorientation by the common linear statistic. `classifier_three_head_minima` in [PureThirdReplicationLinear.lean](../../formalization/HeadComplexity/Results/PureThirdReplicationLinear.lean) proves the third replication is again a weighted majority, using a sharper covariance estimate. `classifier_even_pure_head_minimum` in [PureReplicationDivisibility.lean](../../formalization/HeadComplexity/Results/PureReplicationDivisibility.lean) proves pure minimum three at every positive even replication. Exhaustive integer certificates give vanilla upper bound three through replication eight, including a second direct check of all 427,292,180 count patterns. These finite upper certificates are arithmetic computations outside Lean. At replication nine, `common_shift_nine_disagrees` excludes every admissible common denominator shift, without excluding other three-head representations. See [the exact small-replication proof](research/small_replication_exact_complexity.md).

At replication five, `classifier_five_not_isLTF` and `classifier_five_threshold_degree_lower` in [PureFifthReplicationNonlinear.lean](../../formalization/HeadComplexity/Results/PureFifthReplicationNonlinear.lean) give a kernel-checked lower bound of two using three positive and three negative inputs with identical first moments. A separately checked integer quadratic has the correct strict sign on all 16,777,216 count patterns, proving threshold degree exactly two outside Lean. The exact head minimum at this replication is either two or three and agrees in all models; the quadratic certificate alone does not determine it.

At replication seven, `classifier_seven_threshold_degree` and `classifier_seven_pure_head_minimum` in [PureSeventhReplicationDegree.lean](../../formalization/HeadComplexity/Results/PureSeventhReplicationDegree.lean) prove both quantities are exactly three. The quadratic lower bound uses six positive and six negative count vectors with equal first and second moments. The Lean proof includes the full bridge from arbitrary polynomials on 126 Boolean variables to the six count variables. Combined with the independently checked vanilla upper certificate, all architectural minima equal three at this replication. The same file proves threshold degree and pure minimum three for every positive multiple of seven; it makes no claim of a three-head vanilla upper bound at arbitrary multiples.

[HeadBudgetPullback.lean](../../formalization/HeadComplexity/Results/HeadBudgetPullback.lean) proves that surjective identification of input coordinates preserves both scalar head budgets by exact score identities. This gives monotonicity of all minimum counts along positive replication multiples for every source head count, formalized in [PureGeneralReplicationDivisibility.lean](../../formalization/HeadComplexity/Results/PureGeneralReplicationDivisibility.lean).

The literal architecture is formalized in [RectangularPureRoPE.lean](../../formalization/HeadComplexity/Model/RectangularPureRoPE.lean). `rectangularStandardPureRotaryComputable_iff_scalar` and `rectangularFreePureRotaryComputable_iff_scalar` hold for every input length and head count, including $n=0$ and $H=0$. Standard-frequency interpolation uses common finite width $2(n+2)$. The model has a fixed query attending to every input and itself, shared token embeddings, Q/K-only rotations, unrotated token-only values, explicit output projections, and the query residual. [RoPEBoundaryCases.lean](../../formalization/HeadComplexity/Results/RoPEBoundaryCases.lean) states the boundary cases explicitly: zero heads compute exactly constants, and every classifier on zero inputs has minimum zero in all four models.

[PureRoPEHeadSchedules.lean](../../formalization/HeadComplexity/Model/PureRoPEHeadSchedules.lean) also permits a separate free frequency list for each head. `rectangularHeadwiseFreePureRotaryComputable_iff_standard` proves that this broader convention has exactly the same head budgets. Scalar extraction even permits arbitrary finite head width and linear position schedules; common standard frequencies already realize every extracted score. [PureRoPEPositiveBase.lean](../../formalization/HeadComplexity/Model/PureRoPEPositiveBase.lean) proves the same exact class for every prescribed geometric frequency base $B\gt1$, with the same finite width; the canonical standard schedule is unchanged.

## Routes investigated and their limitations

[The research log](research_routes.md) records the distinct approaches and their checked scope. These include endpoint reorientation, strict-margin perturbation, projective denominator shifts, independent denominator shears, reciprocal finite differences, affine-statistic representations, denominator planes, product differences, arrowhead matrix transformations, Boolean zero-family tangents, value tilting, exact score approximation, and direct numerical searches.

Several attractive exact transformations fail. Checked obstructions show that a common projective shift cannot always orient all denominators, independent three-head shears cannot generally preserve the cleared polynomial, a prescribed cubic denominator pencil can be too restrictive, and value tilting can cross a Boolean decision boundary. Those failures alone are not Boolean lower bounds. The final separation instead excludes every alternative vanilla representation through the normalized polynomial limit. A [collision-cluster analysis](research/collision_cluster_residue_obstruction.md) proves further restrictions under full coefficient convergence, including arbitrary numerator divergence. Boolean averaging supplies only selected factor coefficients, so that analysis does not yet sharpen the four-to-six interval. An explicit multiscale example refutes a tempting extension of the regular common-base argument.

The search campaign produced 353 exact integer certificates of three-head vanilla representations for sampled pure classifiers. Failed searches were not treated as impossibility evidence. An exact dual certificate excludes one fixed endpoint-denominator proposal with arbitrary affine numerators; it does not exclude every three-head representation. See [the search report](search/three_head_search.md).

## Definitions, validation, and remaining questions

The original vanilla architectural and admissibility definitions are unchanged. The original scalar pure and retained atom definitions are also unchanged. New files add the literal pure rotary architecture, supporting lemmas, explicit families, and stronger results. Earlier theorem statements remain available; Theorem 16 strengthens the restricted two-head result, and Theorem 22 settles the previously open universal equality question negatively. Theorem 23 gives the fully formalized classification of all head budgets.

All final Lean results are checked without proof placeholders or new axioms. The permitted dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The repository validator builds every tracked Lean source and audits every theorem declaration. Mathematical Markdown is checked statically, with KaTeX, and through the real GitHub Markdown API. A GitLab render audit is unavailable in this environment because `glab` and GitLab authentication are absent.

The first separating $m$, the smallest possible input length, and the exact vanilla minimum within the proved intervals remain open. For the three-head family, the checked certificates exclude separation through $m=8$, and whether sufficiently large members need four, five, or six vanilla heads remains open. The two-head theorem and four-input theorem imply that any strict separation needs at least three pure heads, four vanilla heads, and five input bits. The explicit sufficient threshold $10^{40000}$ is not intended to be sharp. [RoPETensorGap.lean](../../formalization/HeadComplexity/Atoms/RoPETensorGap.lean) also proves the existence of a positive tensor-distance gap. The displayed numerical tensor constant and replication threshold remain mathematical results outside Lean; this does not leave a gap in the fully formalized existential Boolean separation.
