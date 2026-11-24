# Kernel-checked literal pure RoPE architecture

The pure rotary architecture and its scalar normal form are equivalent in Lean, for every finite input length and every head count. The explicit separating function therefore satisfies

$$ H^{\ast} _{\text{literal pure RoPE}}(f)=3\lt4\leq H^{\ast} _{\mathrm{vanilla}}(f)\leq5. $$

There is no remaining unformalized step in this architectural separation. The original vanilla model, scalar atom definitions, strict threshold convention, and head-count definitions are unchanged.

## Literal model

[PureRoPEFamily](../../../formalization/HeadComplexity/Model/PureRoPE.lean) has a positive model dimension and an even positive head dimension, with separate query, key, value, and output linear maps for each head. All heads share one embedding for each of the three tokens. There are no additive positional embeddings. Only queries and keys are rotated; values depend only on the token. Attention includes every input and the fixed query token itself. The classifier reads the full query residual against an arbitrary linear readout and threshold.

The standard schedule at head dimension $d=2m$ is

$$ \omega_r=10000^{-r/m}=10000^{-2r/d},\qquad 0\leq r\lt m. $$

The implementation indexes input positions from zero and puts the query at position $n$. `oneIndexed_weight_eq` proves that positions one through $n$ and query position $n+1$ give exactly the same weights. `headUpdate_eq_weighted_sum` identifies the normalized numerator implementation with the usual sum of softmax-weighted projected values.

## Proof chain

| Component | Kernel-checked declarations | Source |
| --- | --- | --- |
| Standard frequencies | `frequency_standard_schedule`, `node_injective` | [RoPEFrequencies.lean](../../../formalization/HeadComplexity/Analysis/RoPEFrequencies.lean) |
| Literal planar rotation matrices | `blockRotate_add`, `blockRotate_inner`, `blockRotate_inner_relative` | [RotaryBlocks.lean](../../../formalization/HeadComplexity/Model/RotaryBlocks.lean) |
| Trigonometric interpolation | `interpolate_square`, `interpolate_standard` | [RoPEInterpolation.lean](../../../formalization/HeadComplexity/Analysis/RoPEInterpolation.lean) |
| Theorem 14's sharp width bound | `RoPEPairedInterpolation.interpolate_standard` | [RoPEPairedInterpolation.lean](../../../formalization/HeadComplexity/Analysis/RoPEPairedInterpolation.lean) |
| Shared embeddings and exact realization | `tokenMap_embedding`, `PureRoPERealization.exists_family` | [RoPETokenMaps.lean](../../../formalization/HeadComplexity/Analysis/RoPETokenMaps.lean), [PureRoPERealization.lean](../../../formalization/HeadComplexity/Model/PureRoPERealization.lean) |
| Realization at every sufficient even width | `PureRoPEPairedRealization.exists_family_at_width` | [PureRoPEPairedRealization.lean](../../../formalization/HeadComplexity/Model/PureRoPEPairedRealization.lean) |
| Arbitrary positive weights and exact residual scores | `pureRoPE_exists_exact_positive_weights`, `pureRoPE_residual_score_iff_atoms` | [PureRoPEExactScore.lean](../../../formalization/HeadComplexity/Results/PureRoPEExactScore.lean) |
| Position and residual conventions | `oneIndexed_weight_eq`, `residual_computability_iff` | [RoPEArchitectureConventions.lean](../../../formalization/HeadComplexity/Analysis/RoPEArchitectureConventions.lean) |
| Architectural head counts | `literalPureRoPEResidualHStar_eq_pureRoPEHStar`, `explicit_literal_complexities`, `explicit_literal_residual_strict_separation` | [PureRoPEArchitecture.lean](../../../formalization/HeadComplexity/Results/PureRoPEArchitecture.lean) |

The interpolation proof establishes distinctness of the complex exponential frequency nodes, proves the Vandermonde determinant nonzero, and uses its inverse to interpolate the finite logit sequence. Multiplying the coefficients by a query-position phase and taking real parts gives the required real cosine and sine coefficients. Using both positive and negative frequency nodes proves interpolation whenever $n\leq2m$. No rank, interpolation, or surjectivity statement is assumed.

The main realization chooses model dimension three and head dimension $2(n+2)$. The stronger `exists_family_at_width` allows every positive even head dimension at least $n$. The three shared embeddings are coordinate vectors. Linear maps send these vectors to the required token keys, common query vector, and token-only values. The query key realizes its self-logit independently, and its value is the atom's query numerator divided by its positive self-weight. The readout is orthogonal to the fixed query embedding, so the realized residual score is exactly the atom sum. This works for zero inputs and zero heads as well.

Necessity extracts the positive weights and three scalar token values from an arbitrary literal architecture. Its fixed residual contributes one scalar constant. Thus the equivalence preserves every real score and every head count, rather than only approximating Boolean labels.

## Reproduce the verification

From the repository root:

```bash
cd formalization
lake build
cd ..
python3 artifacts/rope/explicit_separation/audit_lean.py
bash artifacts/scripts/validate.sh
```

The headline audit and the all-theorem validator permit only `propext`, `Classical.choice`, and `Quot.sound`. There are no added axioms or proof placeholders.

The completed validation built 3,321 jobs and audited 2,677 theorem declarations across all 145 tracked Lean modules, including 84 headline aliases. The build, placeholder scan, and all-theorem axiom audit each exited successfully. The five updated documentation files also passed static math lint, KaTeX validation, and faithful GitHub rendering, with 405 recognized math spans.

## Scope

The requested pure rotary bridge and the resulting architectural separation are complete. The separate literal retained-position architecture is not formalized by these modules. The exact vanilla count of the separating function, four or five, remains open. The optional explicit rational five-head step retains a handwritten finite-difference error estimate; the existence of a five-head vanilla realization and the architectural separation are independently kernel-checked.
