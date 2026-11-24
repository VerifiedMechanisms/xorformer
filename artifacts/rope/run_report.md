# RoPE Head Complexity Run Report

## Answer obtained

For all four requested variants, rotary head complexity is at most vanilla head complexity. Fixed standard frequencies and freely chosen frequencies give the same exact score class at unrestricted width, separately with and without additive positional embeddings.

The stronger universal equality with vanilla is unresolved in this run. No Boolean function with a strict head-count separation was found or certified.

The full definitions and proofs are in [the theorem writeup](../../theorems/03_rotary_attention/014_rope_head_complexity.md). The proved comparison is threshold degree at most retained-RoPE complexity, at most pure-RoPE complexity, at most vanilla complexity. Equality holds throughout for symmetric functions and whenever vanilla attains threshold degree.

A further handwritten construction shows that every two-head rotary classifier has a three-head vanilla realization. Thus any strict improvement using two rotary heads must be exactly two versus three.

## Machine-checked results

- [Atoms/RoPE.lean](../../formalization/HeadComplexity/Atoms/RoPE.lean): `AffineFraction.exists_pure` simulates every vanilla-admissible ratio exactly using one pure rotary scalar atom. `pureRoPEComputable_of_vanilla` lifts this to the existing shared-embedding vanilla classifier at each head count.
- [Results/RoPEComparison.lean](../../formalization/HeadComplexity/Results/RoPEComparison.lean): `pureRoPEHStar_le_vanilla`, `retainedRoPEHStar_le_pure`, and `thresholdDeg_le_retainedRoPEHStar` prove the scalar complexity chain. `ropeHStar_eq_vanilla_of_degree_tight` and `ropeHStar_symmetric` prove equality cases. Both one-head scalar classes are characterized as linear threshold functions.
- [Examples/RoPE.lean](../../formalization/HeadComplexity/Examples/RoPE.lean): `RoPEExamples.mixedReciprocal_no_vanilla_one_head_score` proves that one pure scalar head can realize an exact score unavailable to one vanilla head, even with a free constant. Every classifier obtained by thresholding that score still has vanilla complexity at most one.

The literal rotary matrices, the trigonometric Vandermonde interpolation proof, the unrestricted-positive-denominator characterization of retained RoPE, and the three-head vanilla upper bound for two-head rotary classifiers are handwritten, not Lean-checked. In particular, the formal minimum-count definitions are explicitly scalar models; the writeup supplies their architectural interpretation.

## Approaches that did not settle strictness

- Reversing the exact single-head score simulation is impossible, as the certified three-bit reciprocal example shows. This does not prevent a different vanilla score from having the same Boolean labels.
- Mixed denominator slopes alone do not prove a separation: the same cube function can have another ratio representation. The example avoids that ambiguity by proving impossibility against every admissible vanilla ratio, but still only separates exact scores.
- The existing ten-bit threshold-degree separation cannot distinguish the architectures. Its obstruction applies to all sums of two positive affine ratios, including the rotary variants.

No numerical optimization failure is used as a lower-bound certificate, and no large computational search was performed.

## Definition changes

Added `PureRoPEAtom`, `RetainedRoPEAtom`, their computability predicates and minimum counts, and `positiveFractionComputable`. Existing vanilla definitions and theorem statements are unchanged. The new results and examples are imported by the standard library umbrellas and indexed in the theorem ledger.

## Validation

- `bash artifacts/scripts/validate.sh`: all 47 tracked Lean modules built; 953 theorem declarations audited; only `propext`, `Classical.choice`, and `Quot.sound` occur as axioms; no proof placeholders.
- Static Markdown and KaTeX checks passed for the theorem and ledger: 255 math spans.
- GitHub's real Markdown API recognized all 174 theorem spans and all 81 ledger spans, with no residual math or escaped-payload errors. Authentication used the supplied repository token helper without printing the token.
- GitLab rendering was not audited because `glab` is unavailable in this environment.
- `git diff --check` passed.

## Remaining questions

Decide whether arbitrary positive affine denominators can strictly reduce classifier head count compared with vanilla-admissible denominators. This is exactly the retained-RoPE comparison. The pure-RoPE comparison is the analogous question for the token-only-value atom class.

The fixed/free frequency distinction is resolved; the unresolved issue is Boolean sign expressivity. Formalizing the literal rotary interpolation bridge would close the remaining Lean coverage gap in the proved architectural inequalities.
