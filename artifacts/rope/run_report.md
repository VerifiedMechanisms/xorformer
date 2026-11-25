# RoPE Head Complexity Run Report

> **Historical report.** This records the starting branch before the proof-track follow-up. Its open-problem and formalization status is superseded by [the proof-track report](proof_track_report.md) and [Theorem 23](../../theorems/03_rotary_attention/023_pure_rope_separation_every_head_count.md).

## Answer obtained

For all four requested variants, rotary head complexity is at most vanilla head complexity. Fixed standard frequencies and freely chosen frequencies give the same exact score class at unrestricted width, separately with and without additive positional embeddings.

Universal equality of pure RoPE with vanilla remains unresolved. The follow-up settles retained-RoPE strictness: the seven-bit orientation function has retained complexity two, and pure and vanilla complexity three. No strict pure-RoPE head-count example was certified.

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

Retained-RoPE strictness is settled by the seven-bit example in Theorem 15. The analogous question for the token-only-value pure atom class remains open.

The fixed/free frequency distinction is resolved; the unresolved issue is Boolean sign expressivity. Formalizing the literal rotary interpolation bridge would close the remaining Lean coverage gap in the proved architectural inequalities.

## Follow-up: requested pure-RoPE example

The requested strict Boolean example remains unresolved. The follow-up produced a new exclusion theorem and exact certificates for an unsuccessful search, rather than a claimed counterexample.

[Theorem 15](../../theorems/03_rotary_attention/015_pure_rope_two_heads_complement_invariant.md) proves that a function invariant under complementing every input bit has equal pure-RoPE and vanilla complexity whenever its pure complexity is at most two. Thus any two-versus-three example must lack that symmetry. The proof uses a special numerator relation forced by token-only values and cannot be transferred to the retained-position variant without an additional argument.

`Atoms/RoPEReorientation.lean` checks the special pure-head coefficient relation, `RoPEReorientation.exists_positive_direction_of_ne_zero`, `weighted_antipodal_average`, and `quadric_reorientation`. The complete classifier theorem, including the finite strictness-preserving perturbation and the construction of two vanilla heads, is handwritten in Theorem 15. Existing model definitions and earlier theorem statements remain unchanged.

The [search artifacts](search/README.md) contain 830 exact two-head vanilla certificates for sampled two-head pure classifiers on eight, ten, and twelve bits. This includes 100 samples chosen to suppress low-degree Fourier terms. All certificates were verified on the full cube with Python integer arithmetic. They do not establish a general equality theorem. Seven initial numerical failures were resolved by further search; they are not counterexamples.

The seven-bit orientation example in run `e9ce59582a3f` was also inspected. Its vanilla lower bound uses denominator orientation, but the function is complement-invariant. Theorem 15 therefore rules it out as a two-head pure-RoPE separation. The earlier reciprocal exact-score separation and the ten-bit rank obstruction also remain unsuitable for the requested Boolean separation.

Follow-up validation: all 48 tracked Lean modules built and all 965 theorem declarations passed the standard-axiom audit. Static Markdown and KaTeX checks passed for the three math documents, with 330 spans. The exact search verifier checked all 830 records. GitLab rendering remains unavailable because `glab` is not installed.

The follow-up also obtained a strict retained-RoPE comparison, using the existing seven-bit vanilla lower bound from run `e9ce59582a3f`. The corollary to Theorem 15 gives retained complexity two and pure and vanilla complexity three. `search/verify_retained_f7.py` verifies the two-head retained certificate at all 128 inputs and constructs its retained atom parameters exactly as rational numbers. This certificate is not a pure-RoPE certificate. The vanilla lower bound and exact count are the cited run's Lean results, not newly imported declarations in this checkout.

GitHub's real Markdown API recognized all 174 spans in Theorem 14, all 72 in Theorem 15, and all 84 in the theorem ledger, with no render findings. The external proofs are linked at the exact inspected commit hashes.
