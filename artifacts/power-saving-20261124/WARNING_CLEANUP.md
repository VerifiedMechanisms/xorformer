# Lean warning cleanup

## Result

The default library and all thirteen research modules pass `lake --wfail build` with zero warnings. The research modules were explicitly named because the default root module does not import them. The successful transcripts are [the default build](warning-cleanup-full-build.txt) and [the research-module build](warning-cleanup-build.txt).

The aggregate [axiom audit](VerificationAudit.lean) was rerun with `-DwarningAsError=true`. Its twenty declarations use only `propext`, `Classical.choice`, and `Quot.sound`. A scan of all thirteen research sources found no `sorry`, `admit`, or axiom declarations. [The verification manifest](final-verification.json) contains refreshed source and transcript hashes.

## Changes and statement preservation

- Removed unused finite-enumeration and decidable-equality assumptions from the affine zero-divisor and two-head cancellation lemmas. Proofs that need decidable equality now use it locally.
- Replaced `Fintype` with `Finite` for finite query sets when the statement does not depend on an enumeration. Applied the same change to the column index in `product_width_of_antipodal`, constructing its enumeration inside the proof.
- Scoped the remaining enumeration assumptions to the matrix-rank statements that actually use them.
- Replaced the flagged simplification steps, removed an unused simplification argument, and corrected the reported whitespace issues.

No mathematical conclusion was weakened. Removing redundant assumptions generalizes the affected auxiliary statements. No definitions were changed, and no theorem was deleted. Relative to the canonical baseline `f4781ed`, every formalization change is an added research module; no preexisting formalization file was changed or removed. No additional linter suppression was introduced.

## Research status

This maintenance step proves no new head-complexity bound and does not extend the recorded research duration. The original unrestricted exponent improvement remains unproved. The auxiliary declarations, failed approaches, and exact limitations remain documented in [the research outcome](RESEARCH_OUTCOME.md).
