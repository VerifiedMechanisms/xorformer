# Imported Warren proof and original-model audit

## Provenance

The required starting revision did not contain a proof of `WarrenStrictSignPatternBound`. A permitted read of `VerifiedMechanisms/xorformer-runs` found a complete proof on branch `ar/2c00c9dca8bf`, at tip `f15907a98f4f86fcd8f72ef838d19a2197c133b8`. The general counting theorem was committed there as `0fc32da90a7b2c4e09298f63d934b52ba56e3ab8`; the source branch's final audit is commit `6f5c7d43e32195fe4b05508de9f5f2d3e4888699`.

Thirteen missing modules were copied byte for byte from that branch. No existing module was overwritten. The only public export change is an import of `Results.WarrenBound` in `Results.All`. The original definitions of `Head`, `FracAtom`, `computableWithHeadsN`, `HStar`, and `worstCaseHeadComplexity` are unchanged.

This is imported prior work, independently rebuilt and audited here. It is not a new improvement to the lower-bound exponent.

## Proof chain

The chain starts with polynomial division for diagonal leading terms, then bounds regular roots by perturbation. Algebraically independent values over a countable coefficient field supply generic regular levels. A common closest-point objective has unique minimizers on finitely many closed sign regions. Strict constrained minima are bounded by a polynomial penalty and the regular-root theorem. Counting signed active sets gives the strict Warren bound.

`HeadComplexity.warrenStrictSignPatternBound` proves exactly the existing proposition in `Results.CountingLowerBound`. It has no counting assumption. In particular, `HeadComplexity.worstCaseHeadComplexity_gt_div` now supplies the existing finite division-form bound against the original worst-case head complexity without a Warren argument.

The theorem still assumes the explicit natural-number size condition from its statement. Nothing in this import proves a power saving or a logarithmic factor over the quadratic denominator.

## Fresh verification

`lake build HeadComplexity.Results.WarrenBound` passed with 3426 jobs. The complete transcript is in `warren-build.txt`.

`WarrenAudit.lean` checks the exact interface and the unconditional division-form statement. Its `#print axioms` transcript, `warren-axioms.txt`, lists only `propext`, `Classical.choice`, and `Quot.sound` for the strict sign count, Warren theorem, and worst-case lower bound.

The repository's `AxiomCheck.lean` separately checked all 101 theorem declarations in the 13 imported modules. Its transcript is `warren-all-declarations-audit.txt`. It rejects project axioms and any transitive axiom beyond the same three foundational axioms. The audit passed. A source scan found no `sorry`, `admit`, `axiom`, `unsafe`, or `implemented_by` declaration in the imported modules.

The proof's use of real analysis and algebra is through existing Mathlib theorems. The audit did not assume the source branch's saved build or axiom transcript.
