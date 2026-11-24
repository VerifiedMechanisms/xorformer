# Provenance of the prior universal logarithmic upper bound

## Exact source

The prior remote branch `origin/ar/0f08fe6fb98a`, read at commit `7065e81f2c6bb6733a077b9e6b671d079c707b03`, contains `formalization/HeadComplexity/Results/UniversalLogSaving.lean`. Its public declarations are:

- `HeadComplexity.worstCaseHeadComplexity_isBigO_two_pow_div_mul_log`.
- `HeadComplexity.worstCaseHeadComplexity_real_le_log_saving`.
- `HeadComplexity.worstCaseHeadComplexity_exists_log_saving`.

The explicit statement is

$$ \forall n\geq32,\qquad W(n)\leq2323202\frac{2^n}{n\log n}. $$

Here $\log$ is the natural logarithm, and $W$ is the original `worstCaseHeadComplexity`. The theorem has no compiler premise remaining in its public statement. It obtains its compiler from `hasStrictReverseGridCompiler_affinePlane`, followed by the original atom-to-head construction and the global gluing argument.

The same branch contains the saved kernel-axiom transcript `artifacts/head-compression/audit_universal_log_saving.txt`. It reports only `propext`, `Classical.choice`, and `Quot.sound` for these declarations. The construction and independent semantic audit are recorded in `continuation-affine-plane-decoder.tex` and `continuation-log-saving-cold-audit.tex` in that directory.

## Verification in this run

This run read the theorem source, saved axiom transcript, affine-plane written proof, and cold audit selectively with `git show`. It did not inherit or rebuild the large prior verification tree. Consequently this is a provenance record for a prior theorem with a saved kernel transcript, not a newly proved result or a fresh kernel build in this run.

The universal upper bound must be kept separate from the critical-width capacity lower bound of order $nH\log n$. The former constructs a representation for every Boolean target. The latter counts many realizable tables and is not a worst-case upper bound by itself. Neither proves the requested unrestricted lower bound with a fixed power saving over $2^n/n^2$.

## Consequence for a proposed osculating compiler

The new `curvilinear_osculating_capacity.md` gives an absolute constant $c\gt0$ such that, for every sufficiently large $n$, some Boolean target requires osculating length at least $c2^n/n$. Taking the prior universal upper theorem as established, there cannot be an absolute constant $C$ that converts every original representation with $H$ heads into a strict osculating representation of the same target with length at most $CH$.

Indeed, applying such a compiler to the prior universal representations would make every target have osculating length at most $2323202C2^n/(n\log n)$, which is smaller than $c2^n/n$ for sufficiently large $n$. This contradicts the osculating capacity lower bound. The same argument rules out a uniform overhead $o(\log n)$, with the usual additive integer-rounding terms absorbed for large $n$.

This obstruction concerns that specific exact strict-sign compiler. An overhead of order $\log n$ or larger, a different target class, or a joint compiler into another family is not excluded by this comparison. In particular, it does not rule out a sublinear power overhead that could still yield the lower-bound exponent requested in this run.
