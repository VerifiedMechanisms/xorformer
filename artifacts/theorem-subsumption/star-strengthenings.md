# Certified Strengthenings of the Core Results

## Baseline and Scope

The preservation baseline is `50b66da5bbcfe1d7dd98c5e403874cc5089d7e98`, before the star-cover series and after the certified theorem-195 atomic-margin improvements. These results target core theorem 6, core theorem 9, and the existing degree-sensitive support bound. Reproducing the atomic-margin constants does not count as progress here.

The attention-only model, `FracAtom`, `computableWithHeadsN`, `thresholdDeg`, and `HStar` are unchanged. Every original Lean source is preserved byte for byte except `Results/All.lean`, which only gains imports and aliases. The reproduction script checks this against the preservation baseline.

## Proved advances

The [mathematical writeup](../../theorems/02_complexity_measure_upper_bounds/198_monomial_star_universal_head_bound.md) gives the complete statements and proofs.

| Older result | New guarantee | Main declaration |
| --- | --- | --- |
| Core theorem 9: universal budget $2^n-1$ | For $n\gt0$, $H^{\ast}(f)\leq11\cdot2^n/n$; the certified joint integer theorem retains the original, half-cube, logarithmic, and constant-12 endpoints. | `HStar_real_le_eleven_mul_two_pow_div`, `HStar_le_universalElevenStarBound` |
| Core theorem 6: $\deg_{\pm}(f)\leq H^{\ast}(f)$ | The unconditional Lean sandwich using `starDegreeBound`; for $n\gt0$ its upper budget is $G(n,d)$, where $d=\deg_{\pm}(f)$. | `thresholdDeg_le_HStar_le_starDegreeBound` |
| Existing degree-sensitive support budget $1+\sum_{r=2}^{D}\binom nr$ | The additional budget $G(n,D)=\sum_{r=0}^{D-1}\binom{n-1}{r}$ for $n\gt0$; the joint theorem keeps the old budget in all boundary cases. | `HStar_le_min_starDegree_affineFree_of_ThresholdDegLE` |

The quadratic budget becomes $n$ and the cubic budget becomes $1+\binom n2$. These are consequences of the same degree-sensitive compiler, not separate independent advances.

Intermediate universal results are the half-cube budget $2^{n-1}$ and the real logarithmic budget

$$ L(n)=\frac{2\cdot2^n(\log(n/2)+1)}{n}, \qquad n\geq2. $$

The final theorem keeps both by taking minima. The worst-case bound and $W(n)/2^n\to0$ are checked corollaries. Supporting approximation, finite averaging, cover-transport, and recursion lemmas are not counted as independent advances.

## Model connection

`exists_fracAtom_approx_monomial_mul_affineValue` constructs genuine atoms using the pre-existing negative-affine-ratio realization. `SquarefreePolynomial.computableWithHeadsN_of_starCover` groups coefficients, uses the existing strict-margin replacement theorem, and returns `computableWithHeadsN` for the actual attention model.

The polynomial compiler starts with `SquarefreePolynomial.exists_squarefree_strictSignRep_of_ThresholdDegLE`. Thus weak threshold certificates are strictly separated without changing their degree. The universal cover argument applies to all truth tables through the already proved `thresholdDeg_spec`.

`monomialStarCoverNumber_block_recurrence` proves the semidirect construction and its size bound. `monomialStarCoverNumber_real_le_eleven` closes strong induction using finite Bernoulli weights and an explicit exponential-series bound. No covering theorem or analytic estimate is introduced as an axiom.

The semidirect construction is adapted from [Cooper, Ellis, and Kahng, Section 2.1](https://arxiv.org/abs/math/0309081). Its adaptation, constants, and application to attention are all proved in the local Lean sources.

## Strict subsumption certificates

All comparisons use `TheoremSubsumption.compareTheorems` from the pinned package at `112d2d977cb3c1daa452a9ed6db6561fd025f128`. Every comparison asserts the following four outcomes and fails elaboration if any changes:

- Requirements in both directions: `PROVED`.
- Context-free source guarantee implies target guarantee: `PROVED`.
- Reverse guarantee implication: `REFUTED` by an explicit proof.
- Classification: `source strictly subsumes target under this alignment`.

The checks run in logical mode. Contextual and adapter search statuses are not used as evidence.

| Source contract | Existing or intermediate target | Exact reverse witness | Module |
| --- | --- | --- | --- |
| `star_universal_contract` | Original core theorem 9 contract | $n=3$, head variable $5$ | [StarUpperBoundSubsumption.lean](../../formalization/HeadComplexity/StarUpperBoundSubsumption.lean) |
| `star_degree_contract` | Existing support-count degree contract | $n=4$, degree $2$, head variable $7$ | Same module |
| `star_threshold_degree_contract` | Original core theorem 6 contract | $n=8$, degree $2$, head variable $9$ | Same module |
| `logarithmic_contract` | Original core theorem 9 contract | $n=13$, head variable $4097$ | [UniversalSublinearSubsumption.lean](../../formalization/HeadComplexity/UniversalSublinearSubsumption.lean) |
| `logarithmic_contract` | Half-cube contract | $n=32$, head variable $2^{31}$ | Same module |
| `sublinear_sequence_contract` | Exact original normalized worst-case endpoints | Sequence zero at dimension zero and $1/2$ thereafter | Same module |
| `linear_contract` | Original core theorem 9 contract | $n=13$, head variable $4097$ | [UniversalLinearSavingSubsumption.lean](../../formalization/HeadComplexity/UniversalLinearSavingSubsumption.lean) |
| `linear_contract` | Full rounded logarithmic contract, including all its minima | $n=256$, head variable $23\cdot2^{247}$ | Same module |

### Checked alignments and strictness

`HeadCountRealized n heads` is exactly the existence of an actual Boolean function with `heads = HStar n f`. The degree contracts additionally retain either a genuine `ThresholdDegLE` certificate or the equality `degree = thresholdDeg f`. Both sides of each comparison have the same realization premise. The baseline contracts invoke the original result declarations directly; the source contracts invoke the new actual-model theorems. For core theorem 6, `thresholdDeg_bound_iff_model_degree_bound` proves that the minimum-form lower bound is equivalent to the full original statement for every computed head count. The baseline contract also invokes the original `degree_le_of_computableWithHeadsN` declaration directly.

The sequence comparison aligns its shared sequence with the actual normalized worst-case invariant. `baseline_ratio_at_worstCase` bridges the original `worstCaseHeadComplexity_le` theorem. `sequence_baseline_guarantee_iff` checks that the harmless conjunction used to keep the pointwise universal quantifier inside the tool's guarantee is equivalent to the exact baseline statement.

The reverse witnesses are abstract values admitted by the old numerical guarantees. They are not claimed to be counterexamples to the stronger actual-model theorems. Separate Lean endpoint proofs establish genuine improvements of applicable budgets:

- `two_pow_pred_lt_original_universal` is strict in every dimension at least two.
- `quadratic_eight_bit_endpoints_strict` gives eight versus 29 for the full applicable eight-bit quadratic class.
- `universalStarBound_lt_half` is strict in every dimension at least 32.
- `eleven_budget_lt_logarithmic` is strict in every dimension at least 256.
- `logarithmic_reverse_refuted` checks the complete rounded natural budgets at dimension 256 using exact arithmetic, including all earlier minima.

## Reproduction

From the repository root:

```sh
bash artifacts/scripts/validate_star_strengthenings.sh
bash artifacts/scripts/validate.sh
```

The focused script builds all new modules and the result umbrella, rejects proof placeholders, audits every owned theorem including generated comparison certificates, checks preservation of the pre-existing Lean sources, and reruns all eight comparisons. The full validator builds and audits every tracked library module.

For full tool reports, run these commands from `formalization`:

```sh
lake env lean HeadComplexity/StarUpperBoundSubsumption.lean
lake env lean HeadComplexity/UniversalSublinearSubsumption.lean
lake env lean HeadComplexity/UniversalLinearSavingSubsumption.lean
```

The axiom allowlist is exactly `propext`, `Classical.choice`, and `Quot.sound`. There are no project axioms, proof placeholders, or native-decision axioms in the new proofs.

Math Markdown is checked with the repository static checker and local KaTeX.

## Validation record

The focused script passed: eight strict comparisons, 391 owned theorem declarations across 12 modules, and preservation of all 135 baseline Lean source files. The full validator passed for 146 modules and 3,637 theorem declarations, including private helpers and generated comparison certificates. All theorem dependencies stay within the three standard allowed axioms.

The complete static and KaTeX audit passed for 220 tracked Markdown files and 12,896 math spans. The compact [validation record](star-strengthenings-checks.txt) lists the commands and results.

## Attempts and open work

Grouping only the affine terms retained a large nonlinear support bill. Whole monomial stars fixed that, and one-stage random repair gave the logarithmic bound, but did not remove its logarithm. Discounting repairs through a smaller block closed the stronger recursion. The initial constant 12 was sharpened to 11; its named compatibility results remain available.

Exploratory small-cover searches were not used in the proofs and are not counted as certified results. A universal fixed-denominator span at the dimension-count threshold was not established. Optimal constants, exact worst-case head complexity, and a matching unconditional lower bound remain open here. The existing Warren-dependent counting lower bound keeps its original premise.
