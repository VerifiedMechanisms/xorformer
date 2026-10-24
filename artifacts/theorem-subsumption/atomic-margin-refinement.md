# A Certified Quantitative Improvement to Theorem 195

## Result

Research against `abstraction-reusing-results` at commit `560b69173bbafd79733af4b9fd6cfc2faf3ec1ba`, dated 2026-10-24, yields a stronger version of the currently curated atomic-margin sparsification result. Under exactly the existing certificate hypotheses,

$$ H^{\ast}(f) \leq \left\lceil 2(n+1)\left(\frac{\Lambda}{\gamma}\right)^2 \right\rceil, \qquad H^{\ast}(f) \leq 3(n+1)\left(\frac{\Lambda}{\gamma}\right)^2. $$

For every nonconstant function, the existing literal condition number also satisfies

$$ H^{\ast}(f) \leq 3(n+1)\kappa_{\mathrm{atom}}(f)^2. $$

The old proved constants are 32 for the rounded sample count and 33 for the real-valued bounds. The sample coefficient improves by a factor of 16; the real-valued coefficient improves by a factor of 11. This strengthens the explicit Lean bounds. The asymptotic claim in the original Markdown theorem already permits an unspecified absolute constant.

The target is [theorem 195](../../theorems/02_complexity_measure_upper_bounds/195_atomic_margin_sparsification.md), exported in [`Results/All.lean`](../../formalization/HeadComplexity/Results/All.lean) as `theorem195_atomic_margin_sample_bound`, `theorem195_atomic_margin_sparsification`, and `theorem195_atomic_condition_number`. On this branch, `Results/All.lean` is the curated entry point referred to in the request.

## Research Finding

Inspection of [`AtomicSampling.lean`](../../formalization/HeadComplexity/Atoms/AtomicSampling.lean), [`AtomicMarginSparsification.lean`](../../formalization/HeadComplexity/Results/AtomicMarginSparsification.lean), and [`AtomicCondition.lean`](../../formalization/HeadComplexity/Results/AtomicCondition.lean) revealed two independent quantitative losses.

First, the old proof places a centered random variable in the symmetric interval from negative two to two. The actual interval has width two, regardless of its center. Mathlib's already imported Hoeffding lemma uses interval width, so its sub-Gaussian parameter can be reduced from four to one.

Second, the empirical approximation theorem gives a *strict* loss inequality. The old compiler spends only half of the available margin. Spending the full margin still leaves a strictly positive score, reducing the required sample coefficient by another factor of four.

The improvement uses the existing finite sampling and atom-scaling constructions. It needs no new axiom, external archive, stronger atom class, or additional regularity assumption.

## Statement and Proof

Let a genuine `AtomicMarginCertificate` provide finitely many fractional atoms, a probability distribution on them, normalized outputs, and a signed margin:

$$ |a_j(x)|\leq 1, \qquad y_x\in\lbrace-1,1\rbrace, \qquad u_x=\mathbb E_j a_j(x), \qquad y_x(c+\Lambda u_x)\geq\gamma\gt0, \qquad \Lambda\gt0. $$

### Claim 1. Sharper empirical loss

For each fixed input, the centered loss has mean zero and belongs to

$$ Z_x(j)=y_x(u_x-a_j(x)) \in [y_xu_x-1,y_xu_x+1]. $$

This interval has width two. Hoeffding's lemma therefore gives sub-Gaussian parameter one. Independence and the existing finite union argument show that a sample simultaneously satisfies

$$ \sum_{i=1}^{m} y_x(u_x-a_{j_i}(x)) \lt m\varepsilon \qquad\text{for every }x $$

whenever

$$ 2^n\exp\left(-\frac{m\varepsilon^2}{2}\right)\lt1. $$

The new declaration is `exists_empirical_oneSided_approximation_sharp`. The original declaration with denominator eight remains available as a corollary, preserving its signature.

### Claim 2. Full-margin compilation

Choose the full error budget and the refined sample count:

$$ \varepsilon=\frac{\gamma}{\Lambda}, \qquad m=\left\lceil2(n+1)\left(\frac{\Lambda}{\gamma}\right)^2\right\rceil. $$

The union-bound budget is at most the exponential of negative one, since

$$ \frac{m\varepsilon^2}{2}\geq n+1, \qquad 2^n\leq e^n, \qquad 2^n e^{-m\varepsilon^2/2}\leq e^{-1}\lt1. $$

For the resulting empirical score, the loss is strictly smaller than the original margin:

$$ y_x\left(c+\frac{\Lambda}{m}\sum_{i=1}^{m}a_{j_i}(x)\right) = y_x(c+\Lambda u_x)-\frac{\Lambda}{m}\sum_{i=1}^{m}y_x(u_x-a_{j_i}(x)) \gt \gamma-\Lambda\varepsilon=0. $$

The existing `FracAtom.scale` operation absorbs the common sample weight into valid heads. This proves the natural-valued bound.

### Claim 3. Real-valued and infimum bounds

For a nonconstant function, the existing normalization argument gives

$$ \frac{\Lambda}{\gamma}\geq1, \qquad A=(n+1)\left(\frac{\Lambda}{\gamma}\right)^2\geq1. $$

Consequently,

$$ H^{\ast}(f)\leq\lceil2A\rceil\lt2A+1\leq3A. $$

Constant functions have zero head complexity, so the real-valued certificate bound requires no nonconstancy assumption. For the literal infimum, the square root of the head count divided by the positive coefficient is a lower bound for every realized condition ratio. It is therefore a lower bound for their infimum. Squaring proves the stated condition-number bound without assuming attainment. $\blacksquare$

These proofs are in [`AtomicMarginRefinement.lean`](../../formalization/HeadComplexity/Results/AtomicMarginRefinement.lean). The curated entry point additionally exports `theorem195_atomic_margin_sample_bound_refined`, `theorem195_atomic_margin_sparsification_refined`, and `theorem195_atomic_condition_number_refined`.

## Formal Comparison

[`AtomicMarginSubsumption.lean`](../../formalization/HeadComplexity/AtomicMarginSubsumption.lean) applies the pinned `theorem-subsumption` v0.2.0 criterion from the topmost commit. The shared inputs are dimension, head count, and condition ratio. Both contracts require the same `AtomicMarginSamplingContract`, whose fields express positive ratio, the constant/nonconstant normalization alternative, and the empirical sampling rule. No real-valued head bound is assumed as a field.

`AtomicMarginCertificate.samplingContract` proves the semantic bridge from every genuine certificate to this numeric interface. The refined bound is obtained from that interface. `legacy_guarantee_at_certificate` independently identifies the old numeric guarantee with the original theorem's conclusion by applying the original declaration. Thus the numerical promises have checked connections to the actual H* development.

| Obligation | Certified status | Generated certificate |
| --- | --- | --- |
| Old requirements imply new requirements | `PROVED` | `subsumptionCertificate_1` |
| New requirements imply old requirements | `PROVED` | `subsumptionCertificate_2` |
| New guarantee implies old guarantee without requirements | `PROVED` | `subsumptionCertificate_3` |
| Old guarantee implies new guarantee without requirements | `REFUTED` | `subsumptionCertificate_4` |

All four certificate names are in namespace `HeadComplexity.AtomicMarginSubsumption`. Elaboration asserts these statuses and the classification **source strictly subsumes target under this alignment**.

The reverse implication is refuted at dimension one, head count seven, and ratio one: the old numeric cap is 66 and the new cap is six. This is a counterexample to the *context-free numeric implication*. It does not describe a Boolean function satisfying the sampling requirements, and it does not claim logical independence of two already proved H* theorems.

There is also a checked improvement on genuine certificate data. `certificate_endpoints_strictly_improve` proves that the real-valued endpoint is strictly smaller for every valid certificate. `certificate_sample_counts_strictly_improve` proves that even the rounded natural endpoint is strictly smaller for every valid certificate of a nonconstant function. These statements compare upper certificates, rather than claiming that the actual minimum head count changes.

The result establishes one quantitative improvement to a curated result. It makes no optimality claim for the constant three and no corpus-wide frontier claim. The original theorem declarations and the 38-note selection manifest remain available and unchanged.

## Verification

The focused build passed with the branch's pinned Lean 4.31.0 and Mathlib v4.31.0. The focused all-declaration audit passed for 233 theorems across the six modules below, including all four generated comparison certificates. Reproduce it from `formalization/`:

```sh
lake build HeadComplexity.AtomicMarginSubsumption HeadComplexity.Results.All
lake env lean --run ../artifacts/scripts/AxiomCheck.lean \
  HeadComplexity.Atoms.AtomicSampling \
  HeadComplexity.Results.AtomicMarginSparsification \
  HeadComplexity.Results.AtomicCondition \
  HeadComplexity.Results.AtomicMarginRefinement \
  HeadComplexity.AtomicMarginSubsumption \
  HeadComplexity.Results.All
```

The full repository validator, `bash artifacts/scripts/validate.sh`, also passed its build, placeholder scan, and axiom audit of 3,130 theorem declarations across 125 tracked modules. The separate focused audit explicitly covers the two newly created Lean modules, which the tracked-file enumeration does not yet include.

The comparison module contains regression assertions for all four settled obligations. The axiom audits check generated and private declarations as well as the public results, permitting only `propext`, `Classical.choice`, and `Quot.sound`. No exhaustive four-bit archive check is required for this result.

Static Markdown lint and KaTeX validation passed for this report and the edited formalization README, with 13 math spans checked. This newly created report was included explicitly because the tracked-file CI scan does not cover it until it is added to Git.

The faithful GitHub render audit was skipped after automatic approval review rejected sending the local research report to GitHub's external Markdown API. The faithful GitLab render audit was skipped because `glab` is unavailable. No remote-render verification is claimed.
