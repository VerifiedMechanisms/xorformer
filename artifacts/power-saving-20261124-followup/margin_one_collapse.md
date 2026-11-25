# Exact margin one collapses to one head

## Kernel-checked statement

Let a nonconstant truth table have an original representation of any finite width with relative margin at least one. Then it already has a genuine width-one representation of relative margin one.

The exact declaration is `HeadComplexity.MarginOneCollapse.hasRelativeMargin_one_head` in [MarginOneCollapse.lean](../../formalization/HeadComplexity/Research/MarginOneCollapse.lean). Its hypotheses state both the existence of a false input and the existence of a true input. It uses the requested full-cube amplitude, arbitrary original real coefficients, target-dependent denominators, and arbitrary signed cancellation. No head class or admissibility condition is changed.

The stronger pointwise declarations are `alignment_of_margin_one`, `bias_eq_zero_of_margin_one`, and `eval_eq_norm_mul_signedLabel`. For every original head in such a certificate, they prove

$$ b=0,\qquad \phi _h(x)=\|\phi _h\| _\infty f _{\pm}(x) $$

on every Boolean input, where $f _{\pm}$ takes values in $\lbrace-1,+1\rbrace$.

## Proof

Write $D=|b|+\sum _h\|\phi _h\| _\infty$. Strict representation implies $D\gt0$. Margin at least one gives $f _{\pm}(x)S(x)\geq D$ for every input. Every individual summand has the opposite upper bound

$$ f _{\pm}(x)b\leq|b|,\qquad f _{\pm}(x)\phi _h(x)\leq\|\phi _h\| _\infty. $$

Consequently all these inequalities are equalities: their nonnegative defects have sum at most zero. At a false input the bias equality gives $-b=|b|$, while at a true input it gives $b=|b|$, so $b=0$.

The remaining pointwise equalities give $f _{\pm}(x)\phi _h(x)=\|\phi _h\| _\infty$ for every head. Since the amplitude is positive, some head has positive norm. That genuine head, with zero bias, already has signed score equal to its full-cube norm at every input. Its relative margin is exactly one. No rescaling or replacement denominator is necessary. $\blacksquare$

## Consequence for the stationarity route

A proposed globally accessible stationarity argument forcing unit-gap amplitude one would force this one-head endpoint. It cannot be treated as a generic healthy-margin endpoint for arbitrary truth tables. Such an argument must account for exceptional denominator configurations, boundary attainment, or a failure of its access hypotheses.

This is an exact equality statement. It does not give a width reduction for margins merely close to one, and it does not obstruct a comparison repair at either tiny target margin in the benchmark.

The independently audited written refinement [margin_one_nonattainment.md](margin_one_nonattainment.md) uses the original shared attention parameter to show that no genuine head on at least two bits is nonconstant and exactly two-valued. Combined with the kernel collapse, this excludes attaining margin one for every nonconstant table at every finite width. `LiteralMarginNonattainmentWitness.literal_margin` separately kernel-checks genuine one-head literal margins approaching one. The complete nonattainment classification remains a written theorem; it is not implied by this module alone.

A reusable scalar step of the broader classification is now kernel-checked as `TwoValuedFaceGeometry.four_corner_labels_constant` in [TwoValuedFaceGeometry.lean](../../formalization/HeadComplexity/Research/TwoValuedFaceGeometry.lean). On a two-dimensional face, let the affine denominator be positive at all four vertices. Assume its two slopes vanish simultaneously, and if they vanish then the two numerator slopes vanish simultaneously. If the affine ratio takes only the values minus one and one, all four labels are equal. The proof checks all sixteen label patterns by linear arithmetic. The original shared parameters imply these slope conditions after normalization, but the general face restriction and cube connectivity wrapper remain written. This scalar module builds with 3137 jobs and has only the three standard axioms, recorded in `two-valued-face-geometry-axioms.txt`.

## Verification

The module builds successfully with 3283 jobs. All four declarations have only `propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom reports. The audit is [AuditMarginOneCollapse.lean](../../formalization/AuditMarginOneCollapse.lean); the recorded outputs are `margin-one-collapse-build.txt` and `margin-one-collapse-axioms.txt`.

The finite-margin agent independently audited the complete proof, including the per-head equality quantifier, both-label bias argument, existence of a positive-norm head, and the actual original-model margin conclusion.
