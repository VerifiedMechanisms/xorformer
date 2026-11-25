# Near-unit margin forces one-head computability

## Statement

Let $N=2^n$. A nonconstant truth table represented by original admissible heads with relative margin at least $\gamma$ is already computable by one of those heads, with zero bias, whenever

$$ N(1-\gamma)\lt1. $$

This statement is kernel checked as `HeadComplexity.NearUnitMarginCollapse.exists_strict_head_of_near_unit_margin`. Its wrapper `computable_one_head_of_near_unit_margin` concludes the original `computableWithHeadsN n 1 f`. The selected head need not retain the source relative margin.

## Proof

Write $D=|b|+\sum_h\|\phi_h\| _\infty$ and $s(x)\in\lbrace-1,+1\rbrace$ for the labels. Every head deficit $\|\phi_h\| _\infty-s(x)\phi_h(x)$ is nonnegative. If a head fails to classify at least one point strictly, the sum of its deficits over the cube is at least its norm. Since both labels occur, the bias deficit has sum at least $|b|$. Thus, if no head alone classifies the table,

$$ D\leq\sum_x(D-s(x)S(x))\leq N(1-\gamma)D\lt D. $$

Strict representation implies $D\gt0$, giving the contradiction. The Lean proof includes the bias term, the full-cube cardinality, and the conversion back to the original computability definition.

## Scope and verification

This quantitative endpoint statement uses arbitrary real coefficients, signed cancellation, and target-dependent denominators. It is not a quantitative repair and gives no gain at the tiny margins required for the counting argument. Its role is to constrain a proposed near-unit optimum without assuming that any optimum is attained.

The source is [NearUnitMarginCollapse.lean](../../formalization/HeadComplexity/Research/NearUnitMarginCollapse.lean). The dedicated build and three exact axiom prints are in `near-unit-margin-collapse-build.txt` and `near-unit-margin-collapse-axioms.txt`. All three declarations use only `propext`, `Classical.choice`, and `Quot.sound`. An independent agent audited the deficit proof and the original-model wrapper.
