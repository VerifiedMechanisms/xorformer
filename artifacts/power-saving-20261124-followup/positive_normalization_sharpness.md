# The factor three in positive normalization is sharp

## Universal upper bound

Let a nonconstant Boolean table have a strict representation

$$ S(x)=-1+\sum_{h=1}^H\phi_h(x),\qquad \phi_h(x)\geq0 $$

by genuine original heads. At every width, its requested relative margin is at most $1/3$. This statement does not assume minimum-zero heads or an upper amplitude bound.

The exact declaration is `HeadComplexity.PositiveNormalizationSharpness.relativeMargin_le_third` in `formalization/HeadComplexity/Research/PositiveNormalizationSharpness.lean`.

**Proof.** Write $A=1+\sum_h\|\phi_h\|_\infty$ and let $\gamma$ be the relative margin. A negative input gives $\gamma A\leq1$, because the head sum is nonnegative. A positive input gives $\gamma A\leq A-2$, because the head sum is at most $A-1$. Therefore

$$ \gamma\leq\frac{\min(1,A-2)}{A}\leq\frac13. $$

The last inequality uses $A\geq3$ for its first branch and $A\leq3$ for its second. Strict representation ensures $A\gt0$. $\blacksquare$

## Exact original witnesses

On one bit, the literal $f(x)=x_1$ has the genuine one-head score $2x_1-1$ with bias zero and relative margin exactly one. One explicit original parameter choice is $\eta=-2$, $\delta=4$, $\gamma=1$, $\alpha=1$, $\rho_1=1$, and $m_1=0$. Its denominator is the positive constant two.

Translating that head by one gives the nonnegative minimum-zero head $2x_1$. With bias $-1$, it has amplitude three, signed minimum score one, and relative margin exactly $1/3$.

These witnesses are kernel checked as `literal_source_margin` and `literal_normalized_margin`. The declaration `hasNormalizedMargin_literal_iff` proves that the canonical width-one class represents the literal at margin at least $\gamma$ exactly when $\gamma\leq1/3$.

Consequently the factor three in `SameWidthPositiveNormalization.hasNormalizedMargin_or_complement` cannot be improved uniformly. Output complementation does not evade the universal upper bound, since the complemented literal remains nonconstant.

## Scope and verification

This sharp constant concerns the positive-head, bias-minus-one normal form. It supplies no obstruction to the benchmark's tiny relative margins or to its desired unrestricted width lower bound. Arbitrary original representations may have larger margins, as the literal witness demonstrates.

The module builds successfully in 3290 jobs. All five declarations have only `propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom reports. An independent semantic review checked both the universal inequality and the original-parameter witnesses.
