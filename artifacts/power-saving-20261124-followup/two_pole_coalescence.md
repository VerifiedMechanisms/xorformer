# Exact two-pole coalescence and the first obstruction to iteration

## Status

The two-pole identity, its complete truth-table preservation, and the existence of admissible original heads for all sufficiently small positive parameters are kernel checked in `formalization/HeadComplexity/Research/TwoPoleCoalescence.lean`. The principal declaration is `HeadComplexity.TwoPoleCoalescence.eventually_admissible_coalescence`.

The extension from an arbitrary original two-head representation to the positive-base convention is explained below as a written proof. The polynomial-ideal obstruction to a particular three-head iteration is also a written proof. Neither statement gives a new asymptotic lower bound.

The inherited weighted osculating count, its full-rank and weak-sign caveats, and the shape-coordinate degree obstruction were audited before this construction. They are in `artifacts/power-saving-20261124/curvilinear_osculating_capacity.md`, `weighted_degree_sign_capacity.md`, and `staircase_charts_and_shape_degree.md`. The present result supplies an exact low-width access lemma; it does not reprove those counting results.

## Exact path

Let $A_1,A_2,B_1,B_2$ be real affine forms on the Boolean cube, with both denominators strictly positive everywhere. For $t\neq0$, put

$$ D_t=B_2+t(B_1-B_2),\qquad M_{1,t}=A_2/t,\qquad M_{2,t}=A_1+(1-1/t)A_2. $$

Where the denominators are nonzero, direct expansion gives

$$ \frac{M_{1,t}}{B_2}+\frac{M_{2,t}}{D_t}=\frac{A_1B_2+A_2B_1}{B_2D_t}=\frac{B_1}{D_t}\left(\frac{A_1}{B_1}+\frac{A_2}{B_2}\right). $$

Thus every input has exactly its original score sign whenever $D_t$ is positive. This includes zeros, although lower-bound applications can first use the existing strictification theorem. The numerators may grow like $1/t$; no bounded-coefficient assumption is imposed.

The reciprocal germ $B(s)=B_2+s(B_1-B_2)$ has first coefficients $f_0=1/B_2$ and $f_1=-(B_1-B_2)/B_2^2$. Consequently the endpoint score is a strict length-two osculating score whenever the original score is strict:

$$ (A_1+A_2)f_0-A_2f_1=\frac{A_1B_2+A_2B_1}{B_2^2}. $$

This is an exact score identity after a positive multiplier, rather than merely a weak limiting sign representation. It is checked by `coalesced_score_identity` and `coalesced_sign`.

## Original admissibility

The formal path theorem assumes that the constant and every variable coefficient of $B_2$ are strictly positive. It assumes only full-cube positivity of $B_1$. For all sufficiently small $t$, the coefficients of $D_t$ are strictly positive by continuity. Each numerator is affine with arbitrary real coefficients, so `FracAtom.ofPositiveAffineRatio` constructs both heads. `atoms_denom_zero` and `atoms_denom_one` check that their denominators are exactly the prescribed forms. The norms, coefficients, and cancellations are unrestricted.

For an arbitrary original two-head score, absorb the output bias into one affine numerator. If at least one denominator is nonconstant, choose it as $B_2$. Original nonconstant denominators have all slopes strictly positive or all slopes strictly negative. In the negative case, complement every Boolean input coordinate in the complete score, construct the path, and complement back using `FracAtom.flip`. The other denominator need not have the same orientation. If both denominators are constant, the whole score is affine and the existing one-head affine construction applies. The restriction on arbitrary numerators at a constant original denominator is therefore not silently bypassed.

When the two original denominator orientations differ, the constructed family is guaranteed admissible only near zero. It is not claimed to give an admissible path from the original parameter point at $t=1$ through every intermediate parameter.

This construction changes the denominator directions and numerator coefficients together. The inherited fixed-direction radial contraction counterexample therefore does not exclude it.

## Why the elementary merger does not iterate

Suppose there is a third term $A_3/B_3$. Multiplying the whole score by $B_1/D_t$ preserves its signs, but turns that term into

$$ \frac{A_3B_1}{B_3D_t}. $$

A naive iteration would express this as $C_1/B_3+C_2/D_t$ with affine $C_1,C_2$. Such an identity of rational functions requires

$$ C_1D_t+C_2B_3=A_3B_1. $$

The left side belongs to the polynomial ideal $(B_3,D_t)$. For generic affine forms in at least two continuous variables, the right side does not. For example, take affine coordinates $u,v$, let $B_3=u$, $D_t=v$, and choose $A_3=B_1=1$. Evaluation at $u=v=0$ contradicts the required identity. If full-cube positivity is desired, replace $u,v$ by $1+x_1,1+x_2$; the ideal argument evaluates the polynomial identity at $x_1=x_2=-1$, not at a cube input. One may choose nearby strictly positive coherent denominator slopes and preserve the same ideal obstruction.

This excludes that specific exact rational-function decomposition, even with arbitrary affine numerators. It does not exclude an identity only on the Boolean cube, an alternative positive multiplier, a different path, or a compiler allowed additional heads. In particular it does not establish that all representations of a truth table fail to coalesce.

The first missing high-width lemma remains a sign-preserving access theorem with total osculating length or free-product width small enough for the finite count. General semialgebraic curve selection without a suitable bound on the relevant jets does not supply that theorem.

## Verification

`lake build HeadComplexity.Research.TwoPoleCoalescence` passes. The companion `TwoPoleCoalescenceAudit.lean` prints the transitive axioms of the principal path, identity, and endpoint-sign declarations. The all-declaration audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Build and audit output are saved alongside this note.
