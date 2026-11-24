# Finite coordinate fibers and the full unit gap

## Exact transfer

Let $X$ and $J$ be finite sets. Suppose the real scores $S_j$ agree on a selected coordinate set $I\subseteq X$, and a fixed score $G$ interpolates their common values there. Write $D_j=S_j-G$ and choose

$$ M=1+\sum_{j\in J}\sum_{x\in X}\frac{2}{|D_j(x)|}, $$

where a summand with zero denominator is defined to be zero. Then

$$ T_j(x)=1+M D_j(x) $$

has $|T_j(x)|\geq1$ on the complete finite domain, equals $1$ on every selected coordinate, and is positive exactly where $D_j(x)\geq0$. Indeed, a nonzero difference satisfies $M|D_j(x)|\geq2$; a zero difference gives $T_j(x)=1$.

If $S_j$ uses $H$ genuine original heads and $G$ uses $K$ genuine original heads, then $T_j$ uses $H+K$ genuine heads. Scale the former heads by $M$, the latter by $-M$, and set the bias to $1+M(b_j-c)$. Scaling changes only numerator readout parameters, so all original admissibility conditions remain true. No coefficient bounds, margin assumptions, or restrictions on signed cancellation are used.

The declarations `gapScale_mul_abs_ge`, `centered_unit_gap`, `common_fiber_unit_contacts`, and `atom_centering_identity` in `HeadComplexity/Research/FiniteFiberUnitGap.lean` check these assertions.

## Exact limitation

This transfer does not turn a general coordinate fiber into a counterexample for a full active linear basis. Suppose a linear feature family contains the constant function and its restriction to $I$ is injective. The unique interpolant taking the value $1$ on every row of $I$ is then the constant function on all of $X$.

This statement is kernel checked as `all_positive_contacts_force_constant`. In particular, if one of the centered scores is nonconstant, the enlarged collection of features cannot have an injective restriction to $I$. When $G$ is another member of the original coordinate fiber, the nonzero difference $S_j-G$ explicitly lies in the kernel of that restriction.

There is a second independent limitation: distinct real-valued fiber points need not give distinct sign patterns of $S_j-G$. Therefore a large algebraic fiber does not by itself provide a large count of full unit-gap truth tables, even before the active-basis issue is considered.

The transfer shows that arbitrary common real observations can be replaced by positive unit observations with additive head overhead. The two precise remaining requirements are many distinct signs after centering, and enough independent unit contacts at the resulting width. Neither is supplied by this lemma. The original worst-case complexity definition is unchanged, and no improvement to its unconditional lower bound is claimed.

## Verification

The accompanying `FiniteFiberGapAudit.lean` prints the transitive axioms of the exported declarations. Build and axiom logs are recorded separately. These are kernel-checked finite statements; there is no numerical experiment in this note.
