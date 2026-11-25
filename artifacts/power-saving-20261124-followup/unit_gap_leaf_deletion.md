# Deleting monochromatic coordinate leaves of a unit basis

## Statement

Let $A=a_0+\sum_i a_ix_i$ and $B=b_0+\sum_i b_ix_i$, with every denominator coefficient strictly positive. Suppose a sign table $f$ satisfies $f(x)A(x)\geq B(x)$ on the entire Boolean cube, and selected actual contact points have $A(x)=g(x)B(x)$ with prescribed signs $g$.

Suppose every selected contact with $x_i=1$ has the same sign $s\in\lbrace-1,+1\rbrace$. For any $0\leq t\leq b_i$, set

$$ A_t=A-stx_i,\qquad B_t=B-tx_i. $$

Then the full-cube unit inequalities and every prescribed contact value are preserved. For $t\lt b_i$, every denominator coefficient remains strictly positive, so the new ratio is an admissible original head. At $t=b_i$, the denominator remains positive as a function because $b_0\gt0$, but the zero slope is a boundary point of this orientation chart. This endpoint is not asserted to be an admissible original head.

## Proof

For every cube vertex,

$$ f(x)A_t(x)-B_t(x)=f(x)A(x)-B(x)+tx_i(1-f(x)s)\geq0. $$

The last factor is either zero or two. At a selected contact, either $x_i=0$, so nothing changes, or $g(x)=s$, so $A_t(x)-g(x)B_t(x)=0$. The denominator coefficient sum decreases by exactly $t$, while its constant coefficient is unchanged. Thus its normalized constant coefficient improves whenever a positive amount is removed.

The same deletion can be performed successively at all monochromatic one-face coordinates. The prescribed signs are unchanged, so deleting one coordinate cannot destroy the premise for another.

## Consequence for recursive basis constructions

A common proposed amplification starts with an affine Boolean basis and appends a new coordinate. All old basis points get zero in that coordinate, and one new basis point gets one. This coordinate has only one selected one-face contact, hence is monochromatic. Its entire denominator coefficient can be removed in the closure of every feasible branch while retaining the basis observations and all full-cube unit inequalities.

Equivalently, if $Z$ is the signed interpolation basis matrix and $T=Z^{-1}\mathrm{diag}(g)Z$, then a monochromatic coordinate satisfies $Te_i=se_i$. Every corresponding full-cube inequality has coefficient $(f(x)s-1)x_i\leq0$ in $b_i$. Removing $b_i$ therefore improves it.

This proves that sequential coordinate extensions of this form cannot amplify a small constant-denominator balance by forcing an additional denominator weight. It does not exclude a construction that substantially changes the old basis or introduces coordinates whose selected one-face contacts carry both signs.

The ten-variable no-coordinate-ray example has both signs among the selected one-face contacts of every coordinate. It is already a core to which this deletion lemma does not apply.

## Formal status and remaining gap

`HeadComplexity/Research/UnitGapLeafDeletion.lean` proves `signed_gap_preserved`, `contacts_preserved`, `remaining_slopes_pos`, `exists_admissible_contracted_atom`, `exists_contracted_unit_head`, and `coefficient_mass_decreases`, in namespace `HeadComplexity.UnitGapLeafDeletion`. The analytic argument above is only finite real algebra; it uses no margin assumption beyond the stated global unit inequalities.

The targeted build passed with 3227 jobs. All eight theorem declarations and the four recorded public `#print axioms` checks use only `propext`, `Classical.choice`, and `Quot.sound`.

No inverse-polynomial lower bound on the best normalized constant coefficient has been proved for cores with both contact signs in every one-face. The existing packing argument remains conditional on such a representative. Even a per-basis bound would need an additional joint-contact argument to avoid paying a separate selection of approximately $n$ Boolean rows per head.
