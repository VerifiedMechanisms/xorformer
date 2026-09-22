# Affine-Cylinder Threshold-Degree Sandwich

## Statement

For every Boolean function $f$,

$$ \deg_{\pm}(f) \leq H^{\ast}(f) \leq \mathrm{actc}(f) \leq \min\lbrace\mathrm{ctc}(f),\mathrm{afs}_{\pm}(f)\rbrace. $$

Consequently,

$$ \deg_{\pm}(f) \leq \mathrm{actc}(f) \leq \mathrm{ctc}(f), $$

and

$$ \deg_{\pm}(f) \leq \mathrm{afs}_{\pm}(f) \leq \mathrm{ptfsp}(f). $$

> **Interpretation.** The affine-cylinder invariant is now bracketed from both sides. It is an optimized upper-bound target, but it cannot be smaller than threshold degree.

## Proof

The threshold-degree lower bound [006_threshold_degree_head_complexity_bound.md](../01_foundations_and_normal_form/006_threshold_degree_head_complexity_bound.md) gives

$$ \deg_{\pm}(f)\leq H^{\ast}(f). $$

The affine-cylinder threshold-cost lemma [103_affine_cylinder_threshold_cost.md](103_affine_cylinder_threshold_cost.md) gives

$$ H^{\ast}(f)\leq\mathrm{actc}(f) $$

and

$$ \mathrm{actc}(f)\leq\mathrm{ctc}(f). $$

The affine-cylinder hierarchy lemma [104_affine_cylinder_cost_hierarchy.md](104_affine_cylinder_cost_hierarchy.md) gives

$$ \mathrm{actc}(f)\leq\mathrm{afs}_{\pm}(f) \leq \mathrm{ptfsp}(f). $$

Combining these inequalities proves

$$ \deg_{\pm}(f) \leq H^{\ast}(f) \leq \mathrm{actc}(f) \leq \min\lbrace\mathrm{ctc}(f),\mathrm{afs}_{\pm}(f)\rbrace. $$

The two displayed consequences follow by deleting intermediate terms from the same chain. $\blacksquare$

## Consequences

For parity,

$$ \mathrm{actc}(\mathrm{XOR}_n)\geq n, $$

because $\deg_{\pm}(\mathrm{XOR}_n)=n$.

For the halfspace-intersection family $F_n=T_n\wedge U_n$ from [105_halfspace_intersection_head_lower_bound.md](105_halfspace_intersection_head_lower_bound.md),

$$ \mathrm{actc}(F_n)\geq c n. $$

Thus $\mathrm{actc}$ correctly assigns large cost to the families that refute uncalibrated threshold-vote and LTF decision-list upper bounds.

## Lean Correspondence

`CubeCylinder` records disjoint positive and negative literal sets. Its
oriented expansion and uniform atom approximation are proved in
`Atoms/CylinderApproximation.lean`.

`CylinderThresholdCertificate` and
`AffineCylinderThresholdCertificate` are the finite strict-margin certificate
types for $\mathrm{ctc}$ and $\mathrm{actc}$. Both minimum costs are inhabited,
attained, and equipped with minimality theorems. The short Lean names are
`ctc` and `actc`.

The two compilers are `CylinderThresholdCertificate.computable` and
`AffineCylinderThresholdCertificate.computable`. The hierarchy is expressed
by `HStar_le_actc`, `actc_le_ctc`, `actc_le_affineFreeSparsity`, and
`actc_le_affineFreeSparsity_le_ptfSparsity`.

The headline theorem is
`thresholdDeg_le_HStar_le_actc_le_min_ctc_affineFreeSparsity` in
`Results/AffineCylinderThreshold.lean`. The degree support-count consequence is
`actc_le_one_add_sum_choose_of_ThresholdDegLE`.
