import Mathlib.Analysis.Convex.Segment

import HeadComplexity.Foundation.Vec

set_option linter.style.header false

/-!
# Segment crossing obstruction.

If a point `P` lies on the segment `[p, q]` and also on the segment
`[r, s]`, then no linear functional can place `p, q` strictly below
a threshold `τ` while placing `r, s` strictly above it. This is the
geometric core of the one-head XOR impossibility argument.
-/

namespace HeadComplexity

/-- **Segment crossing obstruction.** If a point `P` lies simultaneously on
the segments `[p, q]` and `[r, s]`, then no linear functional `L` can place
`L p, L q` weakly below a threshold `τ` while placing `L r, L s` strictly
above `τ`. The asymmetry (weak `≤` on one side, strict `<` on the other) is
exactly what the XOR-impossibility application needs. -/
theorem segment_cross_not_separable
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {p q r s : V} (L : V →ₗ[ℝ] ℝ) {τ : ℝ}
    (hp : L p ≤ τ) (hq : L q ≤ τ) (hr : τ < L r) (hs : τ < L s)
    {P : V} (hPpq : P ∈ segment ℝ p q) (hPrs : P ∈ segment ℝ r s) : False := by
  have hle : L P ≤ τ := (convex_halfSpace_le L.isLinear τ).segment_subset hp hq hPpq
  have hgt : τ < L P := (convex_halfSpace_gt L.isLinear τ).segment_subset hr hs hPrs
  exact (not_lt_of_ge hle) hgt

end HeadComplexity
