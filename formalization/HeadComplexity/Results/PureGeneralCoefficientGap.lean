import HeadComplexity.Results.PureGeneralSeparation
import Mathlib.Analysis.SpecificLimits.Basic

set_option linter.style.header false

/-!
# A uniform gap from oriented factor coefficients in every head dimension

The gap concerns the top squarefree coefficients of cleared polynomials.
It is uniform over all real factor parameters, including unbounded sequences.
The radius is existential and does not specify an effective replication count.
-/

namespace HeadComplexity.PureGeneralReplicatedGrid

open MvPolynomial VanillaGeneralCentered VanillaCoefficientLimit
open RoPEGeneralPhysicalCoordinates Filter
open scoped Topology

/-- Every nonzero scalar multiple of the physical source has a positive
uniform coefficient gap from all oriented same-head affine-factor sums. -/
theorem exists_oriented_top_coefficient_gap (h : ℕ) (hh : 2 ≤ h)
    (t : ℝ) (ht : t ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : Data (h + 1) (Input h),
      (∀ i, VanillaThreeCentered.Oriented (a.denominatorSlope i)) →
      ∃ e : Input h →₀ ℕ, (∀ i, e i ≤ 1) ∧
        e.sum (fun _ k => k) = h + 1 ∧
        ε ≤ |a.polynomial.coeff e - (C t * physical h).coeff e| := by
  classical
  by_contra hn
  push Not at hn
  have hex (k : ℕ) := hn (1 / ((k : ℝ) + 1)) (by positivity)
  choose a horient hdist using hex
  apply oriented_factor_limit_excluded h hh a t ht horient
  intro e he hdegree
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun _ => abs_nonneg _) (fun k => (hdist k e he hdegree).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

end HeadComplexity.PureGeneralReplicatedGrid
