import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Exact residue interpolation identity used in the collision-cluster audit. -/

namespace HeadComplexity.RoPEClusterMoments

open scoped BigOperators

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- Multiplying residues by the polynomial vanishing at all but one pole
isolates that residue. No distinctness assumption on the poles is needed. -/
theorem sum_residue_annihilator (s : Finset ι) (a r : ι → R)
    (t : ι) (ht : t ∈ s) :
    ∑ i ∈ s, a i * ∏ j ∈ s.erase t, (r i - r j) =
      a t * ∏ j ∈ s.erase t, (r t - r j) := by
  apply Finset.sum_eq_single t
  · intro i hi hit
    have hz : ∏ j ∈ s.erase t, (r i - r j) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hit, hi⟩)
      exact sub_self (r i)
    rw [hz, mul_zero]
  · intro h
    exact (h ht).elim

/-- A multiscale collision with bounded first moment. The weights here are
the actual residues multiplied by the common factor t cubed. -/
theorem four_cluster_first_moment (t x y a d : R) :
    (3 * a - 2 * t * d) * (t * x) +
      (-3 * a + t * d) * (2 * t * x + t ^ 2 * y) +
      a * (3 * t * x + 3 * t ^ 2 * y) = t ^ 3 * (d * y) := by
  ring

/-- After division by t cubed, the limiting second moment uses four
independent linear coordinates. -/
theorem four_cluster_second_moment (t x y a d : R) :
    (3 * a - 2 * t * d) * (t * x) ^ 2 +
      (-3 * a + t * d) * (2 * t * x + t ^ 2 * y) ^ 2 +
      a * (3 * t * x + 3 * t ^ 2 * y) ^ 2 =
    t ^ 3 * (6 * a * x * y + 2 * d * x ^ 2 + 6 * t * a * y ^ 2 +
      4 * t * d * x * y + t ^ 2 * d * y ^ 2) := by
  ring

/-- The same example has a nonzero fourth-order pole. It therefore does
not refute a collision obstruction assuming that higher poles vanish. -/
theorem four_cluster_third_moment (t x y a d : R) :
    (3 * a - 2 * t * d) * (t * x) ^ 3 +
      (-3 * a + t * d) * (2 * t * x + t ^ 2 * y) ^ 3 +
      a * (3 * t * x + 3 * t ^ 2 * y) ^ 3 =
    t ^ 3 * (6 * a * x ^ 3 + t * (45 * a * x ^ 2 * y + 6 * d * x ^ 3) +
      t ^ 2 * (63 * a * x * y ^ 2 + 12 * d * x ^ 2 * y) +
      t ^ 3 * (24 * a * y ^ 3 + 6 * d * x * y ^ 2) + t ^ 4 * d * y ^ 3) := by
  ring

end HeadComplexity.RoPEClusterMoments
