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

/-- The first three moments isolate one residue at three distinct nonzero
leading poles. This is the Vandermonde elimination used in the Laurent audit. -/
theorem three_pole_moment_elimination (a b c A B C : R) :
    (a ^ 3 * A + b ^ 3 * B + c ^ 3 * C) -
      (b + c) * (a ^ 2 * A + b ^ 2 * B + c ^ 2 * C) +
      b * c * (a * A + b * B + c * C) =
    a * (a - b) * (a - c) * A := by
  ring

/-- Vanishing first three moments force the first residue to vanish when
its leading pole is nonzero and distinct from the other two. -/
theorem first_residue_zero_of_three_moments [NoZeroDivisors R]
    (a b c A B C : R) (ha : a ≠ 0) (hab : a ≠ b) (hac : a ≠ c)
    (h₁ : a * A + b * B + c * C = 0)
    (h₂ : a ^ 2 * A + b ^ 2 * B + c ^ 2 * C = 0)
    (h₃ : a ^ 3 * A + b ^ 3 * B + c ^ 3 * C = 0) : A = 0 := by
  have he := three_pole_moment_elimination a b c A B C
  rw [h₁, h₂, h₃] at he
  have hz : a * (a - b) * (a - c) * A = 0 := by simpa using he.symm
  exact (mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (mul_ne_zero ha (sub_ne_zero.mpr hab)) (sub_ne_zero.mpr hac))

end HeadComplexity.RoPEClusterMoments
