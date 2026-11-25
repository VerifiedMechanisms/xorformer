import Mathlib.Algebra.BigOperators.Ring.Finset

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

end HeadComplexity.RoPEClusterMoments
