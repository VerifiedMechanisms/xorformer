import HeadComplexity.Results.PureThreeSeparationLimit
import HeadComplexity.Polynomial.RoPEPhysicalTensor

set_option linter.style.header false

/-!
# Eventual exclusion of averaged witnesses for the explicit pure family

This theorem uses the actual physical source polynomial, its affine
coordinate change and irreducibility, and its mixed cubic tensor. The
remaining architectural bridge is construction of an averaged witness from
a vanilla representation.
-/

namespace HeadComplexity.PureThreeSeparationLimit

open MvPolynomial RoPEPhysicalCoordinates RoPEPhysicalTensor
open scoped Topology
open Filter

theorem physical_sign_rigidity (Q : Poly) (hQ : Q ≠ 0) (hdeg : Q.totalDegree ≤ 3)
    (hweak : ∀ q, (∀ i, -1 ≤ q i ∧ q i ≤ 1) →
      (0 < eval q physical → 0 ≤ eval q Q) ∧
      (eval q physical < 0 → eval q Q ≤ 0)) :
    ∃ a : ℝ, a ≠ 0 ∧ Q = C a * physical := by
  have hclosed (q : Fin 18 → ℝ) (hq : q ∈ openCube) :
      ∀ i, -1 ≤ q i ∧ q i ≤ 1 := fun i ↦ ⟨(hq i (Set.mem_univ i)).1.le,
        (hq i (Set.mem_univ i)).2.le⟩
  obtain ⟨a, ha, he⟩ := positive_scalar_multiple_of_weak_sign_cube Q hQ hdeg
    (fun q hq ↦ (hweak q (hclosed q hq)).1)
    (fun q hq ↦ (hweak q (hclosed q hq)).2)
  exact ⟨a, ha.ne', he⟩

theorem no_physical_averaged_witness_sequence (m : ℕ → ℕ)
    (hmpos : ∀ k, 0 < m k) (hm : Tendsto m atTop atTop)
    (w : ∀ k, AveragedWitness physical (m k)) : False :=
  no_averaged_witness_sequence physical physical_sign_rigidity
    mixedTensor_physical mixedTensor_physical_ne_zero m hmpos hm w

/-- The explicit pure source eventually has no averaged three-factor
representation with the exact vanilla denominator orientation. -/
theorem eventually_no_physical_averaged_witness :
    ∀ᶠ m in atTop, ¬Nonempty (AveragedWitness physical m) :=
  eventually_no_witness_of_no_sequence (AveragedWitness physical)
    no_physical_averaged_witness_sequence

end HeadComplexity.PureThreeSeparationLimit
