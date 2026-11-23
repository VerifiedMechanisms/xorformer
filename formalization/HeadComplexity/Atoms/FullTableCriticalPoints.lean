import HeadComplexity.Atoms.ProjectiveCriticalPoints
import Mathlib.LinearAlgebra.Matrix.Symmetric

set_option linter.style.header false

/-!
# Algebraic checks for the full-table Gram-metric construction

These ingredients do not formalize the analytic implicit-function argument.
They check the Gram lower bound, the energy differential identity, and the
weighted pair reconstruction needed by the written critical-point theorem.
No asymptotic head lower bound is asserted.
-/

namespace HeadComplexity.FullTableCriticalPoints

open Finset Matrix
open scoped BigOperators

theorem singleton_energy_bound {ι X : Type*} [Fintype ι] [Fintype X]
    [DecidableEq ι] [DecidableEq X]
    (e : ι → X) (he : Function.Injective e) (ψ : ι → X → ℝ)
    (hψ : ∀ i j, ψ i (e j) = if i = j then 1 else 0) (v : ι → ℝ) :
    (∑ i, (v i)^2) ≤ ∑ x, (∑ i, v i * ψ i x)^2 := by
  have hsingle : ∀ j, (∑ i, v i * ψ i (e j)) = v j := by
    intro j
    simp [hψ]
  calc
    (∑ i, (v i)^2) = ∑ i, (∑ j, v j * ψ j (e i))^2 := by simp_rw [hsingle]
    _ = ∑ x ∈ Finset.univ.image e, (∑ j, v j * ψ j x)^2 := by
      rw [Finset.sum_image]
      exact fun a _ b _ hab ↦ he hab
    _ ≤ ∑ x, (∑ j, v j * ψ j x)^2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro x _ _
      positivity

/-- Algebraic form of differentiating `K = G r`, with `G` symmetric. -/
theorem energy_differential_identity {ι : Type*} [Fintype ι]
    (G dG : Matrix ι ι ℝ) (hG : G.IsSymm)
    (K dK r dr : ι → ℝ) (hK : K = G.mulVec r)
    (hdK : dK = dG.mulVec r + G.mulVec dr) :
    dotProduct dK r + dotProduct K dr =
      2 * dotProduct dK r - dotProduct r (dG.mulVec r) := by
  have hsym : dotProduct (G.mulVec r) dr = dotProduct r (G.mulVec dr) := by
    rw [dotProduct_comm]
    exact hG.dotProduct_mulVec_comm (x := dr) (y := r)
  have hd : dotProduct dK r = dotProduct r (dG.mulVec r) +
      dotProduct r (G.mulVec dr) := by
    rw [hdK, add_dotProduct]
    rw [dotProduct_comm (dG.mulVec r) r, dotProduct_comm (G.mulVec dr) r]
  rw [hK, hsym]
  linarith

theorem weighted_pair_kernel {d k : ℕ} (hd : 0 < d) (hk : 2 ≤ k)
    (a : Fin d → ℝ) (t c : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (ht : ∀ j, 0 < t j)
    (da : Fin d → ℝ) (dt : Fin k → ℝ)
    (hfirst : ∀ j, a ⟨0, hd⟩ * dt j = (1 + t j) * da ⟨0, hd⟩)
    (hother : ∀ i, a i * dt ⟨0, by omega⟩ =
      (1 + t ⟨0, by omega⟩) * da i)
    (hnonzero : c ⟨0, by omega⟩ * (1 + t ⟨0, by omega⟩) +
      c ⟨1, by omega⟩ * (1 + t ⟨1, by omega⟩) ≠ 0)
    (hpair :
      (c ⟨1, by omega⟩ * (1 + t ⟨1, by omega⟩) -
        c ⟨0, by omega⟩ * t ⟨1, by omega⟩) * dt ⟨0, by omega⟩ +
      (c ⟨0, by omega⟩ * (1 + t ⟨0, by omega⟩) -
        c ⟨1, by omega⟩ * t ⟨0, by omega⟩) * dt ⟨1, by omega⟩ = 0) :
    da = 0 ∧ dt = 0 := by
  let i0 : Fin d := ⟨0, hd⟩
  let j0 : Fin k := ⟨0, by omega⟩
  let j1 : Fin k := ⟨1, by omega⟩
  let lam : ℝ := da i0 / a i0
  have ha0 : a i0 ≠ 0 := (ha i0).ne'
  have hdt : ∀ j, dt j = (1 + t j) * lam := by
    intro j
    dsimp [lam]
    rw [← mul_div_assoc]
    apply (eq_div_iff ha0).2
    simpa [mul_comm, mul_div_assoc] using hfirst j
  have hda : ∀ i, da i = a i * lam := by
    intro i
    have hi := hother i
    change a i * dt j0 = (1 + t j0) * da i at hi
    rw [hdt] at hi
    apply (mul_left_cancel₀ (show 1 + t j0 ≠ 0 by have := ht j0; positivity))
    nlinarith only [hi]
  have hpair' : (c j1 * (1 + t j1) - c j0 * t j1) * dt j0 +
      (c j0 * (1 + t j0) - c j1 * t j0) * dt j1 = 0 := hpair
  rw [hdt, hdt] at hpair'
  have hprod : (c j0 * (1 + t j0) + c j1 * (1 + t j1)) * lam = 0 := by
    convert hpair' using 1 <;> ring
  have hlam : lam = 0 := (mul_eq_zero.mp hprod).resolve_left hnonzero
  constructor
  · funext i
    simp [hda i, hlam]
  · funext j
    simp [hdt j, hlam]

/-- The scalar balance equations in the limiting sharp-well system have an
invertible diagonal derivative when their explicitly checked factors are nonzero. -/
theorem sharp_well_kernel {ι : Type*} (η C r v : ι → ℝ)
    (hη : ∀ i, η i ≠ 0) (hC : ∀ i, C i ≠ 0) (hr : ∀ i, r i ≠ 0)
    (hv : ∀ i, (-2 * η i * C i * r i) * v i = 0) : v = 0 := by
  funext i
  exact (mul_eq_zero.mp (hv i)).resolve_left
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (hη i)) (hC i)) (hr i))

end HeadComplexity.FullTableCriticalPoints

#print axioms HeadComplexity.FullTableCriticalPoints.singleton_energy_bound
#print axioms HeadComplexity.FullTableCriticalPoints.energy_differential_identity
#print axioms HeadComplexity.FullTableCriticalPoints.weighted_pair_kernel
#print axioms HeadComplexity.FullTableCriticalPoints.sharp_well_kernel
