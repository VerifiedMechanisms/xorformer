import HeadComplexity.Foundation.FiniteFeatureSignLimit
import Mathlib.Order.Filter.AtTopBot.Basic

set_option linter.style.header false

/-!
# Weak signs from increasingly fine centered Hamming grids

This attaches the dense-grid argument to arbitrary subsequences of positive
replication counts. Its moving-evaluation hypothesis is supplied by compact
bounded-degree polynomial coefficients.
-/

namespace HeadComplexity.RoPEGridLimit

open scoped Topology
open Filter

def InCenteredGrid {ι : Type*} (m : ℕ) (q : ι → ℝ) : Prop :=
  ∀ i, ∃ k : ℕ, k ≤ m ∧ q i = 2 * (k : ℝ) / m - 1

noncomputable def gridApprox {ι : Type*} (m : ℕ) (q : ι → ℝ) : ι → ℝ :=
  fun i ↦ centeredGridApprox (m - 1) (q i)

theorem gridApprox_mem {ι : Type*} (m : ℕ) (hm : 0 < m) (q : ι → ℝ)
    (hq : ∀ i, -1 ≤ q i ∧ q i ≤ 1) : InCenteredGrid m (gridApprox m q) := by
  intro i
  obtain ⟨k, hk, he⟩ := centeredGridApprox_mem (m - 1) (q i) (hq i).1 (hq i).2
  have hm' : m - 1 + 1 = m := by omega
  refine ⟨k, by omega, ?_⟩
  change centeredGridApprox (m - 1) (q i) = _
  rw [he]
  norm_cast
  rw [hm']

theorem gridApprox_tendsto {ι : Type*} (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (q : ι → ℝ) (hq : ∀ i, -1 ≤ q i) :
    Tendsto (fun k ↦ gridApprox (m k) q) atTop (𝓝 q) := by
  exact (centeredGridApprox_pi_tendsto q hq).comp
    ((tendsto_sub_atTop_nat 1).comp hm)

/-- Any moving-evaluation limit of sign representatives on increasingly fine
centered grids has the weak source signs on the full continuous cube. -/
theorem weak_sign_of_grid_limit {ι : Type*}
    (P Q : (ι → ℝ) → ℝ) (R : ℕ → (ι → ℝ) → ℝ)
    (m : ℕ → ℕ) (hmpos : ∀ k, 0 < m k) (hm : Tendsto m atTop atTop)
    (hP : Continuous P)
    (hsign : ∀ k q, InCenteredGrid (m k) q → (0 < R k q ↔ 0 < P q))
    (hlimit : ∀ q (z : ℕ → (ι → ℝ)), Tendsto z atTop (𝓝 q) →
      Tendsto (fun k ↦ R k (z k)) atTop (𝓝 (Q q)))
    (q : ι → ℝ) (hq : ∀ i, -1 ≤ q i ∧ q i ≤ 1) :
    (0 < P q → 0 ≤ Q q) ∧ (P q < 0 → Q q ≤ 0) := by
  let z : ℕ → (ι → ℝ) := fun k ↦ gridApprox (m k) q
  have hz : Tendsto z atTop (𝓝 q) := gridApprox_tendsto m hm q (fun i ↦ (hq i).1)
  exact weak_sign_of_sequence_limit (fun k ↦ P (z k)) (fun k ↦ R k (z k))
    (P q) (Q q) (hP.continuousAt.tendsto.comp hz) (hlimit q z hz)
    (fun k ↦ hsign k (z k) (gridApprox_mem (m k) (hmpos k) q hq))

end HeadComplexity.RoPEGridLimit
