import HeadComplexity.Polynomial.RoPEGeneralFactorRank
import HeadComplexity.Polynomial.RoPEGeneralPolarization

/-!
# Actual vanilla mixed contractions have small rank on denominator kernels

The diagonal coefficient projection is linear, so the generic derivative
factorization applies to the literal centered vanilla factors directly.
-/

noncomputable section

namespace HeadComplexity.RoPEVanillaContractionRank

open RoPEGeneralPolarization RoPEGeneralDerivative RoPEGeneralFactorRank

variable {H m : ℕ} {σ : Type*} [Fintype σ]

theorem contractMap_eq_projected_derivative
    (a : VanillaGeneralCentered.Data H (Block m × σ)) (v : σ → ℝ) :
    contractMap m a.polynomial v =
      (projection m).comp (derivativeMap
        (VanillaBlockDerivatives.blockDirectionLinear (some none : Block m))
        (directional (VanillaBlockDerivatives.blockDirection (none : Block m) v)
          a.polynomial)) := by
  apply LinearMap.ext
  intro w
  rfl

theorem contractMap_rank_le
    (a : VanillaGeneralCentered.Data H (Block m × σ)) (v : σ → ℝ)
    (hv : (VanillaBlockDerivatives.denominatorRows a (none : Block m)).mulVec v = 0) :
    Module.finrank ℝ (contractMap m a.polynomial v).range ≤ H := by
  rw [contractMap_eq_projected_derivative]
  exact data_block_projected_second_rank_le a (none : Block m)
    (some none : Block m) v (projection m) hv

open scoped BigOperators

/-- Uniform row orientation supplies a simplex normal as soon as the matrix is
nonzero. No lower bound on row magnitudes is required. -/
theorem exists_oriented_row_of_ne_zero {r : ℕ} {ι : Type*} [Fintype ι]
    (D : Matrix (Fin r) ι ℝ)
    (hrows : ∀ h, VanillaThreeCentered.Oriented (D h)) (hne : D ≠ 0) :
    ∃ h s, (∀ i, 0 ≤ s * D h i) ∧ 0 < ∑ i, s * D h i := by
  classical
  have hex : ∃ h i, D h i ≠ 0 := by
    by_contra hn
    apply hne
    ext h i
    by_contra hi
    exact hn ⟨h, i, hi⟩
  obtain ⟨h, i, hi⟩ := hex
  rcases hrows h with hp | hn | hz
  · refine ⟨h, 1, fun j ↦ by simpa using (hp j).le, ?_⟩
    exact Finset.sum_pos' (fun j _ ↦ by simpa using (hp j).le)
      ⟨i, Finset.mem_univ _, by simpa using hp i⟩
  · refine ⟨h, -1, fun j ↦ by simpa using (neg_pos.mpr (hn j)).le, ?_⟩
    exact Finset.sum_pos' (fun j _ ↦ by simpa using (neg_pos.mpr (hn j)).le)
      ⟨i, Finset.mem_univ _, by simpa using neg_pos.mpr (hn i)⟩
  · exact (hi (hz i)).elim

theorem data_oriented_row_of_ne_zero
    (a : VanillaGeneralCentered.Data H (Block m × σ))
    (ha : ∀ h, VanillaThreeCentered.Oriented (a.denominatorSlope h))
    (hne : VanillaBlockDerivatives.denominatorRows a (none : Block m) ≠ 0) :
    ∃ h s, (∀ i, 0 ≤ s * a.denominatorSlope h (none, i)) ∧
      0 < ∑ i, s * a.denominatorSlope h (none, i) := by
  apply exists_oriented_row_of_ne_zero
    (VanillaBlockDerivatives.denominatorRows a (none : Block m)) ?_ hne
  intro h
  rcases ha h with hp | hn | hz
  · exact Or.inl (fun i ↦ hp (none, i))
  · exact Or.inr (Or.inl (fun i ↦ hn (none, i)))
  · exact Or.inr (Or.inr (fun i ↦ hz (none, i)))

end HeadComplexity.RoPEVanillaContractionRank
