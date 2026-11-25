import HeadComplexity.Polynomial.VanillaCoefficientLimit
import HeadComplexity.Polynomial.RoPEGeneralPhysicalBlocks

set_option linter.style.header false

/-! # Reindexing actual factor limits into physical source blocks -/

namespace HeadComplexity.VanillaFactorReindex

open MvPolynomial VanillaGeneralCentered VanillaCoefficientLimit
open RoPEGeneralPhysicalBlocks RoPEGeneralPolarization
open PureGeneralReplicatedGrid
open scoped BigOperators Topology
open Filter

noncomputable def reindex {H : ℕ} {σ τ : Type*} (e : τ ≃ σ) (a : Data H σ) : Data H τ where
  denominatorConstant := a.denominatorConstant
  numeratorConstant := a.numeratorConstant
  denominatorSlope := fun h i ↦ a.denominatorSlope h (e i)
  numeratorSlope := fun h i ↦ a.numeratorSlope h (e i)

theorem affine_rename_equiv {σ τ : Type*} [Fintype σ] [Fintype τ]
    (e : τ ≃ σ) (c : ℝ) (v : σ → ℝ) :
    RoPECrossBlockCoefficients.affine c (fun i ↦ v (e i)) =
      rename e.symm (RoPECrossBlockCoefficients.affine c v) := by
  classical
  simp only [RoPECrossBlockCoefficients.affine, map_add, map_sum, map_mul, rename_C, rename_X]
  rw [← e.sum_comp]
  simp

theorem reindex_polynomial {H : ℕ} {σ τ : Type*} [Fintype σ] [Fintype τ]
    (e : τ ≃ σ) (a : Data H σ) : (reindex e a).polynomial = rename e.symm a.polynomial := by
  classical
  simp only [Data.polynomial, reindex, affine_rename_equiv, map_sum, map_mul, map_prod]

theorem reindex_oriented {H : ℕ} {σ τ : Type*} (e : τ ≃ σ) (a : Data H σ)
    (ha : ∀ h, VanillaThreeCentered.Oriented (a.denominatorSlope h)) :
    ∀ h, VanillaThreeCentered.Oriented ((reindex e a).denominatorSlope h) := by
  intro h
  rcases ha h with hp | hn | hz
  · exact Or.inl (fun i ↦ hp (e i))
  · exact Or.inr (Or.inl (fun i ↦ hn (e i)))
  · exact Or.inr (Or.inr (fun i ↦ hz (e i)))

theorem coeff_rename_equiv {σ τ : Type*} (e : τ ≃ σ)
    (P : MvPolynomial σ ℝ) (d : τ →₀ ℕ) :
    (rename e.symm P).coeff d = P.coeff (d.mapDomain e) := by
  have h := coeff_rename_mapDomain e e.injective (rename e.symm P) d
  rw [rename_rename] at h
  simpa only [Equiv.self_comp_symm, rename_id, AlgHom.id_apply] using h.symm

theorem top_limit_reindex {H n : ℕ} {σ : Type*} [Fintype σ]
    (e : σ ≃ Fin n) (a : ℕ → Data H (Fin n)) (P : MvPolynomial (Fin n) ℝ)
    (hlim : TopCoefficientLimit a P) (d : σ →₀ ℕ)
    (hd : ∀ i, d i ≤ 1) (hcard : d.sum (fun _ k ↦ k) = H) :
    Tendsto (fun k ↦ (reindex e (a k)).polynomial.coeff d) atTop
      (𝓝 ((rename e.symm P).coeff d)) := by
  have hd' : ∀ i, (d.mapDomain e) i ≤ 1 := by
    intro i
    simpa only [Finsupp.mapDomain_equiv_apply] using hd (e.symm i)
  have hc' : (d.mapDomain e).sum (fun _ k ↦ k) = H := by
    rw [Finsupp.sum_mapDomain_index]
    · exact hcard
    · intro i; rfl
    · intro i a b; rfl
  simpa only [reindex_polynomial, coeff_rename_equiv] using hlim (d.mapDomain e) hd' hc'

/-- The actual source factor limit becomes a limit to the homogeneous physical
block lift used in the rank calculation. -/
theorem top_limit_physical_blocks (m : ℕ)
    (a : ℕ → Data (m + 2) (Fin (groupCount (m + 2)))) (t : ℝ)
    (hlim : TopCoefficientLimit a (C t * RoPEGeneralPhysicalCoordinates.physical (m + 1)))
    (d : (Block m × Local m) →₀ ℕ) (hd : ∀ i, d i ≤ 1)
    (hcard : d.sum (fun _ k ↦ k) = m + 2) :
    Tendsto (fun k ↦ (reindex (physicalEquiv m) (a k)).polynomial.coeff d) atTop
      (𝓝 ((C t * blockLift m (localSource m 0)).coeff d)) := by
  have he := top_limit_reindex (physicalEquiv m) a
    (C t * RoPEGeneralPhysicalCoordinates.physical (m + 1)) hlim d hd hcard
  simp only [map_mul, rename_C, coeff_C_mul] at he ⊢
  change Tendsto _ _ (𝓝 (t * (reindexedPhysical m).coeff d)) at he
  rw [reindexedPhysical_top_coeff m d hcard] at he
  exact he

end HeadComplexity.VanillaFactorReindex
