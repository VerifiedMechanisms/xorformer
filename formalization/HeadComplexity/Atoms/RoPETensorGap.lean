import HeadComplexity.Atoms.RoPETensorFactors
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Matrix.Normed

set_option linter.style.header false

/-!
# A positive distance from every oriented three-factor tensor

The compact frame obstruction is uniform over unbounded factor parameters.
This gives a positive metric gap around every nonzero rescaling of the
physical source tensor. The radius here is existential; the separate
mathematical estimate supplies an explicit numerical radius for the source.
-/

namespace HeadComplexity.RoPEThreeTensor

open scoped Topology BigOperators Matrix.Norms.Elementwise
open Filter

abbrev Tensor := Fin 6 → Matrix (Fin 6) (Fin 6) ℝ
abbrev Rows := Matrix (Fin 3) (Fin 6) ℝ

/-- The physical source tensor stays a fixed positive distance from all
three-factor tensors possessing an oriented nonzero first-block row. -/
theorem exists_dist_gap_oriented_factorTensor
    (ε δ aScale : ℝ) (hε : ε ≠ 0) (hδ : δ ≠ 0) (haScale : aScale ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ D₁ N₁ D₂ N₂ D₃ N₃ : Rows,
      (∃ h σ, (∀ j, 0 ≤ σ * D₁ h j) ∧ 0 < ∑ j, σ * D₁ h j) →
      r ≤ dist (factorTensor D₁ N₁ D₂ N₂ D₃ N₃)
        (aScale • factorTensor (denominatorRows ε) (numeratorRows δ)
          (denominatorRows ε) (numeratorRows δ) (denominatorRows ε) (numeratorRows δ)) := by
  classical
  by_contra hn
  push Not at hn
  have hex (k : ℕ) := hn (1 / ((k : ℝ) + 1)) (by positivity)
  choose D₁ N₁ D₂ N₂ D₃ N₃ horient hdist using hex
  apply no_tendsto_scaled_physical_source_factorTensor ε δ aScale hε hδ haScale
    D₁ N₁ D₂ N₂ D₃ N₃ horient
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ (hdist k).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

theorem physical_source_entry (ε δ : ℝ) :
    factorTensor (denominatorRows ε) (numeratorRows δ)
      (denominatorRows ε) (numeratorRows δ) (denominatorRows ε) (numeratorRows δ)
      0 1 2 = 6 * ε ^ 2 * δ := by
  simp [factorTensor, crossContraction, denominatorRows, numeratorRows, cross,
    Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem physical_source_ne_zero (ε δ : ℝ) (hε : ε ≠ 0) (hδ : δ ≠ 0) :
    factorTensor (denominatorRows ε) (numeratorRows δ)
      (denominatorRows ε) (numeratorRows δ) (denominatorRows ε) (numeratorRows δ) ≠ 0 := by
  intro he
  have hc := congrFun (congrFun (congrFun he 0) 1) 2
  rw [physical_source_entry] at hc
  exact (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hε)) hδ) hc

/-- Zero tensors can be included without any nonconstant-denominator premise.
This covers both cases arising from a vanilla three-head cleared polynomial. -/
theorem exists_dist_gap_or_zero_factorTensor
    (ε δ aScale : ℝ) (hε : ε ≠ 0) (hδ : δ ≠ 0) (haScale : aScale ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ D₁ N₁ D₂ N₂ D₃ N₃ : Rows,
      (factorTensor D₁ N₁ D₂ N₂ D₃ N₃ = 0 ∨
        ∃ h σ, (∀ j, 0 ≤ σ * D₁ h j) ∧ 0 < ∑ j, σ * D₁ h j) →
      r ≤ dist (factorTensor D₁ N₁ D₂ N₂ D₃ N₃)
        (aScale • factorTensor (denominatorRows ε) (numeratorRows δ)
          (denominatorRows ε) (numeratorRows δ) (denominatorRows ε) (numeratorRows δ)) := by
  obtain ⟨r, hr, hbound⟩ := exists_dist_gap_oriented_factorTensor ε δ aScale hε hδ haScale
  let T : Tensor := aScale • factorTensor (denominatorRows ε) (numeratorRows δ)
    (denominatorRows ε) (numeratorRows δ) (denominatorRows ε) (numeratorRows δ)
  have hT : T ≠ 0 := smul_ne_zero haScale (physical_source_ne_zero ε δ hε hδ)
  refine ⟨min r (dist 0 T), lt_min hr (dist_pos.mpr (Ne.symm hT)), ?_⟩
  intro D₁ N₁ D₂ N₂ D₃ N₃ hcase
  rcases hcase with hz | ho
  · rw [hz]
    exact min_le_right _ _
  · exact (min_le_left _ _).trans (hbound D₁ N₁ D₂ N₂ D₃ N₃ ho)

end HeadComplexity.RoPEThreeTensor
