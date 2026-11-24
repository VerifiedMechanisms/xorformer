import HeadComplexity.Polynomial.PureCubicChart
import Mathlib.Combinatorics.Nullstellensatz

set_option linter.style.header false

/-!
# Finite interpolation on the rational zero chart

This file checks the ten-point product-grid interpolation step and the scalar
graph identity. The divisibility and quantitative sign-rigidity arguments in
Theorem 22 are separate statements and are not asserted here.
-/

namespace HeadComplexity.PureCubicGraph

noncomputable section

open MvPolynomial

def chartScale : ℝ := 10 * 2 ^ 40

theorem chartScale_pos : 0 < chartScale := by norm_num [chartScale]

def gridPoint (j : Fin 10) : ℝ := (j.val : ℝ) / chartScale

theorem gridPoint_injective : Function.Injective gridPoint := by
  intro i j h
  apply Fin.ext
  have h' : (i.val : ℝ) = (j.val : ℝ) :=
    (div_left_inj' (ne_of_gt chartScale_pos)).mp h
  exact_mod_cast h'

def chartGrid : Finset ℝ := Finset.univ.image gridPoint

theorem chartGrid_card : chartGrid.card = 10 := by
  rw [chartGrid, Finset.card_image_of_injective _ gridPoint_injective]
  simp

theorem chartGrid_nonnegative {t : ℝ} (ht : t ∈ chartGrid) : 0 ≤ t := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
  exact div_nonneg (Nat.cast_nonneg _) (le_of_lt chartScale_pos)

theorem chartGrid_small {t : ℝ} (ht : t ∈ chartGrid) : t < 1 / 2 ^ 40 := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
  have hj : (j.val : ℝ) < 10 := by exact_mod_cast j.isLt
  apply (div_lt_iff₀ chartScale_pos).mpr
  norm_num [chartScale] at *

/-- A degree-at-most-nine polynomial vanishing on the 13-dimensional chart
grid is identically zero. This is finite interpolation, not a numerical rank
test at a selected subset of the grid. -/
theorem eq_zero_of_chartGrid (P : MvPolynomial (Fin 13) ℝ)
    (hdeg : P.totalDegree ≤ 9)
    (heval : ∀ y : Fin 13 → ℝ, (∀ i, y i ∈ chartGrid) → eval y P = 0) :
    P = 0 := by
  apply eq_zero_of_eval_zero_at_prod_finset P (fun _ ↦ chartGrid)
  · intro i
    rw [chartGrid_card]
    exact lt_of_le_of_lt ((degreeOf_le_totalDegree P i).trans hdeg) (by decide)
  · exact heval

def graphFirst (u₁ u₂ v₀ v₁ v₂ : ℝ) : ℝ :=
  -u₁ * (1 + v₀) / (1 + v₁) - u₂ * (1 + v₀) / (1 + v₂)

def coordinateCubic (u₀ u₁ u₂ v₀ v₁ v₂ : ℝ) : ℝ :=
  u₀ * (1 + v₁) * (1 + v₂) +
    u₁ * (1 + v₀) * (1 + v₂) + u₂ * (1 + v₀) * (1 + v₁)

theorem graphFirst_zero (u₁ u₂ v₀ v₁ v₂ : ℝ)
    (h₁ : 1 + v₁ ≠ 0) (h₂ : 1 + v₂ ≠ 0) :
    coordinateCubic (graphFirst u₁ u₂ v₀ v₁ v₂) u₁ u₂ v₀ v₁ v₂ = 0 := by
  dsimp [coordinateCubic, graphFirst]
  field_simp
  ring

theorem graphFirst_translate (u₁ u₂ v₀ v₁ v₂ t : ℝ)
    (h₁ : 1 + v₁ ≠ 0) (h₂ : 1 + v₂ ≠ 0) :
    coordinateCubic (graphFirst u₁ u₂ v₀ v₁ v₂ + t) u₁ u₂ v₀ v₁ v₂ =
      t * (1 + v₁) * (1 + v₂) := by
  have h := graphFirst_zero u₁ u₂ v₀ v₁ v₂ h₁ h₂
  dsimp [coordinateCubic] at *
  linarith

end
end HeadComplexity.PureCubicGraph
