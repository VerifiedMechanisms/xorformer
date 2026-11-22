import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! Two positive denominator pairs have identical strict orders on all cube
vertices but different feasible sign patterns. This refutes an order-type
compression shortcut, not the target asymptotic head lower bound. -/
namespace HeadComplexity
namespace DenominatorOrder
open Finset
open scoped BigOperators

def vertices : Fin 10 → Fin 4 → ℤ := ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 1, 0, 0], ![0, 1, 0, 1], ![0, 1, 1, 0], ![1, 0, 0, 0], ![1, 0, 1, 1], ![1, 1, 1, 1], ![0, 0, 1, 0]]

def kernelWeights : Fin 10 → ℤ := ![15280061511, 18335091357, -699843495, -1295248396, -1388636097, 421929807, 192383607, -1435996937, 827171622, 8631597]

def rightCoefficients : Fin 9 → ℤ := ![25, -558, -976, -1518, 214, 307, 0, 388, -266]

def leftMatrix : Matrix (Fin 10) (Fin 9) ℤ := ![![5, 0, 0, 0, 0, 0, 0, 0, 0], ![95, 0, 0, 0, 19, 0, 0, 0, 5], ![3649, 0, 0, 89, 89, 0, 0, 41, 41], ![6435, 0, 165, 0, 0, 0, 39, 0, 0], ![7697, 0, 179, 0, 179, 0, 43, 0, 43], ![17625, 0, 235, 235, 0, 0, 75, 75, 0], ![3315, 195, 0, 0, 0, 17, 0, 0, 0], ![15903, 279, 0, 279, 279, 57, 0, 57, 57], ![41705, 439, 439, 439, 439, 95, 95, 95, 95], ![2775, 0, 0, 75, 0, 0, 0, 37, 0]]

def rightMatrix : Matrix (Fin 10) (Fin 9) ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0], ![20, 0, 0, 0, 4, 0, 0, 0, 5], ![738, 0, 0, 18, 18, 0, 0, 41, 41], ![1287, 0, 33, 0, 0, 0, 39, 0, 0], ![1548, 0, 36, 0, 36, 0, 43, 0, 43], ![3525, 0, 47, 47, 0, 0, 75, 75, 0], ![663, 39, 0, 0, 0, 17, 0, 0, 0], ![3192, 56, 0, 56, 56, 57, 0, 57, 57], ![8360, 88, 88, 88, 88, 95, 95, 95, 95], ![555, 0, 0, 15, 0, 0, 0, 37, 0]]

def allAValues : Fin 16 → ℤ := ![1, 5, 37, 41, 39, 43, 75, 79, 17, 21, 53, 57, 55, 59, 91, 95]

def allLeftValues : Fin 16 → ℤ := ![5, 19, 75, 89, 165, 179, 235, 249, 195, 209, 265, 279, 355, 369, 425, 439]

def allRightValues : Fin 16 → ℤ := ![1, 4, 15, 18, 33, 36, 47, 50, 39, 42, 53, 56, 71, 74, 85, 88]

theorem strict_identical_orders :
    Function.Injective allAValues ∧ Function.Injective allLeftValues ∧
      Function.Injective allRightValues ∧
      ∀ i j, (allLeftValues i < allLeftValues j ↔ allRightValues i < allRightValues j) := by
  decide +kernel

theorem kernelWeights_ne_zero : ∀ i, kernelWeights i ≠ 0 := by decide +kernel

theorem left_kernel : ∀ j, ∑ i, kernelWeights i * leftMatrix i j = 0 := by
  decide +kernel

theorem right_strict_witness :
    ∀ i, 0 < kernelWeights i * ∑ j, rightMatrix i j * rightCoefficients j := by
  decide +kernel

noncomputable def matrixScore (M : Matrix (Fin 10) (Fin 9) ℤ)
    (u : Fin 9 → ℝ) (i : Fin 10) : ℝ := ∑ j, (M i j : ℝ) * u j

theorem left_score_annihilator (u : Fin 9 → ℝ) :
    ∑ i, (kernelWeights i : ℝ) * matrixScore leftMatrix u i = 0 := by
  simp only [matrixScore, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hz (j : Fin 9) : (∑ i, (kernelWeights i : ℝ) * (leftMatrix i j : ℝ)) = 0 := by
    exact_mod_cast left_kernel j
  simp_rw [← mul_assoc, ← Finset.sum_mul, hz, zero_mul]
  simp

/-- No real numerator coefficients realize the prescribed strict signs for
the left denominator pair. -/
theorem left_infeasible : ¬ ∃ u : Fin 9 → ℝ,
    ∀ i, 0 < (kernelWeights i : ℝ) * matrixScore leftMatrix u i := by
  rintro ⟨u, hu⟩
  have hpos : 0 < ∑ i, (kernelWeights i : ℝ) * matrixScore leftMatrix u i :=
    Finset.sum_pos (fun i _ ↦ hu i) Finset.univ_nonempty
  rw [left_score_annihilator] at hpos
  exact lt_irrefl 0 hpos

/-- The same signs are feasible for the right denominator pair. -/
theorem right_feasible : ∃ u : Fin 9 → ℝ,
    ∀ i, 0 < (kernelWeights i : ℝ) * matrixScore rightMatrix u i := by
  refine ⟨fun j ↦ (rightCoefficients j : ℝ), ?_⟩
  intro i
  dsimp [matrixScore]
  exact_mod_cast right_strict_witness i

/-- The matrices are the cleared score evaluations at the listed vertices. -/
theorem matrices_are_evaluations : ∀ i,
    let x := vertices i
    let a := 1 + 16 * x 0 + 38 * x 1 + 36 * x 2 + 4 * x 3
    let bL := 5 + 190 * x 0 + 160 * x 1 + 70 * x 2 + 14 * x 3
    let bR := 1 + 38 * x 0 + 32 * x 1 + 14 * x 2 + 3 * x 3
    leftMatrix i = ![a*bL, x 0*bL, x 1*bL, x 2*bL, x 3*bL,
      x 0*a, x 1*a, x 2*a, x 3*a] ∧
    rightMatrix i = ![a*bR, x 0*bR, x 1*bR, x 2*bR, x 3*bR,
      x 0*a, x 1*a, x 2*a, x 3*a] := by
  intro i
  fin_cases i <;> constructor <;> funext j <;> fin_cases j <;>
    norm_num [vertices, leftMatrix, rightMatrix]

def cubeVertex (j : Fin 16) (i : Fin 4) : ℤ :=
  (j.val / 2 ^ (3 - i.val) % 2 : ℕ)

theorem full_tables_are_evaluations : ∀ j,
    let x := cubeVertex j
    allAValues j = 1 + 16 * x 0 + 38 * x 1 + 36 * x 2 + 4 * x 3 ∧
    allLeftValues j = 5 + 190 * x 0 + 160 * x 1 + 70 * x 2 + 14 * x 3 ∧
    allRightValues j = 1 + 38 * x 0 + 32 * x 1 + 14 * x 2 + 3 * x 3 := by
  decide +kernel


noncomputable def aSlopes : Fin 4 → ℝ := ![16, 38, 36, 4]
noncomputable def bSlopes : Fin 4 → ℝ := ![38, 32, 14, 3]
noncomputable def uSlopes : Fin 4 → ℝ := ![-558, -976, -1518, 214]
noncomputable def vSlopes : Fin 4 → ℝ := ![307, 0, 388, -266]

noncomputable def exampleFunction (x : Fin 4 → Bool) : Bool :=
  decide (0 < 25 + affineValue 0 uSlopes x / affineValue 1 aSlopes x +
    affineValue 0 vSlopes x / affineValue 1 bSlopes x)

/-- The feasible score is implemented by two heads of the original model. -/
theorem exampleFunction_computable : computableWithHeadsN 4 2 exampleFunction := by
  let num₀ : Fin 2 → ℝ := ![0, 0]
  let num : Fin 2 → Fin 4 → ℝ := ![uSlopes, vSlopes]
  let den₀ : Fin 2 → ℝ := ![1, 1]
  let den : Fin 2 → Fin 4 → ℝ := ![aSlopes, bSlopes]
  apply computableWithHeadsN_of_positiveAffineRatios num₀ num den₀ den
    (fun h ↦ by fin_cases h <;> norm_num [den₀])
    (fun h i ↦ by fin_cases h <;> fin_cases i <;> norm_num [den, aSlopes, bSlopes]) 25
  intro x
  simp only [Fin.sum_univ_two, num₀, num, den₀, den, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp [exampleFunction, add_assoc]

end DenominatorOrder
end HeadComplexity
