import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Tactic

set_option linter.style.header false

/-! Finite, explicit avoidance of the roots of a polynomial inside a positive
interval. This supplies the algebraic transfer step for auxiliary jet matrices. -/
namespace HeadComplexity.PolynomialPositiveGrid

open Polynomial Finset
open scoped BigOperators

noncomputable def grid (D : ℕ) (s : ℝ) (j : Fin (D + 1)) : ℝ :=
  ((j.val : ℝ) + 1) / (((D : ℝ) + 2) * s)

theorem grid_injective (D : ℕ) (s : ℝ) (hs : 0 < s) :
    Function.Injective (grid D s) := by
  intro i j hij
  have hden : ((D : ℝ) + 2) * s ≠ 0 := by positivity
  have hm := congrArg (fun z : ℝ ↦ z * (((D : ℝ) + 2) * s)) hij
  simp only [grid, div_mul_cancel₀ _ hden] at hm
  apply Fin.ext
  have hc : (i.val : ℝ) = (j.val : ℝ) := by linarith
  exact_mod_cast hc

theorem grid_positive (D : ℕ) (s : ℝ) (hs : 0 < s) (j : Fin (D + 1)) :
    0 < grid D s j := by
  unfold grid
  positivity

theorem grid_small (D : ℕ) (s : ℝ) (hs : 0 < s) (j : Fin (D + 1)) :
    grid D s j * s < 1 := by
  have hj : (j.val : ℝ) < (D : ℝ) + 1 := by exact_mod_cast j.isLt
  have hden : 0 < ((D : ℝ) + 2) * s := by positivity
  unfold grid
  rw [div_mul_eq_mul_div, div_lt_one hden]
  nlinarith

/-- Among the first degree-plus-one rational grid points, one avoids the roots. -/
theorem exists_grid_nonzero (p : ℝ[X]) (hp : p ≠ 0) (D : ℕ)
    (hdegree : p.natDegree ≤ D) (s : ℝ) (hs : 0 < s) :
    ∃ j : Fin (D + 1), 0 < grid D s j ∧ grid D s j * s < 1 ∧
      p.eval (grid D s j) ≠ 0 := by
  by_contra! h
  apply hp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    (grid_injective D s hs)
  · intro j
    exact h j (grid_positive D s hs j) (grid_small D s hs j)
  · simpa using Nat.lt_succ_of_le hdegree

theorem homotopy_constant_positive (n d : ℕ) (hd : d ≤ n)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hsmall : δ * ((n : ℝ) + 3) < 1) :
    0 < 1 + δ * (ε + 1 - (d : ℝ)) := by
  have hd' : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hd
  have hprod := mul_le_mul_of_nonneg_left hd' hδ.le
  have heprod : 0 < δ * ε := mul_pos hδ hε
  nlinarith

theorem homotopy_slope_positive (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hsmall : δ * ((n : ℝ) + 3) < 1) : 0 < 1 - 2 * δ := by
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith [mul_nonneg hδ.le hn]

/-- The elementary determinant degree bound, without a genericity assumption. -/
theorem natDegree_det_le {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ[X]) (d : ℕ) (hdegree : ∀ i j, (A i j).natDegree ≤ d) :
    A.det.natDegree ≤ Fintype.card I * d := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  calc
    (Equiv.Perm.sign σ • ∏ i, A (σ i) i).natDegree ≤
        (∏ i, A (σ i) i).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · rw [h, one_smul]
      · rw [h, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ i, (A (σ i) i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : I, d := Finset.sum_le_sum fun i _ ↦ hdegree (σ i) i
    _ = _ := by simp

end HeadComplexity.PolynomialPositiveGrid
