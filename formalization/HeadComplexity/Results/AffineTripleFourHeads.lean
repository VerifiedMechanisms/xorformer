import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Results.LowComplexity
import Mathlib.Tactic

set_option linter.style.header false

/-! Four admissible heads compute the sign of three arbitrary affine forms.
The statement uses the existing architecture and permits zeros in the product. -/

namespace HeadComplexity
open scoped BigOperators

theorem four_ratio_product_identity (A D u v : ℝ)
    (hD : D ≠ 0) (hu : D + u ≠ 0) (hv : D + v ≠ 0)
    (huv : D + u + v ≠ 0) :
    A / D - A / (D + u) - A / (D + v) + A / (D + u + v) =
      (A * u * v) * (2 * D + u + v) / (D * (D + u) * (D + v) * (D + u + v)) := by
  field_simp
  ring

theorem four_ratio_product_pos_iff (A D u v : ℝ)
    (hD : 0 < D) (hu : 0 < D + u) (hv : 0 < D + v)
    (huv : 0 < D + u + v) :
    0 < A / D - A / (D + u) - A / (D + v) + A / (D + u + v) ↔
      0 < A * u * v := by
  rw [four_ratio_product_identity A D u v hD.ne' hu.ne' hv.ne' huv.ne',
    div_pos_iff_of_pos_right (mul_pos (mul_pos (mul_pos hD hu) hv) huv),
    mul_pos_iff_of_pos_right (show 0 < 2 * D + u + v by linarith)]

noncomputable def affineTriplePredicate {n : ℕ} (c : Fin 3 → ℝ)
    (a : Fin 3 → Fin n → ℝ) : (Fin n → Bool) → Bool :=
  fun x ↦ decide (0 < affineValue (c 0) (a 0) x *
    affineValue (c 1) (a 1) x * affineValue (c 2) (a 2) x)

theorem computableWithHeadsN_affineTriple {n : ℕ} (c : Fin 3 → ℝ)
    (a : Fin 3 → Fin n → ℝ) :
    computableWithHeadsN n 4 (affineTriplePredicate c a) := by
  classical
  let d₀ : ℝ := 1 + |c 1| + |c 2|
  let d : Fin n → ℝ := fun i ↦ 1 + |a 1 i| + |a 2 i|
  have hpos (u v : ℝ) : 0 < 1 + |u| + |v| ∧
      0 < 1 + |u| + |v| + u ∧ 0 < 1 + |u| + |v| + v ∧
      0 < 1 + |u| + |v| + u + v := by
    have h₁ := neg_abs_le u
    have h₂ := neg_abs_le v
    have h₃ := abs_nonneg u
    have h₄ := abs_nonneg v
    constructor
    · positivity
    constructor
    · linarith
    constructor <;> linarith
  let num₀ : Fin 4 → ℝ := ![c 0, -c 0, -c 0, c 0]
  let num : Fin 4 → Fin n → ℝ := ![a 0, fun i ↦ -a 0 i, fun i ↦ -a 0 i, a 0]
  let den₀ : Fin 4 → ℝ := ![d₀, d₀ + c 1, d₀ + c 2, d₀ + c 1 + c 2]
  let den : Fin 4 → Fin n → ℝ :=
    ![d, fun i ↦ d i + a 1 i, fun i ↦ d i + a 2 i, fun i ↦ d i + a 1 i + a 2 i]
  have hc (h : Fin 4) : 0 < den₀ h := by
    have hp := hpos (c 1) (c 2)
    fin_cases h <;> simp_all [den₀, d₀]
  have ha (h : Fin 4) (i : Fin n) : 0 < den h i := by
    have hp := hpos (a 1 i) (a 2 i)
    fin_cases h <;> simp_all [den, d]
  apply computableWithHeadsN_of_positiveAffineRatios num₀ num den₀ den hc ha 0
  intro x
  have hp (h : Fin 4) := affineValue_pos (den₀ h) (den h) (hc h) (ha h) x
  have hN : affineValue (-c 0) (fun i ↦ -a 0 i) x = -affineValue (c 0) (a 0) x := by
    simp [affineValue, Finset.sum_neg_distrib]
    ring
  have he₁ := affineValue_add d₀ (c 1) d (a 1) x
  have he₂ := affineValue_add d₀ (c 2) d (a 2) x
  have he₃ : affineValue (d₀ + c 1 + c 2) (fun i ↦ d i + a 1 i + a 2 i) x =
      affineValue d₀ d x + affineValue (c 1) (a 1) x + affineValue (c 2) (a 2) x := by
    rw [affineValue_add, he₁]
  have hp₀ := hp 0
  have hp₁ := hp 1
  have hp₂ := hp 2
  have hp₃ := hp 3
  simp only [den₀, den, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at hp₀ hp₁ hp₂ hp₃
  rw [he₁] at hp₁
  rw [he₂] at hp₂
  rw [he₃] at hp₃
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, num₀, num,
    den₀, den, Matrix.cons_val_zero, Matrix.cons_val_succ, zero_add, add_zero]
  rw [hN, he₁, he₂, he₃]
  simp only [neg_div]
  rw [show affineValue (c 0) (a 0) x / affineValue d₀ d x +
      (-(affineValue (c 0) (a 0) x / (affineValue d₀ d x + affineValue (c 1) (a 1) x)) +
      (-(affineValue (c 0) (a 0) x / (affineValue d₀ d x + affineValue (c 2) (a 2) x)) +
      affineValue (c 0) (a 0) x /
        (affineValue d₀ d x + affineValue (c 1) (a 1) x + affineValue (c 2) (a 2) x))) =
      affineValue (c 0) (a 0) x / affineValue d₀ d x -
      affineValue (c 0) (a 0) x / (affineValue d₀ d x + affineValue (c 1) (a 1) x) -
      affineValue (c 0) (a 0) x / (affineValue d₀ d x + affineValue (c 2) (a 2) x) +
      affineValue (c 0) (a 0) x /
        (affineValue d₀ d x + affineValue (c 1) (a 1) x + affineValue (c 2) (a 2) x) by ring]
  rw [four_ratio_product_pos_iff _ _ _ _ hp₀ hp₁ hp₂ hp₃]
  simp [affineTriplePredicate]

theorem HStar_affineTriple_le {n : ℕ} (c : Fin 3 → ℝ) (a : Fin 3 → Fin n → ℝ) :
    HStar n (affineTriplePredicate c a) ≤ 4 :=
  HStar_le_of_computableWithHeadsN (computableWithHeadsN_affineTriple c a)

end HeadComplexity
