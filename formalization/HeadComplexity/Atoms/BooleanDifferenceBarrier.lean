import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false

/-! A Boolean mixed difference of one admissible head need not have affine signs. -/

namespace HeadComplexity.BooleanDifferenceBarrier

theorem second_difference_identity (A D a b u v : ℝ)
    (hD : D ≠ 0) (hu : D + u ≠ 0) (hv : D + v ≠ 0)
    (huv : D + u + v ≠ 0) :
    A / D - (A + a) / (D + u) - (A + b) / (D + v) +
        (A + a + b) / (D + u + v) =
      (A * u * v * (2 * D + u + v) -
        a * v * D * (D + v) - b * u * D * (D + u)) /
        (D * (D + u) * (D + v) * (D + u + v)) := by
  field_simp
  ring

noncomputable def ratio (x y u v : ℝ) : ℝ :=
  (127 / 210 + (8 / 15) * (x + y) + u) / (1 + x + y + u + 2 * v)

noncomputable def mixedDifference (x y : ℝ) : ℝ :=
  ratio x y 0 0 - ratio x y 1 0 - ratio x y 0 1 + ratio x y 1 1

theorem difference_values :
    mixedDifference 0 0 = 1 / 504 ∧ mixedDifference 0 1 = -(1 / 1800) ∧
    mixedDifference 1 0 = -(1 / 1800) ∧ mixedDifference 1 1 = 1 / 4200 := by
  norm_num [mixedDifference, ratio]

theorem difference_signs (x y : Bool) :
    (0 < mixedDifference (boolToReal x) (boolToReal y)) ↔ x = y := by
  cases x <;> cases y <;> norm_num [boolToReal, mixedDifference, ratio]

theorem no_affine_sign_representation :
    ¬ ∃ c a b : ℝ, ∀ x y : Bool,
      (0 < c + a * boolToReal x + b * boolToReal y) ↔
        0 < mixedDifference (boolToReal x) (boolToReal y) := by
  rintro ⟨c, a, b, h⟩
  have h00 := h false false
  have h01 := h false true
  have h10 := h true false
  have h11 := h true true
  norm_num [boolToReal, mixedDifference, ratio] at h00 h01 h10 h11
  linarith

theorem exists_actual_atom :
    ∃ φ : FracAtom 4, ∀ bits : Fin 4 → Bool,
      φ.eval bits = ratio (boolToReal (bits 0)) (boolToReal (bits 1))
        (boolToReal (bits 2)) (boolToReal (bits 3)) := by
  let a : Fin 4 → ℝ := ![8 / 15, 8 / 15, 1, 0]
  let b : Fin 4 → ℝ := ![1, 1, 1, 2]
  have hb : ∀ i, 0 < b i := by
    intro i
    fin_cases i <;> norm_num [b]
  refine ⟨FracAtom.ofPositiveAffineRatio (127 / 210) a 1 b (by norm_num) hb, ?_⟩
  intro bits
  rw [FracAtom.ofPositiveAffineRatio_eval]
  simp [affineValue, Fin.sum_univ_succ, a, b, ratio]
  congr 1 <;> ring

end HeadComplexity.BooleanDifferenceBarrier
