import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# A six-fraction gate on three Boolean coordinates

This is an exact auxiliary localization identity. It is not a proof of
the requested worst-case head bound.
-/

namespace HeadComplexity

noncomputable def sixFractionGate (w p : ℝ) : ℝ :=
  1 / (p + 5 + 4*w) + 1 / (p + 7 + w) + 1 / (p + 3 + 4*w) -
  1 / (p + 5 + 2*w) - 1 / (p + 3 + 5*w) - 1 / (p + 7 + 2*w)

theorem sixFractionGate_zero (p : ℝ) : sixFractionGate 0 p = 0 := by
  unfold sixFractionGate
  ring

theorem sixFractionGate_one (p : ℝ) : sixFractionGate 1 p = 0 := by
  unfold sixFractionGate
  have h₁ : p + 5 + 4*1 = p + 7 + 2*1 := by ring
  have h₂ : p + 7 + 1 = p + 3 + 5*1 := by ring
  have h₃ : p + 3 + 4*1 = p + 5 + 2*1 := by ring
  rw [h₁, h₂, h₃]
  ring

theorem sixFractionGate_two (p : ℝ) : sixFractionGate 2 p = 0 := by
  unfold sixFractionGate
  have h₁ : p + 5 + 4*2 = p + 3 + 5*2 := by ring
  have h₂ : p + 7 + 2 = p + 5 + 2*2 := by ring
  have h₃ : p + 3 + 4*2 = p + 7 + 2*2 := by ring
  rw [h₁, h₂, h₃]
  ring

theorem sixFractionGate_three_formula (p : ℝ) (hp : 0 ≤ p) :
    sixFractionGate 3 p =
      (72*p^2 + 2016*p + 13800) /
      ((p+10)*(p+11)*(p+13)*(p+15)*(p+17)*(p+18)) := by
  have h₁ : p+10 ≠ 0 := by positivity
  have h₂ : p+11 ≠ 0 := by positivity
  have h₃ : p+13 ≠ 0 := by positivity
  have h₄ : p+15 ≠ 0 := by positivity
  have h₅ : p+17 ≠ 0 := by positivity
  have h₆ : p+18 ≠ 0 := by positivity
  unfold sixFractionGate
  norm_num
  ring_nf
  field_simp
  ring

theorem sixFractionGate_three_pos (p : ℝ) (hp : 0 ≤ p) :
    0 < sixFractionGate 3 p := by
  rw [sixFractionGate_three_formula p hp]
  positivity

theorem sixFractionGate_boolean_identity (x y z p : ℝ)
    (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (hz : z = 0 ∨ z = 1) :
    sixFractionGate (x+y+z) p = x*y*z*sixFractionGate 3 p := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    rcases hz with rfl | rfl <;>
    norm_num [sixFractionGate_zero, sixFractionGate_one, sixFractionGate_two]

end HeadComplexity
