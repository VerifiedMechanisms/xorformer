import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# An eight-fraction gate on four Boolean coordinates

An auxiliary switching identity. No universal head bound follows here.
-/

namespace HeadComplexity

noncomputable def eightFractionGate (s y p : ℝ) : ℝ :=
  let b := p + 5 + 5*s + 5*y
  1 / (b+3*y) + 1 / (b-2+2*s+2*y) + 1 / (b-2+s+y) +
    1 / (b+15/4-s-7*y/4) -
    (1 / b + 1 / (b-2+s+4*y) + 1 / (b-2+2*s+y) +
      1 / (b+15/4-s-3*y/4))

theorem eightFractionGate_y_zero (s p : ℝ) :
    eightFractionGate s 0 p = 0 := by
  unfold eightFractionGate
  ring

theorem eightFractionGate_s_zero (p : ℝ) :
    eightFractionGate 0 1 p = 0 := by
  unfold eightFractionGate
  ring_nf

theorem eightFractionGate_s_one (p : ℝ) :
    eightFractionGate 1 1 p = 0 := by
  unfold eightFractionGate
  ring_nf

theorem eightFractionGate_s_two (p : ℝ) :
    eightFractionGate 2 1 p = 0 := by
  unfold eightFractionGate
  ring_nf

theorem eightFractionGate_corner_formula (p : ℝ) (hp : 0 ≤ p) :
    eightFractionGate 3 1 p =
      72*(2*p+55) /
      ((p+25)*(p+30)*(p+24)*(p+27)*(p+28)*(p+31)) := by
  have h₁ : p+25 ≠ 0 := by positivity
  have h₂ : p+30 ≠ 0 := by positivity
  have h₃ : p+24 ≠ 0 := by positivity
  have h₄ : p+27 ≠ 0 := by positivity
  have h₅ : p+28 ≠ 0 := by positivity
  have h₆ : p+31 ≠ 0 := by positivity
  unfold eightFractionGate
  norm_num
  ring_nf
  field_simp
  ring

theorem eightFractionGate_corner_pos (p : ℝ) (hp : 0 ≤ p) :
    0 < eightFractionGate 3 1 p := by
  rw [eightFractionGate_corner_formula p hp]
  positivity

theorem eightFractionGate_boolean_identity (x y z w p : ℝ)
    (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1)
    (hz : z = 0 ∨ z = 1) (hw : w = 0 ∨ w = 1) :
    eightFractionGate (x+z+w) y p =
      x*y*z*w*eightFractionGate 3 1 p := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    rcases hz with rfl | rfl <;> rcases hw with rfl | rfl <;>
    norm_num [eightFractionGate_y_zero, eightFractionGate_s_zero,
      eightFractionGate_s_one, eightFractionGate_s_two]

end HeadComplexity
