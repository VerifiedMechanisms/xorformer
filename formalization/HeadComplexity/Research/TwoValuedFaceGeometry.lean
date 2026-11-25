import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace HeadComplexity.TwoValuedFaceGeometry

/-- A two-dimensional affine ratio with positive denominator cannot have
nonconstant unit-valued output when the two denominator slopes vanish
simultaneously and, in that case, the two numerator slopes also vanish
simultaneously. These
are the zero-pattern implications imposed by the original common alpha/delta. -/
theorem four_corner_labels_constant
    (a0 a1 a2 b0 b1 b2 : ℝ) (s00 s10 s01 s11 : Bool)
    (hb00 : 0 < b0) (hb10 : 0 < b0+b1)
    (hb01 : 0 < b0+b2) (hb11 : 0 < b0+b1+b2)
    (hden : b1=0 ↔ b2=0)
    (hnum : b1=0 → (a1=0 ↔ a2=0))
    (h00 : a0 = (if s00 then 1 else -1)*b0)
    (h10 : a0+a1 = (if s10 then 1 else -1)*(b0+b1))
    (h01 : a0+a2 = (if s01 then 1 else -1)*(b0+b2))
    (h11 : a0+a1+a2 = (if s11 then 1 else -1)*(b0+b1+b2)) :
    s00=s10 ∧ s00=s01 ∧ s00=s11 := by
  cases s00 <;> cases s10 <;> cases s01 <;> cases s11 <;>
    norm_num at h00 h10 h01 h11 ⊢
  all_goals first
  | linarith
  | have hz1 : b1=0 := by linarith
    have hz2 : b2=0 := hden.mp hz1
    have ha1 : a1=0 := by linarith
    have ha2 : a2=0 := (hnum hz1).mp ha1
    linarith
  | have hz2 : b2=0 := by linarith
    have hz1 : b1=0 := hden.mpr hz2
    have ha2 : a2=0 := by linarith
    have ha1 : a1=0 := (hnum hz1).mpr ha2
    linarith

end HeadComplexity.TwoValuedFaceGeometry
