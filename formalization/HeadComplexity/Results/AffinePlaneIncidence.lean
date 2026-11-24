import Mathlib

set_option linter.style.header false

/-! The exact incidence cancellation for the affine-plane reverse decoder.
Only nonvertical affine lines are used. Distinct points with different
first coordinates have exactly one common line; points with the same first
coordinate have none. The statement permits arbitrary real interpolation
coefficients and arbitrary real line contributions. -/

namespace HeadComplexity
namespace AxisZeroGluing

open scoped BigOperators

variable {F : Type*} [Field F]

def affinePlaneSlope (h g : F × F) : F := (g.2 - h.2) / (g.1 - h.1)

theorem affinePlane_incident_iff {h g : F × F} (hx : g.1 ≠ h.1) (a : F) :
    g.2 = a * g.1 + (h.2 - a * h.1) ↔ a = affinePlaneSlope h g := by
  have hd : g.1 - h.1 ≠ 0 := sub_ne_zero.mpr hx
  unfold affinePlaneSlope
  rw [eq_div_iff hd]
  constructor <;> intro he <;> linear_combination -he

theorem affinePlane_incident_same_first {h g : F × F} (hx : g.1 = h.1)
    (a : F) :
    g.2 = a * g.1 + (h.2 - a * h.1) ↔ g = h := by
  constructor
  · intro he
    apply Prod.ext hx
    linear_combination he + a * hx
  · rintro rfl
    ring

/-- Sum over the pencil through `h`, then exchange the order of summation.
The only off-diagonal term from a point `g` is its unique shared line. -/
theorem affinePlane_weighted_pencil_identity
    [Fintype F] [DecidableEq F]
    (h : F × F) (η : F → ℝ) (V : F → (F × F) → ℝ) :
    (∑ a : F, η a * ∑ g : F × F,
      if g.2 = a * g.1 + (h.2 - a * h.1) then V a g else 0) =
      (∑ a : F, η a * V a h) +
      ∑ g : F × F, if g.1 ≠ h.1 then
        η (affinePlaneSlope h g) * V (affinePlaneSlope h g) g else 0 := by
  classical
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  have hpoint (g : F × F) :
      (∑ a : F, if g.2 = a * g.1 + (h.2 - a * h.1)
        then η a * V a g else 0) =
      (if g = h then ∑ a : F, η a * V a h else 0) +
      (if g.1 ≠ h.1 then
        η (affinePlaneSlope h g) * V (affinePlaneSlope h g) g else 0) := by
    by_cases hx : g.1 = h.1
    · simp_rw [affinePlane_incident_same_first hx]
      by_cases hg : g = h
      · subst g
        simp
      · simp [hg, hx]
    · have hg : g ≠ h := fun he ↦ hx (congrArg Prod.fst he)
      simp_rw [affinePlane_incident_iff hx]
      simp [hg, hx]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp

/-- The pencil selector is one row of a rank factorization indexed by all
nonvertical affine lines. -/
theorem affinePlane_line_rank_identity [Fintype F] [DecidableEq F]
    (h : F × F) (η : F → ℝ) (Z : (F × F) → ℝ) :
    (∑ l : F × F, (if l.2 = h.2 - l.1 * h.1 then η l.1 else 0) * Z l) =
      ∑ a : F, η a * Z (a, h.2 - a * h.1) := by
  classical
  simp [Fintype.sum_prod_type, ite_mul]

end AxisZeroGluing
end HeadComplexity
