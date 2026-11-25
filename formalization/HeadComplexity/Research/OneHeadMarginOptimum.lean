import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.OneHeadMarginOptimum

/-- Four unit-gap and norm-budget rows force a quadratic lower bound.
The denominator slope may have either sign. -/
theorem four_row_budget (a b c d K : ℝ)
    (hc : 0 < c) (hB : 0 < c+5*d)
    (h0 : -K*c ≤ a) (h1 : a+b ≤ -(c+d))
    (h2 : c+2*d ≤ a+2*b) (h5 : a+5*b ≤ K*(c+5*d)) :
    (11:ℝ)/5 < K ∧ 0 ≤ 5*K^2-22*K+5 := by
  have hb : 2*c+3*d ≤ b := by linarith
  have hd : 4*d ≤ (K-3)*c := by nlinarith
  have hK : (11:ℝ)/5 < K := by
    by_contra hh
    have hn : 5*K-11 ≤ 0 := by linarith
    have hp := mul_nonpos_of_nonpos_of_nonneg hn hc.le
    nlinarith
  have hr : 0 ≤ (K-7)*c+(5*K-11)*d := by nlinarith
  have hm := mul_nonneg (show 0 ≤ 5*K-11 by linarith) (sub_nonneg.mpr hd)
  have hp : 0 ≤ c*(5*K^2-22*K+5) := by nlinarith
  exact ⟨hK, (nonneg_of_mul_nonneg_right hp hc)⟩

/-- The sharp root selected by the four rows. -/
theorem four_row_budget_sharp (a b c d K : ℝ)
    (hc : 0 < c) (hB : 0 < c+5*d)
    (h0 : -K*c ≤ a) (h1 : a+b ≤ -(c+d))
    (h2 : c+2*d ≤ a+2*b) (h5 : a+5*b ≤ K*(c+5*d)) :
    (11+4*Real.sqrt 6)/5 ≤ K := by
  obtain ⟨hK, hp⟩ := four_row_budget a b c d K hc hB h0 h1 h2 h5
  have hs : (Real.sqrt 6)^2 = 6 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  by_contra hh
  have hl : K < (11+4*Real.sqrt 6)/5 := lt_of_not_ge hh
  have hm := mul_pos (show 0 < (11+4*Real.sqrt 6)/5-K by linarith)
    (show 0 < 5*((11+4*Real.sqrt 6)/5)+5*K-22 by linarith)
  nlinarith

/-- Explicit interior positive-slope optimizer parameters. -/
theorem sharp_parameters :
    let K := (11+4*Real.sqrt 6)/5
    let d := (K-3)/4
    let a := -K
    let b := 2+3*d
    0 < d ∧ a = -K ∧ a+b = -(1+d) ∧
      a+2*b = 1+2*d ∧ a+5*b = K*(1+5*d) := by
  dsimp
  have hs : (Real.sqrt 6)^2 = 6 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have hs1 : 1 < Real.sqrt 6 := by nlinarith
  constructor
  · linarith
  constructor
  · rfl
  constructor
  · ring
  constructor
  · ring
  nlinarith

/-- An affine ratio with positive cross determinant is strictly increasing
on every interval with positive denominator. -/
theorem ratio_strict_mono (a b d x y : ℝ)
    (hx : 0 < 1+d*x) (hy : 0 < 1+d*y)
    (hxy : x < y) (hdet : 0 < b-a*d) :
    (a+b*x)/(1+d*x) < (a+b*y)/(1+d*y) := by
  apply (div_lt_div_iff₀ hx hy).mpr
  have hp := mul_pos (sub_pos.mpr hxy) hdet
  nlinarith

end HeadComplexity.OneHeadMarginOptimum
