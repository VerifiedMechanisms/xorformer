import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
Three genuine heads have a collective Boolean zero relation although each
pair of their normalized feature spaces is linearly independent.
This is a dependency obstruction, not an unrestricted complexity lower bound.
-/

noncomputable section
namespace HeadComplexity.CollectiveThreeHeadRelation
open scoped BigOperators

def slopes : Fin 3 → Fin 5 → ℝ :=
  ![![2, 3, 3, 3, 3], ![2, 1, 2, 2, 2], ![1, 3, 2, 2, 2]]

def numeratorSlopes : Fin 3 → Fin 5 → ℝ :=
  ![![3, 0, 0, 0, 0], ![-6, -4, -4, -4, -4], ![2, 8, 4, 4, 4]]

theorem slopes_pos (h : Fin 3) (i : Fin 5) : 0 < slopes h i := by
  fin_cases h <;> fin_cases i <;> norm_num [slopes]

def denominator (h : Fin 3) (x : Fin 5 → Bool) : ℝ :=
  affineValue 1 (slopes h) x

def atom (h : Fin 3) : FracAtom 5 :=
  FracAtom.ofPositiveAffineRatio 0 (numeratorSlopes h) 1 (slopes h)
    (by norm_num) (slopes_pos h)

theorem atom_eval (h : Fin 3) (x : Fin 5 → Bool) :
    (atom h).eval x = affineValue 0 (numeratorSlopes h) x / denominator h x := by
  exact FracAtom.ofPositiveAffineRatio_eval ..

/-- The cleared relation is supported on only two Boolean ideal generators. -/
theorem cleared_identity (x y z : ℝ) :
    (3*x)*(1+2*x+y+2*z)*(1+x+3*y+2*z) +
      (-6*x-4*y-4*z)*(1+2*x+3*y+3*z)*(1+x+3*y+2*z) +
      (2*x+8*y+4*z)*(1+2*x+3*y+3*z)*(1+2*x+y+2*z) =
    (x^2-x)*(2*x+7*y+4*z+1) + (y^2-y)*(-11*x-12*y-12*z-4) := by ring

/-- The scalar identity holds with any nonnegative tail statistic. -/
theorem scalar_zero (x y : Bool) (z : ℝ) (hz : 0 ≤ z) :
    (3*boolToReal x)/(1+2*boolToReal x+3*boolToReal y+3*z) +
      (-6*boolToReal x-4*boolToReal y-4*z)/(1+2*boolToReal x+boolToReal y+2*z) +
      (2*boolToReal x+8*boolToReal y+4*z)/(1+boolToReal x+3*boolToReal y+2*z) = 0 := by
  have hx0 : 0 ≤ boolToReal x := by cases x <;> norm_num [boolToReal]
  have hy0 : 0 ≤ boolToReal y := by cases y <;> norm_num [boolToReal]
  have hx : (boolToReal x)^2 = boolToReal x := by cases x <;> norm_num [boolToReal]
  have hy : (boolToReal y)^2 = boolToReal y := by cases y <;> norm_num [boolToReal]
  have h1 : 1+2*boolToReal x+3*boolToReal y+3*z ≠ 0 := by positivity
  have h2 : 1+2*boolToReal x+boolToReal y+2*z ≠ 0 := by positivity
  have h3 : 1+boolToReal x+3*boolToReal y+2*z ≠ 0 := by positivity
  have hid := cleared_identity (boolToReal x) (boolToReal y) z
  rw [hx, hy] at hid
  field_simp
  nlinarith [hid]

/-- A genuine three-head exact zero score on the whole five-dimensional cube. -/
theorem sum_atom_eval_zero (x : Fin 5 → Bool) :
    ∑ h : Fin 3, (atom h).eval x = 0 := by
  norm_num [Fin.sum_univ_three, atom_eval, denominator, affineValue,
    Fin.sum_univ_succ, slopes, numeratorSlopes]
  have hz : 0 ≤ boolToReal (x 2) + boolToReal (x 3) + boolToReal (x 4) := by
    have h (i : Fin 5) : 0 ≤ boolToReal (x i) := by cases x i <;> norm_num [boolToReal]
    exact add_nonneg (add_nonneg (h 2) (h 3)) (h 4)
  convert scalar_zero (x 0) (x 1)
    (boolToReal (x 2) + boolToReal (x 3) + boolToReal (x 4)) hz using 1 <;> ring

/-- None of the three summands is the zero function. -/
theorem atom_nonzero (h : Fin 3) : ∃ x, (atom h).eval x ≠ 0 := by
  refine ⟨![true, false, false, false, false], ?_⟩
  fin_cases h <;>
    norm_num [atom_eval, denominator, affineValue, numeratorSlopes, slopes,
      Fin.sum_univ_succ, boolToReal]

/-- Normalized features contain the bias and five numerator slopes per head. -/
def pairScore (a b : Fin 3) (w : Fin 11 → ℝ) (x : Fin 5 → Bool) : ℝ :=
  w 0 + (w 1*boolToReal (x 0)+w 2*boolToReal (x 1)+w 3*boolToReal (x 2)+
    w 4*boolToReal (x 3)+w 5*boolToReal (x 4))/denominator a x +
    (w 6*boolToReal (x 0)+w 7*boolToReal (x 1)+w 8*boolToReal (x 2)+
    w 9*boolToReal (x 3)+w 10*boolToReal (x 4))/denominator b x

/-- Exact selected-row certificate for pair 0,1. -/
theorem pair_01_injective (w : Fin 11 → ℝ)
    (h : ∀ x, pairScore 0 1 w x = 0) : w = 0 := by
  have h0 := h ![false, false, false, false, false]
  have h1 := h ![false, false, false, false, true]
  have h2 := h ![false, false, false, true, false]
  have h3 := h ![false, false, false, true, true]
  have h4 := h ![false, false, true, false, false]
  have h5 := h ![false, false, true, false, true]
  have h6 := h ![false, false, true, true, false]
  have h7 := h ![false, true, false, false, false]
  have h8 := h ![false, true, false, false, true]
  have h9 := h ![true, false, false, false, false]
  have h10 := h ![true, false, false, false, true]
  norm_num [pairScore, denominator, affineValue, slopes, Fin.sum_univ_succ, boolToReal] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hw0 : w 0 = 0 := by
    linear_combination (1 : ℝ) * h0
  have hw1 : w 1 = 0 := by
    linear_combination (-13 : ℝ) * h0 + (60 : ℝ) * h1 + (-35 : ℝ) * h3 + (-35 : ℝ) * h5 + (35 : ℝ) * h6 + (18 : ℝ) * h9 + (-30 : ℝ) * h10
  have hw2 : w 2 = 0 := by
    linear_combination (-21 : ℝ) * h0 + (168 : ℝ) * h1 + (-175 : ℝ) * h3 + (-175 : ℝ) * h5 + (175 : ℝ) * h6 + (-28 : ℝ) * h7 + (56 : ℝ) * h8
  have hw3 : w 3 = 0 := by
    linear_combination (-14 : ℝ) * h0 + (70 : ℝ) * h3 + (84 : ℝ) * h4 + (-70 : ℝ) * h5 + (-70 : ℝ) * h6
  have hw4 : w 4 = 0 := by
    linear_combination (-14 : ℝ) * h0 + (84 : ℝ) * h2 + (-70 : ℝ) * h3 + (70 : ℝ) * h5 + (-70 : ℝ) * h6
  have hw5 : w 5 = 0 := by
    linear_combination (-14 : ℝ) * h0 + (84 : ℝ) * h1 + (-70 : ℝ) * h3 + (-70 : ℝ) * h5 + (70 : ℝ) * h6
  have hw6 : w 6 = 0 := by
    linear_combination (10 : ℝ) * h0 + (-60 : ℝ) * h1 + (35 : ℝ) * h3 + (35 : ℝ) * h5 + (-35 : ℝ) * h6 + (-15 : ℝ) * h9 + (30 : ℝ) * h10
  have hw7 : w 7 = 0 := by
    linear_combination (17/2 : ℝ) * h0 + (-84 : ℝ) * h1 + (175/2 : ℝ) * h3 + (175/2 : ℝ) * h5 + (-175/2 : ℝ) * h6 + (16 : ℝ) * h7 + (-28 : ℝ) * h8
  have hw8 : w 8 = 0 := by
    linear_combination (15/2 : ℝ) * h0 + (-105/2 : ℝ) * h3 + (-60 : ℝ) * h4 + (105/2 : ℝ) * h5 + (105/2 : ℝ) * h6
  have hw9 : w 9 = 0 := by
    linear_combination (15/2 : ℝ) * h0 + (-60 : ℝ) * h2 + (105/2 : ℝ) * h3 + (-105/2 : ℝ) * h5 + (105/2 : ℝ) * h6
  have hw10 : w 10 = 0 := by
    linear_combination (15/2 : ℝ) * h0 + (-60 : ℝ) * h1 + (105/2 : ℝ) * h3 + (105/2 : ℝ) * h5 + (-105/2 : ℝ) * h6
  funext i
  fin_cases i
  · exact hw0
  · exact hw1
  · exact hw2
  · exact hw3
  · exact hw4
  · exact hw5
  · exact hw6
  · exact hw7
  · exact hw8
  · exact hw9
  · exact hw10

/-- Exact selected-row certificate for pair 0,2. -/
theorem pair_02_injective (w : Fin 11 → ℝ)
    (h : ∀ x, pairScore 0 2 w x = 0) : w = 0 := by
  have h0 := h ![false, false, false, false, false]
  have h1 := h ![false, false, false, false, true]
  have h2 := h ![false, false, false, true, false]
  have h3 := h ![false, false, false, true, true]
  have h4 := h ![false, false, true, false, false]
  have h5 := h ![false, false, true, false, true]
  have h6 := h ![false, false, true, true, false]
  have h7 := h ![false, true, false, false, false]
  have h8 := h ![false, true, false, false, true]
  have h9 := h ![true, false, false, false, false]
  have h10 := h ![true, true, false, false, false]
  norm_num [pairScore, denominator, affineValue, slopes, Fin.sum_univ_succ, boolToReal] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hw0 : w 0 = 0 := by
    linear_combination (1 : ℝ) * h0
  have hw1 : w 1 = 0 := by
    linear_combination (-23/2 : ℝ) * h0 + (84 : ℝ) * h1 + (-105/2 : ℝ) * h3 + (-105/2 : ℝ) * h5 + (105/2 : ℝ) * h6 + (4 : ℝ) * h7 + (-42 : ℝ) * h8 + (-12 : ℝ) * h9 + (30 : ℝ) * h10
  have hw2 : w 2 = 0 := by
    linear_combination (-35/2 : ℝ) * h0 + (84 : ℝ) * h1 + (-105/2 : ℝ) * h3 + (-105/2 : ℝ) * h5 + (105/2 : ℝ) * h6 + (28 : ℝ) * h7 + (-42 : ℝ) * h8
  have hw3 : w 3 = 0 := by
    linear_combination (-14 : ℝ) * h0 + (70 : ℝ) * h3 + (84 : ℝ) * h4 + (-70 : ℝ) * h5 + (-70 : ℝ) * h6
  have hw4 : w 4 = 0 := by
    linear_combination (-14 : ℝ) * h0 + (84 : ℝ) * h2 + (-70 : ℝ) * h3 + (70 : ℝ) * h5 + (-70 : ℝ) * h6
  have hw5 : w 5 = 0 := by
    linear_combination (-14 : ℝ) * h0 + (84 : ℝ) * h1 + (-70 : ℝ) * h3 + (-70 : ℝ) * h5 + (70 : ℝ) * h6
  have hw6 : w 6 = 0 := by
    linear_combination (17/3 : ℝ) * h0 + (-56 : ℝ) * h1 + (35 : ℝ) * h3 + (35 : ℝ) * h5 + (-35 : ℝ) * h6 + (-8/3 : ℝ) * h7 + (28 : ℝ) * h8 + (10 : ℝ) * h9 + (-20 : ℝ) * h10
  have hw7 : w 7 = 0 := by
    linear_combination (27/2 : ℝ) * h0 + (-84 : ℝ) * h1 + (105/2 : ℝ) * h3 + (105/2 : ℝ) * h5 + (-105/2 : ℝ) * h6 + (-24 : ℝ) * h7 + (42 : ℝ) * h8
  have hw8 : w 8 = 0 := by
    linear_combination (15/2 : ℝ) * h0 + (-105/2 : ℝ) * h3 + (-60 : ℝ) * h4 + (105/2 : ℝ) * h5 + (105/2 : ℝ) * h6
  have hw9 : w 9 = 0 := by
    linear_combination (15/2 : ℝ) * h0 + (-60 : ℝ) * h2 + (105/2 : ℝ) * h3 + (-105/2 : ℝ) * h5 + (105/2 : ℝ) * h6
  have hw10 : w 10 = 0 := by
    linear_combination (15/2 : ℝ) * h0 + (-60 : ℝ) * h1 + (105/2 : ℝ) * h3 + (105/2 : ℝ) * h5 + (-105/2 : ℝ) * h6
  funext i
  fin_cases i
  · exact hw0
  · exact hw1
  · exact hw2
  · exact hw3
  · exact hw4
  · exact hw5
  · exact hw6
  · exact hw7
  · exact hw8
  · exact hw9
  · exact hw10

/-- Exact selected-row certificate for pair 1,2. -/
theorem pair_12_injective (w : Fin 11 → ℝ)
    (h : ∀ x, pairScore 1 2 w x = 0) : w = 0 := by
  have h0 := h ![false, false, false, false, false]
  have h1 := h ![false, false, false, false, true]
  have h2 := h ![false, false, false, true, false]
  have h3 := h ![false, false, true, false, false]
  have h4 := h ![false, true, false, false, false]
  have h5 := h ![false, true, false, false, true]
  have h6 := h ![false, true, false, true, false]
  have h7 := h ![false, true, true, false, false]
  have h8 := h ![true, false, false, false, false]
  have h9 := h ![true, false, false, false, true]
  have h10 := h ![true, true, false, false, false]
  norm_num [pairScore, denominator, affineValue, slopes, Fin.sum_univ_succ, boolToReal] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hw0 : w 0 = 0 := by
    linear_combination (1 : ℝ) * h0
  have hw1 : w 1 = 0 := by
    linear_combination (-51 : ℝ) * h0 + (189 : ℝ) * h1 + (24 : ℝ) * h4 + (-108 : ℝ) * h5 + (66 : ℝ) * h8 + (-180 : ℝ) * h9 + (60 : ℝ) * h10
  have hw2 : w 2 = 0 := by
    linear_combination (-41 : ℝ) * h0 + (147 : ℝ) * h1 + (24 : ℝ) * h4 + (-84 : ℝ) * h5 + (54 : ℝ) * h8 + (-140 : ℝ) * h9 + (40 : ℝ) * h10
  have hw3 : w 3 = 0 := by
    linear_combination (-39 : ℝ) * h0 + (147 : ℝ) * h1 + (-6 : ℝ) * h3 + (16 : ℝ) * h4 + (-84 : ℝ) * h5 + (12 : ℝ) * h7 + (54 : ℝ) * h8 + (-140 : ℝ) * h9 + (40 : ℝ) * h10
  have hw4 : w 4 = 0 := by
    linear_combination (-39 : ℝ) * h0 + (147 : ℝ) * h1 + (-6 : ℝ) * h2 + (16 : ℝ) * h4 + (-84 : ℝ) * h5 + (12 : ℝ) * h6 + (54 : ℝ) * h8 + (-140 : ℝ) * h9 + (40 : ℝ) * h10
  have hw5 : w 5 = 0 := by
    linear_combination (-39 : ℝ) * h0 + (141 : ℝ) * h1 + (16 : ℝ) * h4 + (-72 : ℝ) * h5 + (54 : ℝ) * h8 + (-140 : ℝ) * h9 + (40 : ℝ) * h10
  have hw6 : w 6 = 0 := by
    linear_combination (32 : ℝ) * h0 + (-126 : ℝ) * h1 + (-16 : ℝ) * h4 + (72 : ℝ) * h5 + (-42 : ℝ) * h8 + (120 : ℝ) * h9 + (-40 : ℝ) * h10
  have hw7 : w 7 = 0 := by
    linear_combination (78 : ℝ) * h0 + (-294 : ℝ) * h1 + (-44 : ℝ) * h4 + (168 : ℝ) * h5 + (-108 : ℝ) * h8 + (280 : ℝ) * h9 + (-80 : ℝ) * h10
  have hw8 : w 8 = 0 := by
    linear_combination (36 : ℝ) * h0 + (-147 : ℝ) * h1 + (9 : ℝ) * h3 + (-16 : ℝ) * h4 + (84 : ℝ) * h5 + (-12 : ℝ) * h7 + (-54 : ℝ) * h8 + (140 : ℝ) * h9 + (-40 : ℝ) * h10
  have hw9 : w 9 = 0 := by
    linear_combination (36 : ℝ) * h0 + (-147 : ℝ) * h1 + (9 : ℝ) * h2 + (-16 : ℝ) * h4 + (84 : ℝ) * h5 + (-12 : ℝ) * h6 + (-54 : ℝ) * h8 + (140 : ℝ) * h9 + (-40 : ℝ) * h10
  have hw10 : w 10 = 0 := by
    linear_combination (36 : ℝ) * h0 + (-138 : ℝ) * h1 + (-16 : ℝ) * h4 + (72 : ℝ) * h5 + (-54 : ℝ) * h8 + (140 : ℝ) * h9 + (-40 : ℝ) * h10
  funext i
  fin_cases i
  · exact hw0
  · exact hw1
  · exact hw2
  · exact hw3
  · exact hw4
  · exact hw5
  · exact hw6
  · exact hw7
  · exact hw8
  · exact hw9
  · exact hw10

end HeadComplexity.CollectiveThreeHeadRelation
