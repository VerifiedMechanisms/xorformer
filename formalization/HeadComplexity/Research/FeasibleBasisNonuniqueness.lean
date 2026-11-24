import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
Two genuine two-head scores have the same seven unit-level active sample rows,
with independent normalized features, full-cube unit slack, and a common
coefficient box. Their eighth labels differ. Thus global feasibility does not
make an active-basis chart have a unique truth-table extension.
-/

noncomputable section
namespace HeadComplexity.FeasibleBasisNonuniqueness
open scoped BigOperators

def slopes : Fin 2 → Fin 2 → Fin 3 → ℝ :=
  ![![![1, 1, 2], ![2, 3, 1]], ![![1, 1, 1], ![3, 3, 1]]]

def coefficients : Fin 2 → Fin 7 → ℝ :=
  ![![3, 4, 4/3, -12, -12, -32/3, 4], ![-3, -6, -6, -24, 28, 28, 32]]

def denominator (k h : Fin 2) (x : Fin 3 → Bool) : ℝ :=
  affineValue 1 (slopes k h) x

def linearScore (k : Fin 2) (a : Fin 7 → ℝ) (x : Fin 3 → Bool) : ℝ :=
  a 0 + (a 1*boolToReal (x 0)+a 2*boolToReal (x 1)+a 3*boolToReal (x 2))/denominator k 0 x +
    (a 4*boolToReal (x 0)+a 5*boolToReal (x 1)+a 6*boolToReal (x 2))/denominator k 1 x

def basisPoint : Fin 7 → Fin 3 → Bool :=
  ![![false,false,true], ![false,true,false], ![false,true,true],
    ![true,false,false], ![true,false,true], ![true,true,false], ![true,true,true]]

def basisValue : Fin 7 → ℝ := ![1, 1, -1, 1, -1, 1, -1]

theorem slopes_pos (k h : Fin 2) (i : Fin 3) : 0 < slopes k h i := by
  fin_cases k <;> fin_cases h <;> fin_cases i <;> norm_num [slopes]

def atom (k h : Fin 2) : FracAtom 3 :=
  FracAtom.ofPositiveAffineRatio 0
    (if h = 0 then ![coefficients k 1, coefficients k 2, coefficients k 3]
      else ![coefficients k 4, coefficients k 5, coefficients k 6])
    1 (slopes k h) (by norm_num) (slopes_pos k h)

/-- Both displayed rational scores use admissible original heads. -/
theorem original_score (k : Fin 2) (x : Fin 3 → Bool) :
    coefficients k 0 + ∑ h, (atom k h).eval x = linearScore k (coefficients k) x := by
  simp [atom, FracAtom.ofPositiveAffineRatio_eval, linearScore,
    denominator, affineValue, Fin.sum_univ_succ]
  ring

/-- Every actual row in the common basis is exactly at its prescribed unit value. -/
theorem basis_values (k : Fin 2) (j : Fin 7) :
    linearScore k (coefficients k) (basisPoint j) = basisValue j := by
  fin_cases k <;> fin_cases j <;>
    norm_num [linearScore, coefficients, basisPoint, basisValue, denominator,
      affineValue, slopes, Fin.sum_univ_succ, boolToReal]

/-- Full Boolean-cube feasibility, including the unselected vertex. -/
theorem full_cube_unit_slack (k : Fin 2) (x : Fin 3 → Bool) :
    1 ≤ |linearScore k (coefficients k) x| := by
  fin_cases k <;> cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    norm_num [linearScore, coefficients, denominator, affineValue, slopes,
      Fin.sum_univ_three, boolToReal, h0, h1, h2]

/-- One coefficient box works for both certificates. -/
theorem coefficient_box (k : Fin 2) (i : Fin 7) : |coefficients k i| ≤ 32 := by
  fin_cases k <;> fin_cases i <;> norm_num [coefficients]

theorem origin_disagreement :
    linearScore 0 (coefficients 0) (fun _ ↦ false) = 3 ∧
    linearScore 1 (coefficients 1) (fun _ ↦ false) = -3 := by
  norm_num [linearScore, coefficients, boolToReal]

/-- Exact row-injectivity certificate for denominator choice 0. -/
theorem basis_0_injective (a : Fin 7 → ℝ)
    (h : ∀ j, linearScore 0 a (basisPoint j) = 0) : a = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  norm_num [linearScore, basisPoint, denominator, affineValue, slopes,
    Fin.sum_univ_succ, boolToReal] at h0 h1 h2 h3 h4 h5 h6
  have ha0 : a 0 = 0 := by
    linear_combination (6 : ℝ) * h0 + (8 : ℝ) * h1 + (-20 : ℝ) * h2 + (6 : ℝ) * h3 + (-16 : ℝ) * h4 + (-18 : ℝ) * h5 + (35 : ℝ) * h6
  have ha1 : a 1 = 0 := by
    linear_combination (12 : ℝ) * h0 + (8 : ℝ) * h1 + (-40 : ℝ) * h2 + (6 : ℝ) * h3 + (-32 : ℝ) * h4 + (-24 : ℝ) * h5 + (70 : ℝ) * h6
  have ha2 : a 2 = 0 := by
    linear_combination (18 : ℝ) * h0 + (68/3 : ℝ) * h1 + (-220/3 : ℝ) * h2 + (6 : ℝ) * h3 + (-44 : ℝ) * h4 + (-46 : ℝ) * h5 + (350/3 : ℝ) * h6
  have ha3 : a 3 = 0 := by
    linear_combination (30 : ℝ) * h0 + (36 : ℝ) * h1 + (-120 : ℝ) * h2 + (18 : ℝ) * h3 + (-84 : ℝ) * h4 + (-90 : ℝ) * h5 + (210 : ℝ) * h6
  have ha4 : a 4 = 0 := by
    linear_combination (-36 : ℝ) * h0 + (-36 : ℝ) * h1 + (120 : ℝ) * h2 + (-24 : ℝ) * h3 + (96 : ℝ) * h4 + (90 : ℝ) * h5 + (-210 : ℝ) * h6
  have ha5 : a 5 = 0 := by
    linear_combination (-60 : ℝ) * h0 + (-220/3 : ℝ) * h1 + (680/3 : ℝ) * h2 + (-36 : ℝ) * h3 + (152 : ℝ) * h4 + (164 : ℝ) * h5 + (-1120/3 : ℝ) * h6
  have ha6 : a 6 = 0 := by
    linear_combination (-30 : ℝ) * h0 + (-40 : ℝ) * h1 + (120 : ℝ) * h2 + (-24 : ℝ) * h3 + (88 : ℝ) * h4 + (96 : ℝ) * h5 + (-210 : ℝ) * h6
  funext i
  fin_cases i
  · exact ha0
  · exact ha1
  · exact ha2
  · exact ha3
  · exact ha4
  · exact ha5
  · exact ha6

/-- Exact row-injectivity certificate for denominator choice 1. -/
theorem basis_1_injective (a : Fin 7 → ℝ)
    (h : ∀ j, linearScore 1 a (basisPoint j) = 0) : a = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  norm_num [linearScore, basisPoint, denominator, affineValue, slopes,
    Fin.sum_univ_succ, boolToReal] at h0 h1 h2 h3 h4 h5 h6
  have ha0 : a 0 = 0 := by
    linear_combination (4 : ℝ) * h0 + (8 : ℝ) * h1 + (-15 : ℝ) * h2 + (8 : ℝ) * h3 + (-15 : ℝ) * h4 + (-21 : ℝ) * h5 + (32 : ℝ) * h6
  have ha1 : a 1 = 0 := by
    linear_combination (6 : ℝ) * h0 + (-15 : ℝ) * h2 + (12 : ℝ) * h3 + (-30 : ℝ) * h4 + (-21 : ℝ) * h5 + (48 : ℝ) * h6
  have ha2 : a 2 = 0 := by
    linear_combination (6 : ℝ) * h0 + (12 : ℝ) * h1 + (-30 : ℝ) * h2 + (-15 : ℝ) * h4 + (-21 : ℝ) * h5 + (48 : ℝ) * h6
  have ha3 : a 3 = 0 := by
    linear_combination (6 : ℝ) * h0 + (12 : ℝ) * h1 + (-30 : ℝ) * h2 + (12 : ℝ) * h3 + (-30 : ℝ) * h4 + (-42 : ℝ) * h5 + (72 : ℝ) * h6
  have ha4 : a 4 = 0 := by
    linear_combination (-28 : ℝ) * h0 + (-32 : ℝ) * h1 + (90 : ℝ) * h2 + (-52 : ℝ) * h3 + (120 : ℝ) * h4 + (126 : ℝ) * h5 + (-224 : ℝ) * h6
  have ha5 : a 5 = 0 := by
    linear_combination (-28 : ℝ) * h0 + (-52 : ℝ) * h1 + (120 : ℝ) * h2 + (-32 : ℝ) * h3 + (90 : ℝ) * h4 + (126 : ℝ) * h5 + (-224 : ℝ) * h6
  have ha6 : a 6 = 0 := by
    linear_combination (-12 : ℝ) * h0 + (-28 : ℝ) * h1 + (60 : ℝ) * h2 + (-28 : ℝ) * h3 + (60 : ℝ) * h4 + (84 : ℝ) * h5 + (-136 : ℝ) * h6
  funext i
  fin_cases i
  · exact ha0
  · exact ha1
  · exact ha2
  · exact ha3
  · exact ha4
  · exact ha5
  · exact ha6

/-- The selected actual rows are a full basis for either normalized feature family. -/
theorem basis_injective (k : Fin 2) (a : Fin 7 → ℝ)
    (h : ∀ j, linearScore k a (basisPoint j) = 0) : a = 0 := by
  fin_cases k
  · exact basis_0_injective a h
  · exact basis_1_injective a h

/-- Both different sign tables are representable in the original width-two model. -/
theorem original_computable (k : Fin 2) :
    fracComputable 3 2 (fun x ↦ decide (0 < linearScore k (coefficients k) x)) := by
  classical
  refine ⟨atom k, coefficients k 0, fun x ↦ ?_⟩
  rw [original_score]
  simp

end HeadComplexity.FeasibleBasisNonuniqueness
