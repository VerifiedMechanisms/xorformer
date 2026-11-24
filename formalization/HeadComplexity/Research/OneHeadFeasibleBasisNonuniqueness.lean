import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option maxRecDepth 2048

/-!
A full-cube feasible, actual-unit-row basis does not determine the truth table,
already for one admissible original head in dimension six. Both examples have
the same numerator slope signs. No low-margin or capacity conclusion follows.
-/

noncomputable section
namespace HeadComplexity.OneHeadFeasibleBasisNonuniqueness
open scoped BigOperators

def slopes : Fin 2 → Fin 6 → ℝ := ![![1, 2, 1, 1, 1, 1], ![1, 4, 1, 1, 1, 1]]

def numeratorCoefficients : Fin 2 → Fin 7 → ℝ := ![![11, -9, -18, -9, -9, -9, 11], ![15, -13, -28, -13, -17, -13, 19]]

def coefficients : Fin 2 → Fin 7 → ℝ := ![![11, -20, -40, -20, -20, -20, 0], ![15, -28, -88, -28, -32, -28, 4]]

def denominator (k : Fin 2) (x : Fin 6 → Bool) : ℝ :=
  affineValue 1 (slopes k) x

def linearScore (k : Fin 2) (a : Fin 7 → ℝ) (x : Fin 6 → Bool) : ℝ :=
  a 0 + (a 1*boolToReal (x 0)+a 2*boolToReal (x 1)+a 3*boolToReal (x 2)+
    a 4*boolToReal (x 3)+a 5*boolToReal (x 4)+a 6*boolToReal (x 5))/denominator k x

def basisPoint : Fin 7 → Fin 6 → Bool :=
  ![![false, false, false, true, true, true], ![false, false, true, false, false, false], ![false, false, true, true, false, true], ![false, true, false, false, false, true], ![false, true, false, false, true, true], ![true, false, false, false, false, false], ![true, false, true, false, true, true]]

def basisValue : Fin 7 → ℝ := ![1, 1, 1, 1, -1, 1, -1]

theorem slopes_pos (k : Fin 2) (i : Fin 6) : 0 < slopes k i := by
  fin_cases k <;> fin_cases i <;> norm_num [slopes]

def atom (k : Fin 2) : FracAtom 6 :=
  FracAtom.ofPositiveAffineRatio 0
    ![coefficients k 1, coefficients k 2, coefficients k 3,
      coefficients k 4, coefficients k 5, coefficients k 6]
    1 (slopes k) (by norm_num) (slopes_pos k)

/-- Both normalized scores use one admissible head and the original free bias. -/
theorem original_score (k : Fin 2) (x : Fin 6 → Bool) :
    coefficients k 0 + (atom k).eval x = linearScore k (coefficients k) x := by
  simp [atom, FracAtom.ofPositiveAffineRatio_eval, linearScore,
    denominator, affineValue, Fin.sum_univ_succ]
  ring

/-- The raw affine numerators displayed in the counterexample are exact. -/
theorem score_ratio (k : Fin 2) (x : Fin 6 → Bool) :
    linearScore k (coefficients k) x =
      affineValue (numeratorCoefficients k 0)
        (fun i ↦ numeratorCoefficients k i.succ) x / denominator k x := by
  have hd : denominator k x ≠ 0 :=
    (affineValue_pos 1 (slopes k) (by norm_num) (slopes_pos k) x).ne'
  apply (eq_div_iff hd).mpr
  unfold linearScore
  field_simp [hd]
  fin_cases k <;>
    norm_num [denominator, affineValue, slopes, coefficients, numeratorCoefficients,
      Fin.sum_univ_succ] <;> ring

/-- Seven actual sample rows, with the same prescribed unit values. -/
theorem basis_values (k : Fin 2) (j : Fin 7) :
    linearScore k (coefficients k) (basisPoint j) = basisValue j := by
  fin_cases k <;> fin_cases j <;>
    norm_num [linearScore, coefficients, basisPoint, basisValue, denominator,
      affineValue, slopes, Fin.sum_univ_succ, boolToReal]

/-- Every one of the 64 vertices has absolute score at least one. -/
theorem full_cube_unit_slack (k : Fin 2) (x : Fin 6 → Bool) :
    1 ≤ |linearScore k (coefficients k) x| := by
  have hvec : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    ext i
    fin_cases i <;> rfl
  rw [hvec]
  generalize x 0 = b0, x 1 = b1, x 2 = b2, x 3 = b3, x 4 = b4, x 5 = b5
  fin_cases k <;> cases b0 <;> cases b1 <;> cases b2 <;>
    cases b3 <;> cases b4 <;> cases b5 <;>
    norm_num [linearScore, coefficients, denominator, affineValue, slopes,
      Fin.sum_univ_succ, boolToReal]

/-- A common bounded coefficient box contains both feasible certificates. -/
theorem coefficient_box (k : Fin 2) (i : Fin 7) : |coefficients k i| ≤ 88 := by
  fin_cases k <;> fin_cases i <;> norm_num [coefficients]

/-- The two labels differ at the fourth-coordinate singleton. -/
theorem singleton_disagreement :
    linearScore 0 (coefficients 0) ![false,false,false,true,false,false] = 1 ∧
    linearScore 1 (coefficients 1) ![false,false,false,true,false,false] = -1 := by
  norm_num [linearScore, coefficients, denominator, affineValue, slopes,
    Fin.sum_univ_succ, boolToReal]

/-- Even the signs of all raw affine numerator slopes agree. -/
theorem numerator_slope_signs (k : Fin 2) (i : Fin 6) :
    (0 < numeratorCoefficients k i.succ) ↔ i = 5 := by
  fin_cases k <;> fin_cases i <;> norm_num [numeratorCoefficients]

/-- Exact basis certificate for denominator choice 0. -/
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
    linear_combination (4 : ℝ) * h0 + (2 : ℝ) * h1 + (-4 : ℝ) * h2 + (4 : ℝ) * h3 + (-5 : ℝ) * h4
  have ha1 : a 1 = 0 := by
    linear_combination (-8 : ℝ) * h0 + (-4 : ℝ) * h1 + (8 : ℝ) * h2 + (-8 : ℝ) * h3 + (10 : ℝ) * h4 + (2 : ℝ) * h5
  have ha2 : a 2 = 0 := by
    linear_combination (-16 : ℝ) * h0 + (-6 : ℝ) * h1 + (16 : ℝ) * h2 + (-16 : ℝ) * h3 + (25 : ℝ) * h4 + (2 : ℝ) * h5 + (-5 : ℝ) * h6
  have ha3 : a 3 = 0 := by
    linear_combination (-8 : ℝ) * h0 + (-2 : ℝ) * h1 + (8 : ℝ) * h2 + (-8 : ℝ) * h3 + (10 : ℝ) * h4
  have ha4 : a 4 = 0 := by
    linear_combination (-8 : ℝ) * h0 + (-4 : ℝ) * h1 + (12 : ℝ) * h2 + (-12 : ℝ) * h3 + (15 : ℝ) * h4 + (2 : ℝ) * h5 + (-5 : ℝ) * h6
  have ha5 : a 5 = 0 := by
    linear_combination (-4 : ℝ) * h0 + (-2 : ℝ) * h1 + (4 : ℝ) * h2 + (-8 : ℝ) * h3 + (10 : ℝ) * h4
  have ha6 : a 6 = 0 := by
    linear_combination (-2 : ℝ) * h1 + (4 : ℝ) * h3 + (-5 : ℝ) * h4 + (-2 : ℝ) * h5 + (5 : ℝ) * h6
  funext i
  fin_cases i
  · exact ha0
  · exact ha1
  · exact ha2
  · exact ha3
  · exact ha4
  · exact ha5
  · exact ha6

/-- Exact basis certificate for denominator choice 1. -/
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
    linear_combination (4 : ℝ) * h0 + (2 : ℝ) * h1 + (-4 : ℝ) * h2 + (6 : ℝ) * h3 + (-7 : ℝ) * h4
  have ha1 : a 1 = 0 := by
    linear_combination (-8 : ℝ) * h0 + (-4 : ℝ) * h1 + (8 : ℝ) * h2 + (-12 : ℝ) * h3 + (14 : ℝ) * h4 + (2 : ℝ) * h5
  have ha2 : a 2 = 0 := by
    linear_combination (-24 : ℝ) * h0 + (-10 : ℝ) * h1 + (24 : ℝ) * h2 + (-36 : ℝ) * h3 + (49 : ℝ) * h4 + (2 : ℝ) * h5 + (-5 : ℝ) * h6
  have ha3 : a 3 = 0 := by
    linear_combination (-8 : ℝ) * h0 + (-2 : ℝ) * h1 + (8 : ℝ) * h2 + (-12 : ℝ) * h3 + (14 : ℝ) * h4
  have ha4 : a 4 = 0 := by
    linear_combination (-8 : ℝ) * h0 + (-4 : ℝ) * h1 + (12 : ℝ) * h2 + (-18 : ℝ) * h3 + (21 : ℝ) * h4 + (2 : ℝ) * h5 + (-5 : ℝ) * h6
  have ha5 : a 5 = 0 := by
    linear_combination (-4 : ℝ) * h0 + (-2 : ℝ) * h1 + (4 : ℝ) * h2 + (-12 : ℝ) * h3 + (14 : ℝ) * h4
  have ha6 : a 6 = 0 := by
    linear_combination (-2 : ℝ) * h1 + (6 : ℝ) * h3 + (-7 : ℝ) * h4 + (-2 : ℝ) * h5 + (5 : ℝ) * h6
  funext i
  fin_cases i
  · exact ha0
  · exact ha1
  · exact ha2
  · exact ha3
  · exact ha4
  · exact ha5
  · exact ha6

theorem basis_injective (k : Fin 2) (a : Fin 7 → ℝ)
    (h : ∀ j, linearScore k a (basisPoint j) = 0) : a = 0 := by
  fin_cases k
  · exact basis_0_injective a h
  · exact basis_1_injective a h

/-- Both disagreeing tables are computed in the original width-one model. -/
theorem original_computable (k : Fin 2) :
    fracComputable 6 1 (fun x ↦ decide (0 < linearScore k (coefficients k) x)) := by
  classical
  refine ⟨fun _ ↦ atom k, coefficients k 0, fun x ↦ ?_⟩
  simp only [Fin.sum_univ_one]
  rw [original_score]
  simp

end HeadComplexity.OneHeadFeasibleBasisNonuniqueness
