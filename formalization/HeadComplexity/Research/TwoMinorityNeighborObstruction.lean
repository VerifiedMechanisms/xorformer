import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option maxRecDepth 4096

noncomputable section
namespace HeadComplexity.TwoMinorityNeighborObstruction
open scoped BigOperators

def affine (c : Fin 9 → ℝ) (x : Fin 8 → Bool) : ℝ :=
  affineValue (c 0) (fun i => c i.succ) x

def denominator : Fin 2 → Fin 9 → ℝ := ![![1, 2, 12, 1, 4, 1, 1, 1, 1], ![1, 1, 11, 1, 1, 1, 1, 1, 1]]

def numerator : Fin 2 → Fin 9 → ℝ := ![![1, -102, 184, 87, 38, -67, 53, -33, 53], ![1, -79, 151, 71, 31, -59, 41, -29, 41]]

def basisPoint : Fin 9 → Fin 8 → Bool := ![![true, false, true, false, false, true, true, false], ![true, false, false, true, false, true, true, true], ![true, true, false, false, true, false, true, false], ![true, false, true, true, false, false, true, false], ![false, false, false, true, false, false, true, false], ![true, true, false, true, true, false, true, false], ![true, false, true, true, true, false, false, true], ![true, false, true, true, true, true, false, false], ![true, true, false, false, true, false, false, false]]

def basisValue : Fin 9 → ℝ := ![1, 1, -1, -1, 1, 1, 1, 1, 1]

theorem denominator_pos (k : Fin 2) (i : Fin 9) : 0 < denominator k i := by
  fin_cases k <;> fin_cases i <;> norm_num [denominator]

def atom (k : Fin 2) : FracAtom 8 :=
  FracAtom.ofPositiveAffineRatio (numerator k 0) (fun i => numerator k i.succ)
    (denominator k 0) (fun i => denominator k i.succ)
    (denominator_pos k 0) (fun i => denominator_pos k i.succ)

theorem atom_eval (k : Fin 2) (x : Fin 8 → Bool) :
    (atom k).eval x = affine (numerator k) x / affine (denominator k) x := by
  exact FracAtom.ofPositiveAffineRatio_eval _ _ _ _ _ _ x

theorem denominator_value_pos (k : Fin 2) (x : Fin 8 → Bool) :
    0 < affine (denominator k) x :=
  affineValue_pos _ _ (denominator_pos k 0) (fun i => denominator_pos k i.succ) x

set_option maxHeartbeats 8000000 in
-- Exhaust the 256 Boolean rows for each of the two exact integer witnesses.
theorem full_cube_gap (k : Fin 2) (x : Fin 8 → Bool) :
    affine (denominator k) x ≤ |affine (numerator k) x| := by
  have hv : x = ![x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7] := by
    ext i; fin_cases i <;> rfl
  rw [hv]
  generalize x 0 = z0, x 1 = z1, x 2 = z2, x 3 = z3,
    x 4 = z4, x 5 = z5, x 6 = z6, x 7 = z7
  fin_cases k <;> cases z0 <;> cases z1 <;> cases z2 <;> cases z3 <;>
    cases z4 <;> cases z5 <;> cases z6 <;> cases z7 <;>
    norm_num [affine, affineValue, denominator, numerator, Fin.sum_univ_succ, boolToReal]

theorem unit_basis_values (k : Fin 2) (j : Fin 9) :
    (atom k).eval (basisPoint j) = basisValue j := by
  rw [atom_eval]
  fin_cases k <;> fin_cases j <;>
    norm_num [affine, affineValue, denominator, numerator, basisPoint, basisValue,
      Fin.sum_univ_succ, boolToReal]

theorem exactly_two_negative_contacts (j : Fin 9) :
    basisValue j = -1 ↔ j = 2 ∨ j = 3 := by
  fin_cases j <;> norm_num [basisValue]

theorem basis_affine_injective (c d : Fin 9 → ℝ)
    (h : ∀ j, affine c (basisPoint j) = affine d (basisPoint j)) : c = d := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  have h8 := h 8
  norm_num [affine, affineValue, basisPoint, Fin.sum_univ_succ, boolToReal] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  ext i
  fin_cases i <;> norm_num only [Fin.mk_zero, Fin.reduceFinMk]
  · linear_combination (1) * h4 + (-1) * h5 + (1) * h8
  · linear_combination (-2) * h0 + (1) * h1 + (2) * h2 + (2) * h3 + (-1) * h4 + (-2) * h5 + (-1) * h6 + (1) * h7
  · linear_combination (3) * h0 + (-1) * h1 + (-4) * h2 + (-2) * h3 + (4) * h5 + (1) * h6 + (-2) * h7 + (1) * h8
  · linear_combination (2) * h0 + (-1) * h1 + (-2) * h2 + (-1) * h3 + (2) * h5 + (1) * h6 + (-1) * h7
  · linear_combination (-1) * h2 + (1) * h5
  · linear_combination (-1) * h0 + (2) * h2 + (-1) * h5 + (1) * h7 + (-1) * h8
  · linear_combination (1) * h0 + (-1) * h2 + (-1) * h3 + (1) * h5
  · linear_combination (1) * h2 + (-1) * h8
  · linear_combination (1) * h0 + (-1) * h2 + (-1) * h3 + (1) * h5 + (1) * h6 + (-1) * h7

def ratio (k : Fin 2) : ℝ :=
  affine (denominator k) (basisPoint 2) / affine (denominator k) (basisPoint 3)

def comparison (k : Fin 2) (i : Fin 9) : ℝ :=
  (denominator k i - numerator k i) / (2 * affine (denominator k) (basisPoint 3))

def signValue (t : ℝ) : ℝ := if 0 < t then 1 else if t = 0 then 0 else -1

theorem ratios : ratio 0 = 17 / 9 ∧ ratio 1 = 3 := by
  norm_num [ratio, affine, affineValue, denominator, basisPoint, Fin.sum_univ_succ, boolToReal]

/-- Even the affine constant coefficient has the same three comparison signs. -/
theorem same_all_coefficient_comparisons (i : Fin 9) :
    signValue (comparison 0 i) = signValue (comparison 1 i) ∧
    signValue (comparison 0 i + ratio 0) = signValue (comparison 1 i + ratio 1) ∧
    signValue (comparison 0 i + 1) = signValue (comparison 1 i + 1) := by
  fin_cases i <;>
    norm_num [signValue, comparison, ratio, affine, affineValue, denominator, numerator,
      basisPoint, Fin.sum_univ_succ, boolToReal]

/-- The downward-neighbor thresholds agree as well. -/
theorem same_positive_level_comparisons (i : Fin 9) :
    signValue (comparison 0 i - ratio 0) = signValue (comparison 1 i - ratio 1) ∧
    signValue (comparison 0 i - 1) = signValue (comparison 1 i - 1) := by
  fin_cases i <;>
    norm_num [signValue, comparison, ratio, affine, affineValue, denominator, numerator,
      basisPoint, Fin.sum_univ_succ, boolToReal]

def testPoint : Fin 8 → Bool := ![false,false,false,false,true,true,true,true]

theorem different_labels : 0 < (atom 0).eval testPoint ∧ (atom 1).eval testPoint < 0 := by
  rw [atom_eval, atom_eval]
  norm_num [testPoint, affine, affineValue, denominator, numerator, Fin.sum_univ_succ, boolToReal]

end HeadComplexity.TwoMinorityNeighborObstruction
