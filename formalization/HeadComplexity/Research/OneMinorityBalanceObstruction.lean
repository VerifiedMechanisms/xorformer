import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option maxRecDepth 8192

/-! A one-minority-contact unit basis with optimal denominator constant 1/22.
This is a fixed-basis obstruction, not a truth-table margin obstruction. -/
noncomputable section
namespace HeadComplexity.OneMinorityBalanceObstruction
open scoped BigOperators

def affine (c : Fin 11 → ℝ) (x : Fin 10 → Bool) : ℝ :=
  affineValue (c 0) (fun i => c i.succ) x

def flatCoeffs : Fin 11 → ℝ := ![-5, -15, -2, -9, 6, 12, -14, -20, 10, 31, 12]

def q : Fin 10 → Bool := ![true, true, true, true, false, true, false, true, true, false]

def basisPoint : Fin 11 → Fin 10 → Bool := ![![false, false, true, false, true, false, true, true, false, true], ![false, false, true, true, false, true, false, true, false, true], ![false, false, true, true, true, true, false, true, false, false], ![false, true, false, false, false, true, true, true, true, false], ![false, true, true, true, false, false, false, true, false, false], ![false, true, true, true, true, true, false, false, false, true], ![true, false, false, false, true, true, false, true, false, true], ![true, false, false, true, true, false, true, true, false, true], ![true, false, true, false, false, true, false, false, true, true], ![true, true, true, false, true, true, true, true, true, true], ![true, true, true, true, false, true, false, true, true, false]]

def basisValue : Fin 11 → ℝ := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1]

def baseDenominator : Fin 11 → ℝ := ![1, 11, 8, 17, 6, 1, 7, 1, 20, 4, 1]

def boundaryDenominator : Fin 11 → ℝ := ![1, 3, 2, 5, 2, 0, 2, 0, 6, 1, 0]

def numerator (b : Fin 11 → ℝ) : Fin 11 → ℝ :=
  fun i => b i - affine b q * flatCoeffs i

def label (x : Fin 10 → Bool) : ℝ :=
  if 0 < affine flatCoeffs x then -1 else 1

theorem baseDenominator_pos (i : Fin 11) : 0 < baseDenominator i := by
  fin_cases i <;> norm_num [baseDenominator]

theorem numerator_eval (b : Fin 11 → ℝ) (x : Fin 10 → Bool) :
    affine (numerator b) x = affine b x - affine b q * affine flatCoeffs x := by
  simp only [affine, affineValue, numerator, Fin.sum_univ_succ]
  ring

theorem basis_identity (b : Fin 11 → ℝ) (j : Fin 11) :
    affine (numerator b) (basisPoint j) =
      basisValue j * affine b (basisPoint j) := by
  rw [numerator_eval]
  fin_cases j <;> norm_num [affine, affineValue, flatCoeffs, basisPoint,
    basisValue, q, Fin.sum_univ_succ, boolToReal] ; ring

set_option maxHeartbeats 8000000 in
-- Exhausting all 1024 Boolean rows requires additional elaboration heartbeats.
theorem base_full_gap (x : Fin 10 → Bool) :
    affine baseDenominator x ≤ label x * affine (numerator baseDenominator) x := by
  rw [numerator_eval]
  have hv : x = ![x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  generalize x 0 = b0, x 1 = b1, x 2 = b2, x 3 = b3, x 4 = b4,
    x 5 = b5, x 6 = b6, x 7 = b7, x 8 = b8, x 9 = b9
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    cases b5 <;> cases b6 <;> cases b7 <;> cases b8 <;> cases b9 <;>
    norm_num [label, affine, affineValue, flatCoeffs, baseDenominator, q,
      Fin.sum_univ_succ, boolToReal]

set_option maxHeartbeats 8000000 in
-- Exhausting all 1024 Boolean rows requires additional elaboration heartbeats.
theorem boundary_full_gap (x : Fin 10 → Bool) :
    affine boundaryDenominator x ≤ label x * affine (numerator boundaryDenominator) x := by
  rw [numerator_eval]
  have hv : x = ![x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  generalize x 0 = b0, x 1 = b1, x 2 = b2, x 3 = b3, x 4 = b4,
    x 5 = b5, x 6 = b6, x 7 = b7, x 8 = b8, x 9 = b9
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    cases b5 <;> cases b6 <;> cases b7 <;> cases b8 <;> cases b9 <;>
    norm_num [label, affine, affineValue, flatCoeffs, boundaryDenominator, q,
      Fin.sum_univ_succ, boolToReal]

theorem basis_affine_injective (c d : Fin 11 → ℝ)
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
  have h9 := h 9
  have h10 := h 10
  norm_num [affine, affineValue, basisPoint, Fin.sum_univ_succ, boolToReal] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  ext i
  fin_cases i <;> norm_num only [Fin.mk_zero, Fin.reduceFinMk]
  · linear_combination (-3/2) * h0 + (-1/2) * h1 + (1) * h2 + (1/2) * h3 + (2) * h4 + (-1/2) * h5 + (1/2) * h7 + (3/2) * h8 + (1/2) * h9 + (-5/2) * h10
  · linear_combination (-13/2) * h0 + (1/2) * h1 + (3) * h2 + (-1/2) * h3 + (5) * h4 + (-5/2) * h5 + (-1) * h6 + (3/2) * h7 + (5/2) * h8 + (11/2) * h9 + (-15/2) * h10
  · linear_combination (-1) * h0 + (1) * h4 + (1) * h9 + (-1) * h10
  · linear_combination (-7/2) * h0 + (1/2) * h1 + (2) * h2 + (-1/2) * h3 + (3) * h4 + (-3/2) * h5 + (-1) * h6 + (1/2) * h7 + (3/2) * h8 + (7/2) * h9 + (-9/2) * h10
  · linear_combination (2) * h0 + (-1) * h2 + (-2) * h4 + (1) * h5 + (-1) * h8 + (-2) * h9 + (3) * h10
  · linear_combination (5) * h0 + (-1) * h1 + (-2) * h2 + (-4) * h4 + (2) * h5 + (1) * h6 + (-1) * h7 + (-2) * h8 + (-4) * h9 + (6) * h10
  · linear_combination (-6) * h0 + (1) * h1 + (3) * h2 + (4) * h4 + (-2) * h5 + (-1) * h6 + (1) * h7 + (2) * h8 + (5) * h9 + (-7) * h10
  · linear_combination (-8) * h0 + (1) * h1 + (4) * h2 + (6) * h4 + (-3) * h5 + (-2) * h6 + (2) * h7 + (3) * h8 + (7) * h9 + (-10) * h10
  · linear_combination (4) * h0 + (-2) * h2 + (-3) * h4 + (1) * h5 + (1) * h6 + (-1) * h7 + (-2) * h8 + (-3) * h9 + (5) * h10
  · linear_combination (25/2) * h0 + (-3/2) * h1 + (-6) * h2 + (1/2) * h3 + (-10) * h4 + (9/2) * h5 + (2) * h6 + (-5/2) * h7 + (-9/2) * h8 + (-21/2) * h9 + (31/2) * h10
  · linear_combination (5) * h0 + (-3) * h2 + (-4) * h4 + (2) * h5 + (1) * h6 + (-1) * h7 + (-2) * h8 + (-4) * h9 + (6) * h10

theorem numerator_forced (a b : Fin 11 → ℝ)
    (h : ∀ j, affine a (basisPoint j) =
      basisValue j * affine b (basisPoint j)) : a = numerator b := by
  exact basis_affine_injective _ _ (fun j => (h j).trans (basis_identity b j).symm)

theorem balance_bound (b : Fin 11 → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hgap : ∀ x, affine b x ≤ label x * affine (numerator b) x) :
    22 * b 0 ≤ ∑ i, b i := by
  have h0 := hgap (![false, false, false, true, true, true, true, true, false, true])
  have h1 := hgap (![false, true, false, false, true, true, false, true, false, false])
  have h2 := hgap (![false, true, false, true, true, false, true, true, false, false])
  have h3 := hgap (![false, true, true, false, false, true, false, false, true, false])
  have h4 := hgap (![true, false, false, false, false, false, true, true, true, false])
  have h5 := hgap (![true, false, true, true, true, false, false, false, false, true])
  have h6 := hgap (![true, true, false, true, false, true, false, false, true, false])
  simp only [numerator_eval] at h0 h1 h2 h3 h4 h5 h6
  norm_num [label, affine, affineValue, flatCoeffs, q, Fin.sum_univ_succ, boolToReal] at h0 h1 h2 h3 h4 h5 h6
  norm_num [Fin.sum_univ_succ]
  linear_combination (2) * h0 + (2) * h1 + (2) * h2 + (5) * h3 + (4) * h4 + (5) * h5 + (1) * h6 + 23 * hb 5 + 17 * hb 7 + 15 * hb 10

theorem all_basis_representatives_balance_bound (a b : Fin 11 → ℝ)
    (hb : ∀ i, 0 ≤ b i)
    (hcontacts : ∀ j, affine a (basisPoint j) =
      basisValue j * affine b (basisPoint j))
    (hgap : ∀ x, affine b x ≤ label x * affine a x) :
    22 * b 0 ≤ ∑ i, b i := by
  rw [numerator_forced a b hcontacts] at hgap
  exact balance_bound b hb hgap

theorem boundary_attains_bound :
    22 * boundaryDenominator 0 = ∑ i, boundaryDenominator i := by
  norm_num [boundaryDenominator, Fin.sum_univ_succ]

def atom : FracAtom 10 :=
  FracAtom.ofPositiveAffineRatio ((numerator baseDenominator) 0)
    (fun i => (numerator baseDenominator) i.succ)
    (baseDenominator 0) (fun i => baseDenominator i.succ)
    (baseDenominator_pos 0) (fun i => baseDenominator_pos i.succ)

theorem atom_eval (x : Fin 10 → Bool) :
    atom.eval x = affine (numerator baseDenominator) x / affine baseDenominator x := by
  exact FracAtom.ofPositiveAffineRatio_eval _ _ _ _ _ _ x

theorem atom_full_unit_gap (x : Fin 10 → Bool) : 1 ≤ label x * atom.eval x := by
  rw [atom_eval, ← mul_div_assoc]
  have hd := affineValue_pos (baseDenominator 0) (fun i => baseDenominator i.succ)
    (baseDenominator_pos 0) (fun i => baseDenominator_pos i.succ) x
  change 0 < affine baseDenominator x at hd
  rw [le_div_iff₀ hd, one_mul]
  exact base_full_gap x

theorem atom_basis_values (j : Fin 11) : atom.eval (basisPoint j) = basisValue j := by
  rw [atom_eval, basis_identity]
  have hd := affineValue_pos (baseDenominator 0) (fun i => baseDenominator i.succ)
    (baseDenominator_pos 0) (fun i => baseDenominator_pos i.succ) (basisPoint j)
  exact mul_div_cancel_right₀ _ hd.ne'

end HeadComplexity.OneMinorityBalanceObstruction
