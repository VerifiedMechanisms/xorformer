import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option maxRecDepth 8192

/-! A fully feasible actual affine-basis branch whose normalized denominator
constant is at most one eighth. This is not an obstruction to inverse-polynomial
balance or to choosing a different representation of the same truth table. -/

noncomputable section
namespace HeadComplexity.FixedBasisBalanceObstruction
open scoped BigOperators

def affine (c : Fin 11 → ℝ) (x : Fin 10 → Bool) : ℝ :=
  affineValue (c 0) (fun i => c i.succ) x

def basisPoint : Fin 11 → Fin 10 → Bool := ![![false, false, false, false, false, false, true, false, false, false], ![false, false, false, false, true, true, true, true, false, false], ![false, false, false, false, true, true, true, true, true, false], ![false, false, false, true, false, true, false, true, false, false], ![false, true, false, false, false, true, false, false, true, true], ![false, true, true, true, true, false, true, true, false, false], ![false, true, true, true, true, false, true, true, true, true], ![true, false, false, false, false, false, false, true, true, true], ![true, false, false, false, true, false, false, false, false, true], ![true, false, false, true, false, false, false, false, true, false], ![true, true, false, false, false, true, true, false, false, true]]

def basisValue : Fin 11 → ℝ := ![1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1]

def baseNumerator : Fin 11 → ℝ := ![119, 139, -389, 1048, -273, -165, 343, -117, -185, 11, -89]

def baseDenominator : Fin 11 → ℝ := ![1, 1, 1, 32, 1, 1, 1, 1, 1, 1, 1]

def testPoint : Fin 10 → Bool := ![false, false, false, true, false, true, true, false, true, true]

theorem baseDenominator_pos (i : Fin 11) : 0 < baseDenominator i := by
  fin_cases i <;> norm_num [baseDenominator]

theorem basis_identity (j : Fin 11) :
    affine baseNumerator (basisPoint j) = basisValue j * affine baseDenominator (basisPoint j) := by
  fin_cases j <;> norm_num [affine, affineValue, basisPoint, basisValue,
    baseNumerator, baseDenominator, Fin.sum_univ_succ, boolToReal]

set_option maxHeartbeats 8000000 in
-- Exhaust all 1024 Boolean rows with kernel-checked integer inequalities.
theorem base_full_gap (x : Fin 10 → Bool) :
    affine baseDenominator x ≤ |affine baseNumerator x| := by
  have hv : x = ![x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  generalize x 0 = b0, x 1 = b1, x 2 = b2, x 3 = b3, x 4 = b4,
    x 5 = b5, x 6 = b6, x 7 = b7, x 8 = b8, x 9 = b9
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    cases b5 <;> cases b6 <;> cases b7 <;> cases b8 <;> cases b9 <;>
    norm_num [affine, affineValue, baseNumerator, baseDenominator,
      Fin.sum_univ_succ, boolToReal]

theorem base_test_negative : affine baseNumerator testPoint < 0 := by
  norm_num [affine, affineValue, baseNumerator, testPoint, Fin.sum_univ_succ, boolToReal]

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
  · linear_combination (1) * h0 + (-3) * h1 + (2) * h2 + (1) * h3 + (1) * h5 + (-1) * h6 + (1) * h8 + (-1) * h9
  · linear_combination (-4) * h1 + (3) * h2 + (1) * h3 + (-1) * h4 + (1) * h5 + (-1) * h6 + (1) * h8 + (-1) * h9 + (1) * h10
  · linear_combination (-2) * h0 + (15) * h1 + (-11) * h2 + (-5) * h3 + (3) * h4 + (-2) * h5 + (2) * h6 + (1) * h7 + (-4) * h8 + (5) * h9 + (-2) * h10
  · linear_combination (4) * h0 + (-36) * h1 + (26) * h2 + (11) * h3 + (-6) * h4 + (7) * h5 + (-6) * h6 + (-2) * h7 + (9) * h8 + (-12) * h9 + (5) * h10
  · linear_combination (-1) * h0 + (8) * h1 + (-6) * h2 + (-2) * h3 + (1) * h4 + (-2) * h5 + (2) * h6 + (-2) * h8 + (3) * h9 + (-1) * h10
  · linear_combination (-1) * h0 + (6) * h1 + (-4) * h2 + (-2) * h3 + (1) * h4 + (-1) * h5 + (1) * h6 + (-1) * h8 + (2) * h9 + (-1) * h10
  · linear_combination (1) * h0 + (-12) * h1 + (9) * h2 + (4) * h3 + (-2) * h4 + (2) * h5 + (-2) * h6 + (-1) * h7 + (3) * h8 + (-4) * h9 + (2) * h10
  · linear_combination (3) * h1 + (-2) * h2 + (-1) * h3 + (-1) * h5 + (1) * h6 + (-1) * h8 + (1) * h9
  · linear_combination (-1) * h0 + (7) * h1 + (-5) * h2 + (-2) * h3 + (1) * h4 + (-1) * h5 + (1) * h6 + (1) * h7 + (-2) * h8 + (2) * h9 + (-1) * h10
  · linear_combination (-1) * h1 + (1) * h2
  · linear_combination (1) * h1 + (-1) * h2 + (-1) * h5 + (1) * h6

/-- Any nonnegative denominator in the same signed actual-basis chart and with
the same label at one additional cube vertex has constant mass at most 1/8. -/
theorem constant_mass_le_eighth (a b : Fin 11 → ℝ)
    (hb : ∀ i, 0 ≤ b i)
    (h : ∀ j, affine a (basisPoint j) = basisValue j * affine b (basisPoint j))
    (hgap : affine b testPoint ≤ -affine a testPoint) :
    8 * b 0 ≤ ∑ i, b i := by
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
  have hb0 := hb 0
  have hb1 := hb 1
  have hb2 := hb 2
  have hb3 := hb 3
  have hb4 := hb 4
  have hb5 := hb 5
  have hb6 := hb 6
  have hb7 := hb 7
  have hb8 := hb 8
  have hb9 := hb 9
  have hb10 := hb 10
  norm_num [affine, affineValue, basisPoint, basisValue, testPoint, Fin.sum_univ_succ, boolToReal] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hgap ⊢
  linarith

def atom : FracAtom 10 :=
  FracAtom.ofPositiveAffineRatio (baseNumerator 0) (fun i => baseNumerator i.succ)
    (baseDenominator 0) (fun i => baseDenominator i.succ)
    (baseDenominator_pos 0) (fun i => baseDenominator_pos i.succ)

theorem atom_eval (x : Fin 10 → Bool) :
    atom.eval x = affine baseNumerator x / affine baseDenominator x := by
  exact FracAtom.ofPositiveAffineRatio_eval _ _ _ _ _ _ x

theorem atom_full_gap (x : Fin 10 → Bool) : 1 ≤ |atom.eval x| := by
  rw [atom_eval, abs_div]
  have hd := affineValue_pos (baseDenominator 0) (fun i => baseDenominator i.succ)
    (baseDenominator_pos 0) (fun i => baseDenominator_pos i.succ) x
  change 0 < affine baseDenominator x at hd
  rw [abs_of_pos hd, le_div_iff₀ hd, one_mul]
  exact base_full_gap x

theorem atom_basis_values (j : Fin 11) : atom.eval (basisPoint j) = basisValue j := by
  rw [atom_eval, basis_identity]
  have hd := affineValue_pos (baseDenominator 0) (fun i => baseDenominator i.succ)
    (baseDenominator_pos 0) (fun i => baseDenominator_pos i.succ) (basisPoint j)
  exact mul_div_cancel_right₀ _ hd.ne'

end HeadComplexity.FixedBasisBalanceObstruction
