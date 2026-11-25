import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option maxRecDepth 8192

/-! A full-cube positive-denominator actual unit-basis branch whose closed
coefficient cone contains no coordinate ray. Polynomial constant balancing
remains open. -/

noncomputable section
namespace HeadComplexity.FeasibleConeNoCoordinateRay
open scoped BigOperators

def affine (c : Fin 11 → ℝ) (x : Fin 10 → Bool) : ℝ :=
  affineValue (c 0) (fun i => c i.succ) x

def basisPoint : Fin 11 → Fin 10 → Bool := ![![false, false, false, true, false, false, false, false, true, true], ![false, false, true, false, false, true, false, true, true, false], ![false, false, true, true, false, false, false, true, false, false], ![false, true, false, false, false, false, false, false, false, false], ![false, true, false, false, false, true, true, true, false, false], ![false, true, false, true, true, false, false, true, true, false], ![true, false, false, false, false, false, false, true, true, true], ![true, false, false, false, true, false, true, false, true, false], ![true, false, false, false, true, true, true, false, false, false], ![true, false, true, true, false, false, false, true, false, false], ![true, true, false, true, true, true, false, true, true, false]]

def basisValue : Fin 11 → ℝ := ![-1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1]

def baseNumerator : Fin 11 → ℝ := ![1286, -44, -1282, -1944, 304, -864, 110, -508, 375, 150, -1748]

def baseDenominator : Fin 11 → ℝ := ![2, 2, 2, 6, 2, 12, 2, 2, 11, 2, 2]

theorem baseDenominator_pos (i : Fin 11) : 0 < baseDenominator i := by
  fin_cases i <;> norm_num [baseDenominator]

theorem basis_identity (j : Fin 11) :
    affine baseNumerator (basisPoint j) = basisValue j * affine baseDenominator (basisPoint j) := by
  fin_cases j <;> norm_num [affine, affineValue, basisPoint, basisValue,
    baseNumerator, baseDenominator, Fin.sum_univ_succ, boolToReal]

set_option maxHeartbeats 8000000 in
-- Exhausting all 1024 Boolean rows needs more elaboration heartbeats.
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
  · linear_combination (-2) * h0 + (-3) * h1 + (13) * h2 + (2) * h3 + (-1) * h4 + (-8) * h5 + (2) * h6 + (4) * h7 + (-3) * h8 + (-10) * h9 + (7) * h10
  · linear_combination (-1) * h2 + (1) * h9
  · linear_combination (2) * h0 + (3) * h1 + (-13) * h2 + (-1) * h3 + (1) * h4 + (8) * h5 + (-2) * h6 + (-4) * h7 + (3) * h8 + (10) * h9 + (-7) * h10
  · linear_combination (3) * h0 + (5) * h1 + (-19) * h2 + (-2) * h3 + (1) * h4 + (12) * h5 + (-3) * h6 + (-6) * h7 + (5) * h8 + (15) * h9 + (-11) * h10
  · linear_combination (-1) * h1 + (3) * h2 + (-2) * h5 + (1) * h7 + (-1) * h8 + (-2) * h9 + (2) * h10
  · linear_combination (1) * h0 + (2) * h1 + (-8) * h2 + (-1) * h3 + (6) * h5 + (-1) * h6 + (-3) * h7 + (3) * h8 + (6) * h9 + (-5) * h10
  · linear_combination (1) * h2 + (-1) * h5 + (-1) * h9 + (1) * h10
  · linear_combination (1) * h0 + (1) * h1 + (-5) * h2 + (-1) * h3 + (1) * h4 + (3) * h5 + (-1) * h6 + (-1) * h7 + (1) * h8 + (4) * h9 + (-3) * h10
  · linear_combination (-1) * h0 + (-1) * h1 + (4) * h2 + (-2) * h5 + (1) * h6 + (1) * h7 + (-1) * h8 + (-3) * h9 + (2) * h10
  · linear_combination (1) * h2 + (-1) * h5 + (1) * h7 + (-1) * h8 + (-1) * h9 + (1) * h10
  · linear_combination (3) * h0 + (4) * h1 + (-17) * h2 + (-2) * h3 + (1) * h4 + (11) * h5 + (-2) * h6 + (-6) * h7 + (5) * h8 + (13) * h9 + (-10) * h10

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


def rayNumerator : Fin 11 → Fin 11 → ℝ := ![![55, -2, -54, -82, 12, -36, 4, -22, 16, 6, -74], ![26, -1, -26, -40, 6, -18, 2, -10, 8, 4, -36], ![18, 0, -17, -26, 4, -12, 2, -8, 4, 2, -24], ![26, -2, -26, -39, 6, -16, 2, -10, 8, 2, -34], ![40, -2, -40, -60, 9, -26, 4, -16, 12, 4, -54], ![22, 0, -22, -34, 6, -17, 2, -8, 6, 4, -32], ![14, 0, -14, -22, 4, -10, 1, -6, 4, 2, -20], ![8, 0, -8, -12, 2, -6, 0, -3, 2, 2, -12], ![44, -2, -44, -66, 10, -28, 4, -18, 13, 4, -58], ![26, 0, -26, -40, 6, -18, 2, -10, 8, 3, -36], ![4, 0, -4, -6, 0, -2, 0, -2, 2, 0, -5]]

def rayDenominator : Fin 11 → Fin 11 → ℝ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

def testPoint : Fin 11 → Fin 10 → Bool := ![![true, true, false, true, false, true, true, false, true, false], ![true, true, false, false, false, false, true, true, true, false], ![false, true, false, false, false, false, true, true, true, false], ![true, true, false, true, false, true, true, false, true, false], ![true, true, false, true, false, true, true, false, true, false], ![false, false, false, false, false, true, false, true, false, true], ![false, false, false, false, false, true, false, true, false, true], ![false, false, false, false, false, true, false, true, false, true], ![false, true, false, false, false, false, true, true, true, false], ![true, true, false, false, false, false, true, true, true, false], ![false, false, false, false, false, false, false, true, false, true]]

def baseLabel (x : Fin 10 → Bool) : ℝ :=
  if 0 < affine baseNumerator x then 1 else -1

set_option maxHeartbeats 2000000 in
-- The explicit finite matrix has 121 entries.
theorem ray_basis_identity (i j : Fin 11) :
    affine (rayNumerator i) (basisPoint j) =
      basisValue j * affine (rayDenominator i) (basisPoint j) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [affine, affineValue, rayNumerator, rayDenominator,
      basisPoint, basisValue, Fin.sum_univ_succ, boolToReal]

theorem ray_strict_failure (i : Fin 11) :
    baseLabel (testPoint i) * affine (rayNumerator i) (testPoint i) <
      affine (rayDenominator i) (testPoint i) := by
  fin_cases i <;>
    norm_num [baseLabel, affine, affineValue, rayNumerator, rayDenominator,
      testPoint, baseNumerator, Fin.sum_univ_succ, boolToReal]

theorem no_coordinate_ray (i : Fin 11) (a : Fin 11 → ℝ)
    (hbasis : ∀ j, affine a (basisPoint j) =
      basisValue j * affine (rayDenominator i) (basisPoint j)) :
    ¬ ∀ x, affine (rayDenominator i) x ≤ baseLabel x * affine a x := by
  have ha : a = rayNumerator i := basis_affine_injective _ _
    (fun j => (hbasis j).trans (ray_basis_identity i j).symm)
  subst a
  intro h
  exact (not_lt_of_ge (h (testPoint i))) (ray_strict_failure i)

end HeadComplexity.FeasibleConeNoCoordinateRay
