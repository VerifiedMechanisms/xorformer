import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option maxRecDepth 4096

/-! An origin-containing unit-contact simplex need not determine the same
truth table after replacing its coherent denominator by a constant. -/

noncomputable section
namespace HeadComplexity.OriginContactBranchCounterexample
open scoped BigOperators

def affine (a : Fin 7 → ℝ) (x : Fin 6 → Bool) : ℝ :=
  affineValue (a 0) (fun i => a i.succ) x

def basisPoint : Fin 7 → Fin 6 → Bool := ![![false, false, false, false, false, false], ![false, true, false, false, true, false], ![false, true, false, true, false, false], ![false, true, true, true, false, true], ![true, false, true, true, false, false], ![true, false, true, true, true, false], ![true, true, true, false, false, true]]

def basisValue : Fin 7 → ℝ := ![1, 1, -1, 1, 1, -1, -1]

def numerator : Fin 7 → ℝ := ![1, -31, 15, 55, -19, -13, -47]

def denominator : Fin 7 → ℝ := ![1, 3, 1, 1, 1, 1, 1]

def constantNumerator : Fin 7 → ℝ := ![1, -6, 2, 10, -4, -2, -8]

theorem basis_contains_origin : basisPoint 0 = fun _ => false := by
  ext i
  fin_cases i <;> rfl

theorem denominator_pos (i : Fin 7) : 0 < denominator i := by
  fin_cases i <;> norm_num [denominator]

theorem basis_contacts (j : Fin 7) :
    affine numerator (basisPoint j) = basisValue j * affine denominator (basisPoint j) := by
  fin_cases j <;> norm_num [affine, affineValue, numerator, denominator,
    basisPoint, basisValue, Fin.sum_univ_succ, boolToReal]

theorem constant_basis_contacts (j : Fin 7) :
    affine constantNumerator (basisPoint j) = basisValue j := by
  fin_cases j <;> norm_num [affine, affineValue, constantNumerator,
    basisPoint, basisValue, Fin.sum_univ_succ, boolToReal]

/-- This also certifies affine independence of the seven contact points. -/
theorem basis_affine_injective (a : Fin 7 → ℝ)
    (h : ∀ j, affine a (basisPoint j) = 0) : a = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  norm_num [affine, affineValue, basisPoint, Fin.sum_univ_succ, boolToReal] at h0 h1 h2 h3 h4 h5 h6
  clear h
  funext i
  fin_cases i <;> norm_num <;> linarith

/-- There is no different constant-denominator affine interpolant with these
unit contact values. -/
theorem constant_interpolant_unique (a : Fin 7 → ℝ)
    (h : ∀ j, affine a (basisPoint j) = basisValue j) : a = constantNumerator := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  norm_num [affine, affineValue, basisPoint, basisValue, Fin.sum_univ_succ, boolToReal] at h0 h1 h2 h3 h4 h5 h6
  clear h
  funext i
  fin_cases i <;> norm_num [constantNumerator] <;> linarith

set_option maxHeartbeats 4000000 in
-- Enumerating both full 64-vertex gap certificates needs a larger tactic budget.
theorem both_full_cube_unit_gaps (x : Fin 6 → Bool) :
    affine denominator x ≤ |affine numerator x| ∧ 1 ≤ |affine constantNumerator x| := by
  have hx : x = ![x 0,x 1,x 2,x 3,x 4,x 5] := by
    ext i
    fin_cases i <;> rfl
  rw [hx]
  generalize x 0 = b0, x 1 = b1, x 2 = b2, x 3 = b3, x 4 = b4, x 5 = b5
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    norm_num [affine, affineValue, numerator, denominator, constantNumerator,
      Fin.sum_univ_succ, boolToReal]

theorem different_labels :
    affine numerator ![false,false,true,false,true,true] = -4 ∧
    affine constantNumerator ![false,false,true,false,true,true] = 1 := by
  norm_num [affine, affineValue, numerator, constantNumerator,
    Fin.sum_univ_succ, boolToReal]

def atom : FracAtom 6 :=
  FracAtom.ofPositiveAffineRatio (numerator 0) (fun i => numerator i.succ)
    (denominator 0) (fun i => denominator i.succ)
    (denominator_pos 0) (fun i => denominator_pos i.succ)

theorem atom_eval (x : Fin 6 → Bool) :
    atom.eval x = affine numerator x / affine denominator x := by
  exact FracAtom.ofPositiveAffineRatio_eval ..

end HeadComplexity.OriginContactBranchCounterexample
