import HeadComplexity.Research.OneHeadFeasibleBasisNonuniqueness
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option linter.style.header false
set_option linter.style.longLine false
set_option maxRecDepth 2048

/-! The existing full-gap one-head counterexample has an integer-unimodular
actual sample basis. Unimodularity makes its constant-denominator interpolant
feasible, but does not make that interpolant preserve every feasible branch. -/

noncomputable section
namespace HeadComplexity.UnimodularFeasibleBasisObstruction
open OneHeadFeasibleBasisNonuniqueness
open scoped BigOperators

def basisMatrix : Matrix (Fin 7) (Fin 7) ℤ :=
  ![![1,0,0,0,1,1,1], ![1,0,0,1,0,0,0], ![1,0,0,1,1,0,1],
    ![1,0,1,0,0,0,1], ![1,0,1,0,0,1,1], ![1,1,0,0,0,0,0],
    ![1,1,0,1,0,1,1]]

def inverseMatrix : Matrix (Fin 7) (Fin 7) ℤ :=
  ![![1,1,-1,1,-1,0,0], ![-1,-1,1,-1,1,1,0], ![-2,-1,2,-2,3,1,-1],
    ![-1,0,1,-1,1,0,0], ![-1,-1,2,-2,2,1,-1], ![0,0,0,-1,1,0,0],
    ![1,0,-1,2,-2,-1,1]]

theorem basisMatrix_zero (j : Fin 7) : basisMatrix j 0 = 1 := by
  fin_cases j <;> rfl

theorem basisMatrix_succ (j : Fin 7) (i : Fin 6) :
    (basisMatrix j i.succ : ℝ) = boolToReal (basisPoint j i) := by
  fin_cases j <;> fin_cases i <;> norm_num [basisMatrix, basisPoint, boolToReal]

/-- An exact integer inverse, so the actual augmented Boolean basis is unimodular. -/
theorem basisMatrix_mul_inverse : basisMatrix * inverseMatrix = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [basisMatrix, inverseMatrix, Fin.sum_univ_succ,
      Matrix.one_apply]

theorem basisMatrix_det_isUnit : IsUnit basisMatrix.det := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨inverseMatrix.det, ?_⟩
  rw [← Matrix.det_mul, basisMatrix_mul_inverse, Matrix.det_one]

def constantScore (x : Fin 6 → Bool) : ℝ :=
  affineValue 3 ![-2,-4,-2,-2,-2,2] x

/-- The constant-denominator interpolant has the same prescribed basis values. -/
theorem constant_basis_values (j : Fin 7) :
    constantScore (basisPoint j) = basisValue j := by
  fin_cases j <;> norm_num [constantScore, affineValue, basisPoint, basisValue,
    Fin.sum_univ_succ, boolToReal]

/-- It is globally unit feasible; this fact does not preserve branch labels. -/
theorem constant_full_cube_unit_slack (x : Fin 6 → Bool) :
    1 ≤ |constantScore x| := by
  have hvec : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    ext i
    fin_cases i <;> rfl
  rw [hvec]
  generalize x 0 = b0, x 1 = b1, x 2 = b2, x 3 = b3, x 4 = b4, x 5 = b5
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    norm_num [constantScore, affineValue, Fin.sum_univ_succ, boolToReal]

/-- The constant interpolant disagrees with an admissible full-gap branch. -/
theorem constant_branch_disagreement :
    constantScore ![false,false,false,true,false,false] = 1 ∧
    linearScore 1 (coefficients 1) ![false,false,false,true,false,false] = -1 := by
  constructor
  · norm_num [constantScore, affineValue, Fin.sum_univ_succ, boolToReal]
  · exact singleton_disagreement.2

/-- The counterexample does not have an origin contact. -/
theorem basis_omits_origin (j : Fin 7) : basisPoint j ≠ (fun _ ↦ false) := by
  fin_cases j <;> intro h
  all_goals
    solve
    | have h' := congrFun h 0; norm_num [basisPoint] at h'
    | have h' := congrFun h 1; norm_num [basisPoint] at h'
    | have h' := congrFun h 2; norm_num [basisPoint] at h'
    | have h' := congrFun h 3; norm_num [basisPoint] at h'


namespace Origin

/-- A different unimodular actual basis, now containing the origin. -/
def points : Fin 7 → Fin 6 → Bool := ![![false,false,false,false,false,false],![false,true,false,true,false,false],![true,true,false,true,false,true],![false,true,false,true,true,true],![false,true,false,false,true,false],![false,true,true,false,true,true],![true,true,false,false,false,true]]
def values : Fin 7 → ℝ := ![1,1,-1,1,-1,1,1]
def matrix : Matrix (Fin 7) (Fin 7) ℤ := ![![1,0,0,0,0,0,0],![1,0,1,0,1,0,0],![1,1,1,0,1,0,1],![1,0,1,0,1,1,1],![1,0,1,0,0,1,0],![1,0,1,1,0,1,1],![1,1,1,0,0,0,1]]
def inverse : Matrix (Fin 7) (Fin 7) ℤ := ![![1,0,0,0,0,0,0],![0,-1,2,-1,1,0,-1],![-1,1,-1,0,0,0,1],![0,0,1,-1,0,1,-1],![0,0,1,0,0,0,-1],![0,-1,1,0,1,0,-1],![0,0,-1,1,-1,0,1]]

theorem origin_contact : points 0 = fun _ ↦ false := by
  ext i
  fin_cases i <;> rfl

theorem matrix_zero (j : Fin 7) : matrix j 0 = 1 := by
  fin_cases j <;> rfl

theorem matrix_succ (j : Fin 7) (i : Fin 6) :
    (matrix j i.succ : ℝ) = boolToReal (points j i) := by
  fin_cases j <;> fin_cases i <;> norm_num [matrix, points, boolToReal]

theorem matrix_mul_inverse : matrix * inverse = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [matrix, inverse, Fin.sum_univ_succ, Matrix.one_apply]

theorem matrix_det_isUnit : IsUnit matrix.det := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨inverse.det, ?_⟩
  rw [← Matrix.det_mul, matrix_mul_inverse, Matrix.det_one]

def positiveSlopes : Fin 6 → ℝ := ![3,1,1,1,1,1]
def positiveNumerator : Fin 6 → ℝ := ![-31,15,-13,-13,-19,21]
def denominator (x : Fin 6 → Bool) : ℝ := affineValue 1 positiveSlopes x
def score (x : Fin 6 → Bool) : ℝ :=
  affineValue 1 positiveNumerator x / denominator x
def constantScore (x : Fin 6 → Bool) : ℝ :=
  affineValue 1 ![-6,2,-2,-2,-4,4] x

theorem positiveSlopes_pos (i : Fin 6) : 0 < positiveSlopes i := by
  fin_cases i <;> norm_num [positiveSlopes]

def atom : FracAtom 6 := FracAtom.ofPositiveAffineRatio
  1 positiveNumerator 1 positiveSlopes (by norm_num) positiveSlopes_pos

theorem atom_eval (x : Fin 6 → Bool) : atom.eval x = score x := by
  exact FracAtom.ofPositiveAffineRatio_eval _ _ _ _ _ _ _

theorem basis_values (j : Fin 7) :
    score (points j) = values j ∧ constantScore (points j) = values j := by
  fin_cases j <;> norm_num [score, constantScore, denominator, positiveSlopes,
    positiveNumerator, points, values, affineValue, Fin.sum_univ_succ, boolToReal]

theorem full_cube_unit_slack (x : Fin 6 → Bool) :
    1 ≤ |score x| ∧ 1 ≤ |constantScore x| := by
  have hvec : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    ext i
    fin_cases i <;> rfl
  rw [hvec]
  generalize x 0 = b0, x 1 = b1, x 2 = b2, x 3 = b3, x 4 = b4, x 5 = b5
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    norm_num [score, constantScore, denominator, positiveSlopes, positiveNumerator,
      affineValue, Fin.sum_univ_succ, boolToReal]

/-- Origin contact and unimodularity still do not preserve the labels when
replacing the denominator by the constant one and refitting the same basis. -/
theorem branch_disagreement :
    constantScore ![false,false,true,true,false,true] = 1 ∧
    score ![false,false,true,true,false,true] = -1 := by
  norm_num [score, constantScore, denominator, positiveSlopes, positiveNumerator,
    affineValue, Fin.sum_univ_succ, boolToReal]

theorem original_computable :
    fracComputable 6 1 (fun x ↦ decide (0 < score x)) := by
  classical
  refine ⟨fun _ ↦ atom, 0, fun x ↦ ?_⟩
  simp only [Fin.sum_univ_one, zero_add, atom_eval]
  simp

end Origin

namespace OriginBranches

/-- Both branches below have strictly positive, coherent denominator slopes. -/
def points : Fin 7 → Fin 6 → Bool := ![![false,false,false,false,false,false],![false,true,false,true,false,false],![false,true,true,true,true,true],![false,false,true,true,true,true],![true,false,true,false,true,false],![true,true,true,true,false,false],![true,true,true,false,false,true]]
def values : Fin 7 → ℝ := ![1,-1,1,-1,-1,1,-1]
def matrix : Matrix (Fin 7) (Fin 7) ℤ := ![![1,0,0,0,0,0,0],![1,0,1,0,1,0,0],![1,0,1,1,1,1,1],![1,0,0,1,1,1,1],![1,1,0,1,0,1,0],![1,1,1,1,1,0,0],![1,1,1,1,0,0,1]]
def inverse : Matrix (Fin 7) (Fin 7) ℤ := ![![1,0,0,0,0,0,0],![-2,2,-2,1,1,-1,1],![0,0,1,-1,0,0,0],![2,-3,2,-1,-1,2,-1],![-1,1,-1,1,0,0,0],![-1,1,0,0,1,-1,0],![-1,1,-1,1,0,-1,1]]

theorem origin_contact : points 0 = fun _ ↦ false := by
  ext i
  fin_cases i <;> rfl

theorem matrix_zero (j : Fin 7) : matrix j 0 = 1 := by
  fin_cases j <;> rfl

theorem matrix_succ (j : Fin 7) (i : Fin 6) :
    (matrix j i.succ : ℝ) = boolToReal (points j i) := by
  fin_cases j <;> fin_cases i <;> norm_num [matrix, points, boolToReal]

theorem matrix_mul_inverse : matrix * inverse = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [matrix, inverse, Fin.sum_univ_succ, Matrix.one_apply]

theorem matrix_det_isUnit : IsUnit matrix.det := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨inverse.det, ?_⟩
  rw [← Matrix.det_mul, matrix_mul_inverse, Matrix.det_one]

def slopes : Fin 2 → Fin 6 → ℝ := ![![2,1,1,1,1,1], ![1,1,1,1,1,3]]
def numerators : Fin 2 → Fin 6 → ℝ := ![![-42,11,51,-15,-15,-27], ![-47,15,55,-19,-13,-31]]
def denominator (k : Fin 2) (x : Fin 6 → Bool) : ℝ := affineValue 1 (slopes k) x
def score (k : Fin 2) (x : Fin 6 → Bool) : ℝ :=
  affineValue 1 (numerators k) x / denominator k x

theorem slopes_pos (k : Fin 2) (i : Fin 6) : 0 < slopes k i := by
  fin_cases k <;> fin_cases i <;> norm_num [slopes]

def atom (k : Fin 2) : FracAtom 6 := FracAtom.ofPositiveAffineRatio
  1 (numerators k) 1 (slopes k) (by norm_num) (slopes_pos k)

theorem atom_eval (k : Fin 2) (x : Fin 6 → Bool) : (atom k).eval x = score k x := by
  exact FracAtom.ofPositiveAffineRatio_eval _ _ _ _ _ _ _

theorem basis_values (k : Fin 2) (j : Fin 7) :
    score k (points j) = values j := by
  fin_cases k <;> fin_cases j <;> norm_num [score, denominator, slopes,
    numerators, points, values, affineValue, Fin.sum_univ_succ, boolToReal]

theorem full_cube_unit_slack (k : Fin 2) (x : Fin 6 → Bool) :
    1 ≤ |score k x| := by
  have hvec : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    ext i
    fin_cases i <;> rfl
  rw [hvec]
  generalize x 0 = b0, x 1 = b1, x 2 = b2, x 3 = b3, x 4 = b4, x 5 = b5
  fin_cases k <;> cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    norm_num [score, denominator, slopes, numerators,
      affineValue, Fin.sum_univ_succ, boolToReal]

/-- Two genuine full-gap branches disagree despite an origin contact and
an integer-unimodular common actual basis with identical unit values. -/
theorem branch_disagreement :
    score 0 ![false,true,false,false,true,false] = -1 ∧
    score 1 ![false,true,false,false,true,false] = 1 := by
  norm_num [score, denominator, slopes, numerators,
    affineValue, Fin.sum_univ_succ, boolToReal]

theorem original_computable (k : Fin 2) :
    fracComputable 6 1 (fun x ↦ decide (0 < score k x)) := by
  classical
  refine ⟨fun _ ↦ atom k, 0, fun x ↦ ?_⟩
  simp only [Fin.sum_univ_one, zero_add, atom_eval]
  simp

end OriginBranches
end HeadComplexity.UnimodularFeasibleBasisObstruction
