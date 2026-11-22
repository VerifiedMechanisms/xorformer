import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Exact finite arithmetic for the positive two-head interpolation ambiguity.
This does not prove the asymptotic worst-case lower bound. -/
namespace HeadComplexity.IntegerFiber
open scoped BigOperators

def bit (v i : ℕ) : ℤ := ((v / 2^i) % 2 : ℕ)
def indices : Fin 20 → ℕ := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 23, 24, 31]
def uOne (s : Bool) : Fin 5 → ℤ :=
  if s then ![5, 0, 0, -1, 2] else ![5, 0, 0, -1, 1]
def uTwo (s : Bool) : Fin 5 → ℤ :=
  if s then ![-2, 4, 5, 3, 6] else ![-2, 4, 5, 3, 5]
def bOne (s : Bool) : Fin 5 → ℤ :=
  if s then ![1, 3, 3, 2, 2] else ![1, 3, 3, 2, 1]
def bTwo (s : Bool) : Fin 5 → ℤ :=
  if s then ![2, 2, 2, 1, 3] else ![2, 2, 2, 1, 2]

def dot (a : Fin 5 → ℤ) (v : ℕ) : ℤ := ∑ i, a i * bit v i.val
def denOne (s : Bool) (v : ℕ) : ℤ := 1 + dot (bOne s) v
def denTwo (s : Bool) (v : ℕ) : ℤ := 1 + dot (bTwo s) v

def score (s : Bool) (v : ℕ) : ℚ :=
  (dot (uOne s) v : ℚ) / denOne s v + (dot (uTwo s) v : ℚ) / denTwo s v

theorem slopes_positive (s : Bool) :
    (∀ i, 0 < bOne s i) ∧ (∀ i, 0 < bTwo s i) := by
  cases s <;> decide

theorem denominators_positive (s : Bool) :
    ∀ v : Fin 32, 0 < denOne s v.val ∧ 0 < denTwo s v.val := by
  cases s <;> decide

theorem sampled_scores_equal : ∀ i : Fin 20,
    score false (indices i) = score true (indices i) := by
  intro i
  fin_cases i <;> norm_num [score, indices, denOne, denTwo, dot, uOne, uTwo,
    bOne, bTwo, bit, Fin.sum_univ_succ]

theorem held_out_difference : score false 17 - score true 17 = 11/60 := by
  norm_num [score, denOne, denTwo, dot, uOne, uTwo, bOne, bTwo, bit, Fin.sum_univ_succ]

/-- Multiply each Jacobian row by the square of both positive denominators. -/
def clearedJacobian (s : Bool) : Matrix (Fin 20) (Fin 20) ℤ := fun r c ↦
  let v := indices r
  let x := bit v (c.val % 5)
  let d := denOne s v
  let e := denTwo s v
  if c.val < 5 then x*d*e^2 else
  if c.val < 10 then x*e*d^2 else
  if c.val < 15 then -(dot (uOne s) v)*x*e^2 else
    -(dot (uTwo s) v)*x*d^2

def inverseMod (s : Bool) : Matrix (Fin 20) (Fin 20) (ZMod 101) :=
  if s then ![
    ![2, 19, 88, 62, 99, 17, 50, 94, 7, 2, 97, 19, 22, 63, 82, 0, 7, 8, 75, 0],
    ![97, 18, 90, 13, 88, 18, 30, 60, 40, 19, 29, 90, 96, 77, 79, 0, 39, 59, 86, 0],
    ![4, 63, 11, 68, 13, 38, 71, 84, 61, 46, 72, 76, 5, 40, 22, 0, 62, 42, 15, 0],
    ![1, 7, 95, 38, 18, 3, 3, 3, 54, 12, 61, 12, 81, 53, 16, 0, 48, 26, 67, 0],
    ![68, 13, 71, 84, 13, 3, 55, 42, 45, 2, 70, 56, 89, 100, 76, 34, 74, 17, 4, 62],
    ![39, 67, 87, 23, 54, 38, 60, 61, 56, 13, 59, 67, 82, 75, 11, 0, 23, 84, 30, 0],
    ![28, 13, 51, 95, 63, 61, 19, 53, 4, 47, 64, 67, 73, 87, 91, 0, 40, 89, 39, 0],
    ![77, 96, 73, 41, 95, 62, 24, 68, 58, 91, 79, 10, 31, 74, 30, 0, 64, 1, 22, 0],
    ![18, 35, 32, 30, 89, 80, 7, 39, 6, 2, 40, 69, 37, 41, 2, 0, 43, 78, 100, 0],
    ![18, 5, 56, 46, 10, 55, 58, 1, 13, 100, 10, 77, 39, 28, 74, 53, 59, 18, 17, 1],
    ![21, 97, 42, 17, 28, 44, 13, 73, 28, 38, 8, 64, 30, 88, 86, 0, 56, 64, 95, 0],
    ![75, 55, 59, 32, 13, 32, 54, 67, 76, 27, 70, 57, 100, 97, 87, 0, 45, 37, 6, 0],
    ![34, 6, 31, 23, 98, 81, 8, 45, 82, 59, 88, 72, 25, 72, 13, 0, 66, 61, 29, 0],
    ![40, 38, 27, 100, 59, 73, 53, 45, 26, 47, 79, 25, 72, 30, 38, 0, 24, 13, 84, 0],
    ![100, 6, 31, 12, 75, 33, 11, 54, 6, 63, 3, 21, 6, 58, 17, 94, 30, 66, 12, 82],
    ![30, 11, 34, 10, 81, 26, 60, 95, 83, 13, 16, 40, 72, 64, 5, 0, 88, 14, 5, 0],
    ![44, 53, 51, 47, 21, 18, 69, 23, 76, 27, 58, 63, 33, 77, 18, 0, 33, 81, 65, 0],
    ![48, 91, 74, 11, 78, 24, 11, 18, 37, 45, 100, 20, 36, 22, 38, 0, 36, 70, 25, 0],
    ![67, 62, 90, 33, 5, 58, 55, 19, 73, 66, 58, 70, 4, 89, 44, 0, 76, 58, 64, 0],
    ![88, 45, 11, 87, 86, 31, 96, 6, 90, 76, 11, 55, 23, 47, 32, 94, 20, 89, 19, 82]
  ]
  else ![
    ![56, 92, 31, 78, 21, 89, 91, 29, 7, 30, 90, 38, 56, 25, 79, 0, 48, 10, 48, 0],
    ![66, 64, 61, 30, 43, 44, 42, 73, 40, 74, 91, 66, 69, 24, 19, 0, 51, 99, 51, 0],
    ![35, 17, 40, 51, 58, 12, 59, 71, 61, 92, 10, 100, 32, 93, 82, 0, 50, 2, 50, 0],
    ![25, 17, 36, 90, 17, 35, 10, 19, 54, 2, 13, 99, 40, 81, 82, 0, 55, 83, 55, 0],
    ![98, 51, 68, 43, 37, 24, 41, 4, 59, 79, 69, 41, 57, 11, 0, 96, 83, 54, 56, 19],
    ![0, 76, 44, 90, 43, 87, 36, 35, 56, 4, 36, 14, 35, 80, 30, 0, 100, 4, 100, 0],
    ![48, 55, 86, 71, 79, 54, 8, 100, 4, 5, 24, 89, 22, 43, 45, 0, 29, 86, 29, 0],
    ![8, 42, 28, 43, 60, 71, 67, 22, 58, 44, 15, 25, 10, 44, 17, 0, 6, 77, 6, 0],
    ![90, 65, 57, 85, 86, 75, 28, 87, 6, 73, 98, 27, 15, 24, 99, 0, 64, 47, 64, 0],
    ![5, 7, 0, 77, 42, 28, 34, 62, 28, 68, 13, 87, 29, 2, 12, 33, 88, 50, 42, 67],
    ![49, 75, 91, 44, 10, 14, 38, 58, 28, 60, 53, 14, 100, 87, 62, 0, 81, 80, 81, 0],
    ![47, 77, 10, 5, 31, 62, 29, 82, 76, 5, 25, 6, 30, 98, 10, 0, 20, 21, 20, 0],
    ![67, 45, 13, 44, 84, 24, 5, 67, 82, 20, 22, 78, 57, 60, 28, 0, 63, 51, 63, 0],
    ![52, 43, 48, 25, 8, 89, 6, 53, 26, 42, 55, 18, 1, 44, 71, 0, 78, 92, 78, 0],
    ![3, 24, 58, 91, 85, 72, 100, 28, 42, 5, 58, 52, 14, 29, 53, 14, 5, 87, 49, 43],
    ![74, 63, 10, 38, 96, 51, 56, 57, 83, 62, 29, 48, 81, 48, 25, 0, 84, 68, 84, 0],
    ![10, 22, 42, 7, 14, 40, 17, 34, 76, 58, 25, 66, 49, 71, 76, 0, 82, 76, 82, 0],
    ![66, 48, 55, 50, 52, 48, 92, 30, 37, 88, 64, 60, 81, 43, 37, 0, 16, 37, 16, 0],
    ![4, 61, 5, 48, 96, 75, 24, 78, 73, 67, 83, 31, 99, 66, 98, 0, 45, 22, 45, 0],
    ![4, 9, 25, 49, 96, 6, 83, 8, 51, 44, 64, 96, 22, 94, 49, 14, 100, 95, 99, 43]
  ]

theorem inverse_mul_mod (s : Bool) :
    inverseMod s * (clearedJacobian s).map (fun a ↦ (a : ZMod 101)) = 1 := by
  cases s <;> decide

theorem clearedJacobian_det_ne_zero (s : Bool) : (clearedJacobian s).det ≠ 0 := by
  have hm : ((clearedJacobian s).map (fun a ↦ (a : ZMod 101))).det ≠ 0 := by
    intro hz
    have h := congrArg Matrix.det (inverse_mul_mod s)
    rw [Matrix.det_mul, hz, mul_zero, Matrix.det_one] at h
    exact (by decide : (0 : ZMod 101) ≠ 1) h
  intro hz
  apply hm
  rw [← Int.cast_det, hz]
  rfl

/-- The analytic Jacobian formula at the two displayed parameter points. -/
def jacobian (s : Bool) : Matrix (Fin 20) (Fin 20) ℚ := fun r c ↦
  let v := indices r
  let x : ℚ := bit v (c.val % 5)
  let d : ℚ := denOne s v
  let e : ℚ := denTwo s v
  if c.val < 5 then x/d else
  if c.val < 10 then x/e else
  if c.val < 15 then -(dot (uOne s) v : ℚ)*x/d^2 else
    -(dot (uTwo s) v : ℚ)*x/e^2

def rowScale (s : Bool) (r : Fin 20) : ℚ :=
  (denOne s (indices r) : ℚ)^2 * (denTwo s (indices r) : ℚ)^2

theorem clearedJacobian_eq (s : Bool) :
    (clearedJacobian s).map (fun a ↦ (a : ℚ)) =
      Matrix.diagonal (rowScale s) * jacobian s := by
  have hd : ∀ r : Fin 20, denOne s (indices r) ≠ 0 ∧ denTwo s (indices r) ≠ 0 := by
    cases s <;> decide
  ext r c
  rw [Matrix.diagonal_mul]
  have hdq : (denOne s (indices r) : ℚ) ≠ 0 := by exact_mod_cast (hd r).1
  have heq : (denTwo s (indices r) : ℚ) ≠ 0 := by exact_mod_cast (hd r).2
  simp only [Matrix.map_apply, clearedJacobian, jacobian, rowScale]
  split_ifs <;> push_cast <;> field_simp

theorem jacobian_det_ne_zero (s : Bool) : (jacobian s).det ≠ 0 := by
  have hm : ((clearedJacobian s).map (fun a ↦ (a : ℚ))).det ≠ 0 := by
    rw [← Int.cast_det]
    exact_mod_cast clearedJacobian_det_ne_zero s
  intro hz
  apply hm
  rw [clearedJacobian_eq, Matrix.det_mul, hz, mul_zero]

def extensionRows : Fin 4 → Fin 20 := ![15,16,17,19]
def extensionColumns : Fin 4 → Fin 20 := ![4,9,14,19]
def clearedExtension (s : Bool) : Matrix (Fin 4) (Fin 4) ℤ :=
  (clearedJacobian s).submatrix extensionRows extensionColumns

def extensionInverseMod (s : Bool) : Matrix (Fin 4) (Fin 4) (ZMod 101) :=
  if s then ![![34, 44, 26, 62], ![53, 83, 31, 1], ![94, 41, 93, 82], ![94, 29, 56, 82]] else ![![96, 27, 76, 19], ![33, 46, 16, 67], ![14, 57, 81, 43], ![14, 1, 87, 43]]

theorem extension_inverse_mul (s : Bool) :
    extensionInverseMod s * (clearedExtension s).map (fun a ↦ (a : ZMod 101)) = 1 := by
  cases s <;> decide

theorem clearedExtension_det_ne_zero (s : Bool) : (clearedExtension s).det ≠ 0 := by
  have hm : ((clearedExtension s).map (fun a ↦ (a : ZMod 101))).det ≠ 0 := by
    intro hz
    have h := congrArg Matrix.det (extension_inverse_mul s)
    rw [Matrix.det_mul, hz, mul_zero, Matrix.det_one] at h
    exact (by decide : (0 : ZMod 101) ≠ 1) h
  intro hz
  apply hm
  rw [← Int.cast_det, hz]
  rfl

theorem extension_jacobian_det_ne_zero (s : Bool) :
    ((jacobian s).submatrix extensionRows extensionColumns).det ≠ 0 := by
  have heq : (clearedExtension s).map (fun a ↦ (a : ℚ)) =
      Matrix.diagonal (fun i ↦ rowScale s (extensionRows i)) *
        (jacobian s).submatrix extensionRows extensionColumns := by
    ext r c
    have h := congrFun (congrFun (clearedJacobian_eq s) (extensionRows r))
      (extensionColumns c)
    simpa [Matrix.diagonal_mul, Matrix.submatrix_apply, Matrix.map_apply,
      clearedExtension] using h
  have hm : ((clearedExtension s).map (fun a ↦ (a : ℚ))).det ≠ 0 := by
    rw [← Int.cast_det]
    exact_mod_cast clearedExtension_det_ne_zero s
  intro hz
  apply hm
  rw [heq, Matrix.det_mul, hz, mul_zero]

end HeadComplexity.IntegerFiber
