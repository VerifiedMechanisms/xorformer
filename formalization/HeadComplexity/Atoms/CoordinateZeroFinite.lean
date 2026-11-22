import HeadComplexity.Atoms.CoordinateZeroData
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-! Kernel-checked arithmetic for the sixteen-bit, three-head regular zero.
This is an auxiliary obstruction, not an asymptotic head lower bound. -/
namespace HeadComplexity.CoordinateZeroFiber
open scoped BigOperators


def bit (v i : ℕ) : ℤ := ((v / 2^i) % 2 : ℕ)
def dot (a : Fin 16 → ℤ) (v : ℕ) : ℤ := ∑ i, a i * bit v i.val
def den (h : Fin 3) (v : ℕ) : ℤ := 1 + dot (denominatorSlopes h) v
def num (h : Fin 3) (v : ℕ) : ℤ := dot (numeratorScaledSlopes h) v

def score (v : ℕ) : ℚ := 1 + ∑ h : Fin 3, (num h v : ℚ) / (3 * den h v)

theorem slopes_positive : ∀ h i, 0 < denominatorSlopes h i := by decide +kernel

theorem indices_injective : Function.Injective indices := by decide +kernel

theorem indices_range : ∀ i, 0 < indices i ∧ indices i < 2^16 := by decide +kernel

theorem sample_denominators_positive : ∀ r h, 0 < den h (indices r) := by decide +kernel


def clearedScore (v : ℕ) : ℤ :=
  3 * den 0 v * den 1 v * den 2 v +
    num 0 v * den 1 v * den 2 v +
    num 1 v * den 0 v * den 2 v +
    num 2 v * den 0 v * den 1 v

theorem cleared_sample_scores_zero : ∀ r, clearedScore (indices r) = 0 := by decide +kernel


theorem sample_scores_zero : ∀ r, score (indices r) = 0 := by
  intro r
  have hd : ∀ h : Fin 3, (den h (indices r) : ℚ) ≠ 0 := by
    intro h
    exact_mod_cast ne_of_gt (sample_denominators_positive r h)
  have hz : (clearedScore (indices r) : ℚ) = 0 := by
    rw [cleared_sample_scores_zero]
    rfl
  simp only [clearedScore, Int.cast_add, Int.cast_mul, Int.cast_ofNat] at hz
  simp only [score, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero]
  change 1 + ((num 0 (indices r) : ℚ) / (3 * den 0 (indices r)) +
    ((num 1 (indices r) : ℚ) / (3 * den 1 (indices r)) +
      (num 2 (indices r) : ℚ) / (3 * den 2 (indices r)))) = 0
  field_simp [hd 0, hd 1, hd 2]
  linear_combination hz


/-- Each rational Jacobian row is multiplied by three times all squared denominators. -/
def clearedJacobian : Matrix (Fin 96) (Fin 96) ℤ := fun r c ↦
  let v := indices r
  let i := c.val % 16
  let h : Fin 3 := ⟨(c.val / 16) % 3, Nat.mod_lt _ (by decide)⟩
  let others := ∏ g : Fin 3, if g = h then 1 else den g v ^ 2
  if c.val < 48 then 3 * bit v i * den h v * others
  else -num h v * bit v i * others

theorem jacobian_mod_eq :
    clearedJacobian.map (fun a ↦ (a : ZMod 101)) = jacobianMod := by
  ext r c
  fin_cases r <;> revert c <;> decide +kernel


theorem inverse_mul_mod : inverseMod * jacobianMod = 1 := by
  ext r c
  fin_cases r <;> revert c <;> decide +kernel


theorem clearedJacobian_det_ne_zero : clearedJacobian.det ≠ 0 := by
  have hm : (clearedJacobian.map (fun a ↦ (a : ZMod 101))).det ≠ 0 := by
    rw [jacobian_mod_eq]
    intro hz
    have h := congrArg Matrix.det inverse_mul_mod
    rw [Matrix.det_mul, hz, mul_zero, Matrix.det_one] at h
    exact (by decide : (0 : ZMod 101) ≠ 1) h
  intro hz
  apply hm
  rw [← Int.cast_det, hz]
  rfl

end HeadComplexity.CoordinateZeroFiber
