import HeadComplexity.Atoms.IntegerBinaryFinite

set_option linter.style.header false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-! Rational Jacobian nonvanishing for the mixed binary-coordinate certificate.
The all-dimension extension is a written proof in the accompanying artifact. -/
namespace HeadComplexity.IntegerBinaryFiber
open scoped BigOperators

/-- The score derivatives in the order of the explicit parameter columns. -/
def jacobian : Matrix (Fin 108) (Fin 108) ℚ := fun r c ↦
  let v := indices r
  let i := c.val % 18
  let h : Fin 3 := ⟨(c.val / 18) % 3, Nat.mod_lt _ (by decide)⟩
  if c.val < 54 then (bit v i : ℚ) / den h v
  else -(num h v : ℚ) * bit v i / (3 * (den h v : ℚ)^2)

def rowScale (r : Fin 108) : ℚ :=
  3 * (den 0 (indices r) : ℚ)^2 * (den 1 (indices r) : ℚ)^2 *
    (den 2 (indices r) : ℚ)^2

theorem clearedJacobian_eq :
    clearedJacobian.map (fun a ↦ (a : ℚ)) = Matrix.diagonal rowScale * jacobian := by
  ext r c
  rw [Matrix.diagonal_mul]
  let v := indices r
  let h : Fin 3 := ⟨(c.val / 18) % 3, Nat.mod_lt _ (by decide)⟩
  have hd : (den h v : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt (sample_denominators_positive r h)
  have hpAll : ∀ j : Fin 3, (den j v : ℚ)^2 *
      ((∏ g : Fin 3, if g = j then 1 else den g v ^ 2 : ℤ) : ℚ) =
      (den 0 v : ℚ)^2 * (den 1 v : ℚ)^2 * (den 2 v : ℚ)^2 := by
    intro j
    fin_cases j <;> norm_num [Fin.prod_univ_succ] <;> ring
  have hp := hpAll h
  have hs : rowScale r = 3 * ((den h v : ℚ)^2 *
      ((∏ g : Fin 3, if g = h then 1 else den g v ^ 2 : ℤ) : ℚ)) := by
    rw [hp]
    dsimp [rowScale, v]
    ring
  simp only [Matrix.map_apply, clearedJacobian, jacobian]
  change (↑(if c.val < 54 then
      3 * bit v (c.val % 18) * den h v * (∏ g : Fin 3, if g = h then 1 else den g v ^ 2)
    else -num h v * bit v (c.val % 18) * (∏ g : Fin 3, if g = h then 1 else den g v ^ 2)) : ℚ) =
    rowScale r * (if c.val < 54 then (bit v (c.val % 18) : ℚ) / den h v
      else -(num h v : ℚ) * bit v (c.val % 18) / (3 * (den h v : ℚ)^2))
  rw [hs]
  split_ifs <;> push_cast <;> field_simp

theorem jacobian_det_ne_zero : jacobian.det ≠ 0 := by
  have hm : (clearedJacobian.map (fun a ↦ (a : ℚ))).det ≠ 0 := by
    rw [← Int.cast_det]
    exact_mod_cast clearedJacobian_det_ne_zero
  intro hz
  apply hm
  rw [clearedJacobian_eq, Matrix.det_mul, hz, mul_zero]

def cloneRows : Fin 6 → Fin 108 := ![0, 13, 15, 25, 30, 32]
def cloneColumns : Fin 6 → Fin 108 := ![0, 18, 36, 54, 72, 90]
def clearedClone : Matrix (Fin 6) (Fin 6) ℤ :=
  clearedJacobian.submatrix cloneRows cloneColumns

def cloneInverseMod : Matrix (Fin 6) (Fin 6) (ZMod 101) := ![
  ![39, 80, 72, 60, 88, 99],
  ![64, 21, 48, 63, 86, 88],
  ![63, 89, 19, 39, 18, 17],
  ![21, 3, 95, 98, 79, 39],
  ![88, 29, 29, 8, 66, 48],
  ![86, 22, 27, 94, 51, 19]]

theorem clone_samples_have_one : ∀ r, bit (indices (cloneRows r)) 0 = 1 := by
  decide +kernel

theorem clone_inverse_mul :
    cloneInverseMod * clearedClone.map (fun a ↦ (a : ZMod 101)) = 1 := by
  decide +kernel

theorem clearedClone_det_ne_zero : clearedClone.det ≠ 0 := by
  have hm : (clearedClone.map (fun a ↦ (a : ZMod 101))).det ≠ 0 := by
    intro hz
    have h := congrArg Matrix.det clone_inverse_mul
    rw [Matrix.det_mul, hz, mul_zero, Matrix.det_one] at h
    exact (by decide : (0 : ZMod 101) ≠ 1) h
  intro hz
  apply hm
  rw [← Int.cast_det, hz]
  rfl

theorem clone_jacobian_det_ne_zero :
    (jacobian.submatrix cloneRows cloneColumns).det ≠ 0 := by
  have heq : clearedClone.map (fun a ↦ (a : ℚ)) =
      Matrix.diagonal (fun i ↦ rowScale (cloneRows i)) *
        jacobian.submatrix cloneRows cloneColumns := by
    ext r c
    have h := congrFun (congrFun clearedJacobian_eq (cloneRows r)) (cloneColumns c)
    simpa [Matrix.diagonal_mul, Matrix.submatrix_apply, Matrix.map_apply,
      clearedClone] using h
  have hm : (clearedClone.map (fun a ↦ (a : ℚ))).det ≠ 0 := by
    rw [← Int.cast_det]
    exact_mod_cast clearedClone_det_ne_zero
  intro hz
  apply hm
  rw [heq, Matrix.det_mul, hz, mul_zero]

end HeadComplexity.IntegerBinaryFiber
