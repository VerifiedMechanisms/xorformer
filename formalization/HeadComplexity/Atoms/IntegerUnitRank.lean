import HeadComplexity.Atoms.IntegerBinaryFiber

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace HeadComplexity.IntegerBinaryFiber
namespace UnitRank
open scoped BigOperators

def newIndices : Fin 108 → ℕ := Function.update indices 53 92746

def integerRow (v : ℕ) (c : Fin 108) : ℤ :=
  let i := c.val % 18
  let h : Fin 3 := ⟨(c.val / 18) % 3, Nat.mod_lt _ (by decide)⟩
  let others := ∏ g : Fin 3, if g = h then 1 else den g v ^ 2
  if c.val < 54 then 3 * bit v i * den h v * others
  else -num h v * bit v i * others

def newCleared : Matrix (Fin 108) (Fin 108) ℤ := fun r ↦ integerRow (newIndices r)

def coefficients : Fin 108 → ZMod 101 := ![47, 61, 4, 38, 5, 37, 18, 56, 70, 15, 82, 34, 33, 41, 34, 44, 13, 64, 14, 20, 85, 81, 47, 24, 12, 81, 49, 9, 1, 50, 95, 20, 7, 76, 84, 95, 69, 12, 20, 52, 94, 69, 45, 98, 63, 36, 68, 36, 45, 99, 96, 33, 53, 14, 89, 2, 100, 28, 93, 89, 66, 100, 31, 27, 66, 81, 63, 54, 21, 95, 68, 15, 74, 21, 31, 41, 24, 9, 8, 73, 40, 21, 29, 77, 71, 86, 23, 97, 65, 10, 9, 7, 74, 72, 97, 79, 73, 1, 60, 31, 87, 59, 95, 4, 95, 93, 79, 0]

theorem replacement_row :
    (fun c ↦ (integerRow 92746 c : ZMod 101)) =
      ∑ k : Fin 108, coefficients k • jacobianMod k := by
  ext c
  fin_cases c <;> decide +kernel

theorem newCleared_mod :
    newCleared.map (fun a ↦ (a : ZMod 101)) =
      jacobianMod.updateRow 53 (fun c ↦ (integerRow 92746 c : ZMod 101)) := by
  ext r c
  by_cases hr : r = 53
  · subst r
    simp [newCleared, newIndices, Matrix.updateRow, Function.update, Matrix.map_apply]
  · have old := congrFun (congrFun jacobian_mod_eq r) c
    simpa [newCleared, newIndices, Matrix.updateRow, Function.update, Matrix.map_apply,
      integerRow, clearedJacobian, hr] using old

theorem newCleared_det_ne_zero : newCleared.det ≠ 0 := by
  letI : Fact (Nat.Prime 101) := ⟨by decide⟩
  have old : jacobianMod.det ≠ 0 := by
    intro hz
    have h := congrArg Matrix.det inverse_mul_mod
    rw [Matrix.det_mul, hz, mul_zero, Matrix.det_one] at h
    exact (by decide : (0 : ZMod 101) ≠ 1) h
  have hm : (newCleared.map (fun a ↦ (a : ZMod 101))).det ≠ 0 := by
    rw [newCleared_mod, replacement_row, Matrix.det_updateRow_sum]
    exact mul_ne_zero (by decide : coefficients 53 ≠ 0) old
  intro hz
  apply hm
  rw [← Int.cast_det, hz]
  rfl

theorem newIndices_injective : Function.Injective newIndices := by decide +kernel

theorem new_den_positive : ∀ r h, 0 < den h (newIndices r) := by decide +kernel

def rawJacobian : Matrix (Fin 108) (Fin 108) ℚ := fun r c ↦
  let v := newIndices r
  let i := c.val % 18
  let h : Fin 3 := ⟨(c.val / 18) % 3, Nat.mod_lt _ (by decide)⟩
  if c.val < 54 then (bit v i : ℚ) / den h v
  else -(num h v : ℚ) * bit v i / (3 * (den h v : ℚ)^2)

def newRowScale (r : Fin 108) : ℚ :=
  3 * (den 0 (newIndices r) : ℚ)^2 * (den 1 (newIndices r) : ℚ)^2 *
    (den 2 (newIndices r) : ℚ)^2

theorem newCleared_eq :
    newCleared.map (fun a ↦ (a : ℚ)) = Matrix.diagonal newRowScale * rawJacobian := by
  ext r c
  rw [Matrix.diagonal_mul]
  let v := newIndices r
  let h : Fin 3 := ⟨(c.val / 18) % 3, Nat.mod_lt _ (by decide)⟩
  have hd : (den h v : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt (new_den_positive r h)
  have hpAll : ∀ j : Fin 3, (den j v : ℚ)^2 *
      ((∏ g : Fin 3, if g = j then 1 else den g v ^ 2 : ℤ) : ℚ) =
      (den 0 v : ℚ)^2 * (den 1 v : ℚ)^2 * (den 2 v : ℚ)^2 := by
    intro j
    fin_cases j <;> norm_num [Fin.prod_univ_succ] <;> ring
  have hs : newRowScale r = 3 * ((den h v : ℚ)^2 *
      ((∏ g : Fin 3, if g = h then 1 else den g v ^ 2 : ℤ) : ℚ)) := by
    rw [hpAll h]
    dsimp [newRowScale, v]
    ring
  simp only [Matrix.map_apply, newCleared, integerRow, rawJacobian]
  change (↑(if c.val < 54 then
      3 * bit v (c.val % 18) * den h v * (∏ g : Fin 3, if g = h then 1 else den g v ^ 2)
    else -num h v * bit v (c.val % 18) * (∏ g : Fin 3, if g = h then 1 else den g v ^ 2)) : ℚ) =
    newRowScale r * (if c.val < 54 then (bit v (c.val % 18) : ℚ) / den h v
      else -(num h v : ℚ) * bit v (c.val % 18) / (3 * (den h v : ℚ)^2))
  rw [hs]
  split_ifs <;> push_cast <;> field_simp

theorem rawJacobian_det_ne_zero : rawJacobian.det ≠ 0 := by
  have hm : (newCleared.map (fun a ↦ (a : ℚ))).det ≠ 0 := by
    rw [← Int.cast_det]
    exact_mod_cast newCleared_det_ne_zero
  intro hz
  apply hm
  rw [newCleared_eq, Matrix.det_mul, hz, mul_zero]

def columnScale (c : Fin 108) : ℚ := if c.val < 54 then 1 else 69300

def scaledJacobian : Matrix (Fin 108) (Fin 108) ℚ :=
  rawJacobian * Matrix.diagonal columnScale

theorem scaledJacobian_det_ne_zero : scaledJacobian.det ≠ 0 := by
  rw [scaledJacobian, Matrix.det_mul, Matrix.det_diagonal]
  apply mul_ne_zero rawJacobian_det_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro c _
  simp only [columnScale]
  split_ifs <;> norm_num

theorem active_scores : ∀ r : Fin 108,
    1 + (69300 : ℚ) * (score (newIndices r) - 1) =
      if r = 53 then -1 else 1 := by
  decide +kernel

#print axioms scaledJacobian_det_ne_zero
#print axioms active_scores

end UnitRank
end HeadComplexity.IntegerBinaryFiber
