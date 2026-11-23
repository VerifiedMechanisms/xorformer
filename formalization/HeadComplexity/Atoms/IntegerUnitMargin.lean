import HeadComplexity.Atoms.IntegerUnitCube
import HeadComplexity.Atoms.IntegerUnitRank

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace HeadComplexity.IntegerBinaryFiber
namespace UnitMargin
open scoped BigOperators

def rawP (v : ℕ) : ℤ :=
  num 0 v * den 1 v * den 2 v + num 1 v * den 0 v * den 2 v +
    num 2 v * den 0 v * den 1 v

def rawD (v : ℕ) : ℤ := 3 * den 0 v * den 1 v * den 2 v

theorem den_positive (h : Fin 3) (v : ℕ) : 0 < den h v := by
  have hs : 0 ≤ dot (denominatorSlopes h) v := by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (slopes_positive h i).le
    exact Int.natCast_nonneg _
  change 0 < 1 + dot (denominatorSlopes h) v
  linarith

theorem rawD_positive (v : ℕ) : 0 < rawD v := by
  unfold rawD
  exact mul_pos (mul_pos (mul_pos (by norm_num) (den_positive 0 v))
    (den_positive 1 v)) (den_positive 2 v)

theorem integer_gap (v : Fin (2^18)) :
    0 ≤ rawP v.val ∨ 34650 * rawP v.val ≤ -rawD v.val := by
  let k : Fin 512 := ⟨v.val / 512, by have := v.isLt; norm_num at this ⊢; omega⟩
  let j : Fin 512 := ⟨v.val % 512, Nat.mod_lt _ (by decide)⟩
  have hv : 512 * k.val + j.val = v.val := by dsimp [k, j]; omega
  have hg := UnitCube.cached_gap k j
  simpa only [UnitCube.cachedP, UnitCube.cachedD, UnitCube.cachedDen_eq,
    UnitCube.cachedNum_eq, hv, rawP, rawD] using hg

theorem raw_fraction (v : ℕ) : score v - 1 = (rawP v : ℚ) / rawD v := by
  have hd : ∀ h : Fin 3, (den h v : ℚ) ≠ 0 := by
    intro h
    exact_mod_cast (den_positive h v).ne'
  simp only [score, add_sub_cancel_left, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  unfold rawP rawD
  push_cast
  field_simp [hd 0, hd 1, hd 2]
  <;> ring

def scaledScore (v : ℕ) : ℚ := 1 + 69300 * (score v - 1)

theorem full_cube_unit_margin (v : Fin (2^18)) :
    1 ≤ scaledScore v.val ∨ scaledScore v.val ≤ -1 := by
  have hd : (0 : ℚ) < rawD v.val := by exact_mod_cast rawD_positive v.val
  rw [scaledScore, raw_fraction]
  rcases integer_gap v with hp | hp
  · left
    have hp' : (0 : ℚ) ≤ rawP v.val := by exact_mod_cast hp
    have : (0 : ℚ) ≤ (rawP v.val : ℚ) / rawD v.val := div_nonneg hp' hd.le
    linarith
  · right
    have hp' : (34650 : ℚ) * rawP v.val ≤ -(rawD v.val : ℚ) := by exact_mod_cast hp
    have hq : (rawP v.val : ℚ) / rawD v.val ≤ -(1 / 34650 : ℚ) := by
      apply (div_le_iff₀ hd).mpr
      linarith
    linarith

theorem origin_value : scaledScore 0 = 1 := by decide +kernel

theorem active_values : ∀ r : Fin 108,
    scaledScore (UnitRank.newIndices r) = if r = 53 then -1 else 1 :=
  UnitRank.active_scores

#print axioms full_cube_unit_margin
#print axioms active_values
#print axioms UnitRank.scaledJacobian_det_ne_zero

end UnitMargin
end HeadComplexity.IntegerBinaryFiber
