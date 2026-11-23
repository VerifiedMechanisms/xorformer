import HeadComplexity.Atoms.UnitMinimumCenterCube

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace HeadComplexity.UnitMinimumCenter
open scoped BigOperators
open IntegerBinaryFiber (bit dot)

def rawP (v : ℕ) : ℤ :=
  num 0 v * den 1 v * den 2 v + num 1 v * den 0 v * den 2 v +
    num 2 v * den 0 v * den 1 v

def rawQ (v : ℕ) : ℤ := den 0 v * den 1 v * den 2 v

def gamma : ℚ := 2373357636515531 / 125000000000000000000

def score (v : ℕ) : ℚ := ∑ h : Fin 3, (num h v : ℚ) / den h v

theorem bit_le_one (v i : ℕ) : bit v i ≤ 1 := by
  have hh : (v / 2^i) % 2 ≤ 1 := by omega
  unfold bit
  exact_mod_cast hh

theorem den_ge_endpoint (h : Fin 3) (v : ℕ) : den h 262143 ≤ den h v := by
  have hone : ∀ i : Fin 18, bit 262143 i.val = 1 := by decide +kernel
  unfold den dot
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  rw [hone i, mul_one]
  simpa using mul_le_mul_of_nonpos_left (bit_le_one v i.val) (slope_bounds h i).1.le

theorem den_positive (h : Fin 3) (v : ℕ) : 0 < den h v := by
  have hh := denominator_endpoint_bounds h
  have hs : (0 : ℤ) < scale := by decide
  have hm := den_ge_endpoint h v
  omega

theorem rawQ_positive (v : ℕ) : 0 < rawQ v := by
  exact mul_pos (mul_pos (den_positive 0 v) (den_positive 1 v)) (den_positive 2 v)

theorem integer_gap_or_selected (v : Fin (2^18)) :
    rawQ v.val ≤ 100000000 * rawP v.val ∨
    100000000 * (125000000000000000000 * rawP v.val +
      2373357636515531 * rawQ v.val) ≤ -125000000000000000000 * rawQ v.val ∨
    v.val = 0 ∨ ∃ r, indices r = v.val := by
  let k : Fin 512 := ⟨v.val / 512, by have := v.isLt; norm_num at this ⊢; omega⟩
  let j : Fin 512 := ⟨v.val % 512, Nat.mod_lt _ (by decide)⟩
  have hv : 512 * k.val + j.val = v.val := by dsimp [k, j]; omega
  have hg := cached_gap k j
  simpa only [gapOrSelected, cachedP, cachedQ, cachedDen_eq, cachedNum_eq,
    hv, rawP, rawQ, activeList_mem_iff] using hg

theorem score_fraction (v : ℕ) : score v = (rawP v : ℚ) / rawQ v := by
  have hd : ∀ h : Fin 3, (den h v : ℚ) ≠ 0 := by
    intro h
    exact_mod_cast (den_positive h v).ne'
  simp only [score, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  unfold rawP rawQ
  push_cast
  field_simp [hd 0, hd 1, hd 2]
  <;> ring

theorem unselected_score_gap (v : Fin (2^18)) (hv : v.val ≠ 0)
    (ha : ¬ ∃ r, indices r = v.val) :
    (1 / 100000000 : ℚ) ≤ score v.val ∨ score v.val ≤ -gamma - 1 / 100000000 := by
  have hq : (0 : ℚ) < rawQ v.val := by exact_mod_cast rawQ_positive v.val
  rw [score_fraction]
  rcases integer_gap_or_selected v with hp | hp | hzero | hactive
  · left
    apply (le_div_iff₀ hq).mpr
    have hh : (rawQ v.val : ℚ) ≤ 100000000 * rawP v.val := by exact_mod_cast hp
    linarith
  · right
    apply (div_le_iff₀ hq).mpr
    have hh : (100000000 : ℚ) * (125000000000000000000 * rawP v.val +
        2373357636515531 * rawQ v.val) ≤ -125000000000000000000 * rawQ v.val := by
      exact_mod_cast hp
    unfold gamma
    linarith
  · exact (hv hzero).elim
  · exact (ha hactive).elim

theorem active_residual : ∀ r : Fin 108,
    |score (indices r) + if labels r < 0 then gamma else 0| < (1 / 10^60 : ℚ) := by
  decide +kernel

theorem origin_score : score 0 = 0 := by decide +kernel

#print axioms unselected_score_gap
#print axioms active_residual

end HeadComplexity.UnitMinimumCenter
