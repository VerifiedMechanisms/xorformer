import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option linter.style.header false

/-! # Standard rotary frequencies and their distinct complex exponential nodes -/

namespace HeadComplexity.RoPEFrequencies

noncomputable section

def frequency (m : ℕ) (r : Fin m) : ℝ :=
  Real.rpow 10000 (-(r.val : ℝ) / (m : ℝ))

theorem frequency_pos (m : ℕ) (r : Fin m) : 0 < frequency m r := by
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem frequency_le_one {m : ℕ} (hm : 0 < m) (r : Fin m) : frequency m r ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) hm'.le

theorem frequency_injective {m : ℕ} (hm : 0 < m) : Function.Injective (frequency m) := by
  intro r s h
  have he := (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 10000)
    (by norm_num : (10000 : ℝ) ≠ 1)).mp h
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hv : (r.val : ℝ) = (s.val : ℝ) := by
    exact neg_injective ((div_left_inj' hm').mp he)
  apply Fin.ext
  exact_mod_cast hv

def node (m : ℕ) (r : Fin m) : ℂ :=
  Complex.exp ((frequency m r : ℂ) * Complex.I)

@[simp] theorem node_exp (m : ℕ) (r : Fin m) :
    node m r = Complex.exp ((frequency m r : ℂ) * Complex.I) := rfl

theorem node_ne_zero (m : ℕ) (r : Fin m) : node m r ≠ 0 :=
  Complex.exp_ne_zero _

theorem node_injective {m : ℕ} (hm : 0 < m) : Function.Injective (node m) := by
  intro r s h
  have hp : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  have hr := frequency_pos m r
  have hs := frequency_pos m s
  have hr' := frequency_le_one hm r
  have hs' := frequency_le_one hm s
  have he : (frequency m r : ℂ) * Complex.I = (frequency m s : ℂ) * Complex.I := by
    apply Complex.exp_inj_of_neg_pi_lt_of_le_pi
    · simpa using (show -Real.pi < frequency m r by linarith)
    · simpa using hr'.trans hp.le
    · simpa using (show -Real.pi < frequency m s by linarith)
    · simpa using hs'.trans hp.le
    · exact h
  apply frequency_injective hm
  simpa using congrArg Complex.im he

/-- The usual exponent `-2r/d` at width `d=2m` is exactly this schedule. -/
theorem frequency_standard_schedule (m : ℕ) (r : Fin m) :
    frequency m r = Real.rpow 10000 (-2 * (r.val : ℝ) / (2 * (m : ℝ))) := by
  unfold frequency
  congr 1
  ring

end
end HeadComplexity.RoPEFrequencies
