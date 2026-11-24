import HeadComplexity.Results.AxisZeroUnbalancedTransfer
import HeadComplexity.Results.AxisZeroAsymptotics
import Mathlib.Data.Nat.Log

set_option linter.style.header false

/-!
# Conditional log-log transfer from a logarithmic smaller block

The star-face repair permits a block of size `Nat.log 2 n`. This file
checks the complete budget for that choice. The sublinear local compiler
remains an explicit hypothesis; no such compiler is asserted here.
-/

namespace HeadComplexity
namespace AxisZeroGluing

open Filter Asymptotics
open scoped Topology

private theorem twice_le_two_pow (b : ℕ) : 2 * b ≤ 2 ^ b := by
  induction b with
  | zero => norm_num
  | succ b ih =>
    cases b with
    | zero => norm_num
    | succ b =>
      rw [pow_succ]
      nlinarith

/-- Elementary bounds for the logarithmic smaller block. -/
theorem logarithmic_block_bounds {n : ℕ} (hn : 32 ≤ n) :
    0 < Nat.log 2 n ∧ 2 * Nat.log 2 n ≤ n ∧
      2 ^ Nat.log 2 n ≤ n ∧ n < 2 * 2 ^ Nat.log 2 n := by
  have hn0 : n ≠ 0 := by omega
  have hpow := Nat.pow_log_le_self 2 hn0
  have hlt : n < 2 ^ (Nat.log 2 n + 1) :=
    (Nat.log_lt_iff_lt_pow (by norm_num : 1 < (2 : ℕ)) hn0).mp (by omega)
  rw [pow_succ] at hlt
  exact ⟨Nat.log_pos (by norm_num) (by omega),
    (twice_le_two_pow _).trans hpow, hpow, by omega⟩

private theorem cube_le_two_pow {n : ℕ} (hn : 32 ≤ n) :
    (n : ℝ) ^ 3 ≤ (2 : ℝ) ^ n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hsq : (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ (n / 2) := by
    exact_mod_cast square_le_two_pow_half hn
  have hfour : (n : ℝ) ^ 4 ≤ (2 : ℝ) ^ (2 * (n / 2)) := by
    rw [mul_comm 2, pow_mul]
    nlinarith [sq_nonneg ((2 : ℝ) ^ (n / 2) - (n : ℝ) ^ 2)]
  have hpow : (2 : ℝ) ^ (2 * (n / 2)) ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hthree : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1)
      (pow_nonneg (show (0 : ℝ) ≤ n by positivity) 3)]
  exact hthree.trans (hfour.trans hpow)

/-- Both repaired faces cost at most an absolute multiple of `2^n/n^2`
even when the smaller block has only logarithmic size. -/
theorem logarithmic_block_faces_le {n : ℕ} (hn : 32 ≤ n) :
    11 * (2 : ℝ) ^ (n - Nat.log 2 n) / (n - Nat.log 2 n : ℕ) +
      11 * (2 : ℝ) ^ (Nat.log 2 n) / (Nat.log 2 n : ℕ) ≤
        55 * (2 : ℝ) ^ n / (n : ℝ) ^ 2 := by
  let b := Nat.log 2 n
  let a := n - b
  obtain ⟨hb, hhalf, hpow, hlt⟩ := logarithmic_block_bounds hn
  change 0 < b at hb
  change 2 * b ≤ n at hhalf
  change 2 ^ b ≤ n at hpow
  change n < 2 * 2 ^ b at hlt
  have ha : 0 < a := by dsimp [a]; omega
  have hab : a + b = n := by dsimp [a]; omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hna : (n : ℝ) ≤ 2 * a := by
    exact_mod_cast (show n ≤ 2 * a by dsimp [a]; omega)
  have hnb : (n : ℝ) ≤ 2 * (2 : ℝ) ^ b := by exact_mod_cast hlt.le
  have hpb : (2 : ℝ) ^ b ≤ n := by exact_mod_cast hpow
  have hsplit : (2 : ℝ) ^ n = 2 ^ a * 2 ^ b := by rw [← pow_add, hab]
  have hlarge : 11 * (2 : ℝ) ^ a / a ≤ 44 * (2 : ℝ) ^ n / (n : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ ha0 (sq_pos_of_pos hn0)).mpr
    rw [hsplit]
    have hh := mul_le_mul hna hnb hn0.le (by positivity : (0 : ℝ) ≤ 2 * a)
    nlinarith [mul_nonneg (show 0 ≤ 11 * (2 : ℝ) ^ a by positivity)
      (sub_nonneg.mpr hh)]
  have hsmall : 11 * (2 : ℝ) ^ b / b ≤ 11 * (2 : ℝ) ^ n / (n : ℝ) ^ 2 := by
    calc
      11 * (2 : ℝ) ^ b / b ≤ 11 * (n : ℝ) := by
        apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hb1)).mpr
        nlinarith
      _ ≤ 11 * (2 : ℝ) ^ n / (n : ℝ) ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hn0)).mpr
        nlinarith [cube_le_two_pow hn]
  change 11 * (2 : ℝ) ^ a / a + 11 * (2 : ℝ) ^ b / b ≤ _
  calc
    _ ≤ 44 * (2 : ℝ) ^ n / (n : ℝ) ^ 2 +
        11 * (2 : ℝ) ^ n / (n : ℝ) ^ 2 := add_le_add hlarge hsmall
    _ = _ := by ring

/-- A saving on the smaller side is enough; this bound accounts for every
local module and every face-correction head. -/
theorem worstCaseHeadComplexity_logarithmic_block_le {n M : ℕ} {K d : ℝ}
    (hn : 32 ≤ n) (hK : 0 ≤ K) (hd : 0 < d) (hdn : d ≤ n)
    (hcompiler : HasReverseAxisCompiler (n - Nat.log 2 n) (Nat.log 2 n) M)
    (hbudget : (M : ℝ) ≤ K * (Nat.log 2 n : ℕ) / d) :
    (worstCaseHeadComplexity n : ℝ) ≤
      (968 * K + 55) * (2 : ℝ) ^ n / ((n : ℝ) * d) := by
  let b := Nat.log 2 n
  let a := n - b
  obtain ⟨hb, hhalf, _, _⟩ := logarithmic_block_bounds hn
  change 0 < b at hb
  change 2 * b ≤ n at hhalf
  have ha : 0 < a := by dsimp [a]; omega
  have hab : a + b = n := by dsimp [a]; omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hna : (n : ℝ) ≤ 2 * a := by
    exact_mod_cast (show n ≤ 2 * a by dsimp [a]; omega)
  have ht := worstCaseHeadComplexity_real_le_of_reverse_axis_compiler_star_faces_eleven
    ha hb hcompiler
  rw [hab] at ht
  have hmain : 484 * (2 : ℝ) ^ n * M / ((a : ℝ) * b) ≤
      968 * K * (2 : ℝ) ^ n / ((n : ℝ) * d) := by
    apply (div_le_div_iff₀ (mul_pos ha0 hb0) (mul_pos hn0 hd)).mpr
    have hbudget' : (M : ℝ) * d ≤ K * b := (le_div_iff₀ hd).mp hbudget
    have hx := mul_le_mul_of_nonneg_left hbudget' hn0.le
    have hy := mul_le_mul_of_nonneg_left hna (show 0 ≤ K * (b : ℝ) by positivity)
    have hz : (M : ℝ) * ((n : ℝ) * d) ≤ 2 * K * ((a : ℝ) * b) := by nlinarith
    nlinarith [mul_nonneg (show 0 ≤ 484 * (2 : ℝ) ^ n by positivity)
      (sub_nonneg.mpr hz)]
  have hf := logarithmic_block_faces_le hn
  have hfaces : 11 * (2 : ℝ) ^ a / a + 11 * (2 : ℝ) ^ b / b ≤
      55 * (2 : ℝ) ^ n / ((n : ℝ) * d) := by
    apply hf.trans
    apply div_le_div_of_nonneg_left (by positivity) (mul_pos hn0 hd)
    nlinarith
  calc
    (worstCaseHeadComplexity n : ℝ) ≤
        484 * (2 : ℝ) ^ n * M / ((a : ℝ) * b) +
        (11 * (2 : ℝ) ^ a / a + 11 * (2 : ℝ) ^ b / b) := by linarith
    _ ≤ 968 * K * (2 : ℝ) ^ n / ((n : ℝ) * d) +
        55 * (2 : ℝ) ^ n / ((n : ℝ) * d) := add_le_add hmain hfaces
    _ = _ := by ring

/-- With natural logarithms, the integer binary logarithm is eventually
at least `log n`, so its logarithm supplies the desired log-log factor. -/
theorem loglog_le_log_logarithmic_block {n : ℕ} (hn : 32 ≤ n) :
    Real.log (Real.log n) ≤ Real.log (Nat.log 2 n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb3 : 3 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hb3' : (3 : ℝ) ≤ Nat.log 2 n := by exact_mod_cast hb3
  obtain ⟨_, _, _, hupper⟩ := logarithmic_block_bounds hn
  have hupper' : (n : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 n + 1) := by
    rw [pow_succ]
    exact_mod_cast (show n ≤ 2 ^ Nat.log 2 n * 2 by omega)
  have hl := Real.log_le_log hn0 hupper'
  rw [Real.log_pow, Nat.cast_add, Nat.cast_one] at hl
  have htwo : Real.log 2 ≤ (3 / 4 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hm := mul_le_mul_of_nonneg_left htwo
    (show 0 ≤ (Nat.log 2 n : ℝ) + 1 by positivity)
  have hln : Real.log n ≤ Nat.log 2 n := by nlinarith
  exact Real.log_le_log (Real.log_pos (by exact_mod_cast (show 1 < n by omega))) hln

/-- A universal logarithmic saving in the smaller, logarithmic block would
prove the original global target. The compiler premise is still open.
Every other term of this implication is checked in the unchanged model. -/
theorem worstCaseHeadComplexity_isBigO_loglog_of_logarithmic_block_compiler
    {K : ℝ} (hK : 0 ≤ K)
    (hcompiler : ∀ᶠ n : ℕ in atTop, ∃ M,
      HasReverseAxisCompiler (n - Nat.log 2 n) (Nat.log 2 n) M ∧
        (M : ℝ) ≤ K * (1 + (Nat.log 2 n : ℝ) / Real.log (Nat.log 2 n))) :
    (fun n : ℕ ↦ (worstCaseHeadComplexity n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (2 : ℝ) ^ n / ((n : ℝ) * Real.log (Real.log n))) := by
  apply Asymptotics.IsBigO.of_bound (1936 * K + 55)
  filter_upwards [eventually_ge_atTop (32 : ℕ), hcompiler] with n hn hc
  obtain ⟨M, hcomp, hbudget⟩ := hc
  obtain ⟨hd, hdn⟩ := loglog_bounds (show 4 ≤ n by omega)
  have hb : 0 < Nat.log 2 n := (logarithmic_block_bounds hn).1
  have hb0 : (0 : ℝ) < Nat.log 2 n := by exact_mod_cast hb
  have hlogs := loglog_le_log_logarithmic_block hn
  have hdb : Real.log (Real.log n) ≤ (Nat.log 2 n : ℝ) := by
    have hlog := Real.log_le_sub_one_of_pos hb0
    linarith
  have hdiv : (Nat.log 2 n : ℝ) / Real.log (Nat.log 2 n) ≤
      (Nat.log 2 n : ℝ) / Real.log (Real.log n) :=
    div_le_div_of_nonneg_left hb0.le hd hlogs
  have hone : (1 : ℝ) ≤ (Nat.log 2 n : ℝ) / Real.log (Real.log n) :=
    (le_div_iff₀ hd).mpr (by simpa using hdb)
  have hbudget' : (M : ℝ) ≤ (2 * K) * (Nat.log 2 n : ℝ) /
      Real.log (Real.log n) := by
    have hh := mul_le_mul_of_nonneg_left (show
      1 + (Nat.log 2 n : ℝ) / Real.log (Nat.log 2 n) ≤
        2 * ((Nat.log 2 n : ℝ) / Real.log (Real.log n)) by linarith) hK
    have := hbudget.trans hh
    convert this using 1; ring
  have hbound := worstCaseHeadComplexity_logarithmic_block_le hn
    (by positivity : 0 ≤ 2 * K) hd hdn hcomp hbudget'
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ worstCaseHeadComplexity n),
    Real.norm_eq_abs, abs_of_pos (by positivity :
      (0 : ℝ) < 2 ^ n / ((n : ℝ) * Real.log (Real.log n)))]
  convert hbound using 1; ring

end AxisZeroGluing
end HeadComplexity
