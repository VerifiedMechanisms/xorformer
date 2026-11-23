import HeadComplexity.Results.AxisZeroTransfer
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Defs

set_option linter.style.header false

/-!
# Conditional logarithmic consequences of the audited transfer

All logarithms here are natural. The central compiler hypotheses remain
explicit; these theorems do not assert that a sublinear compiler exists.
-/

namespace HeadComplexity
namespace AxisZeroGluing

open Filter Asymptotics
open scoped Topology

theorem square_le_two_pow_half {n : ℕ} (hn : 32 ≤ n) : n ^ 2 ≤ 2 ^ (n / 2) := by
  have haux (m : ℕ) (hm : 16 ≤ m) : (2 * m + 1) ^ 2 ≤ 2 ^ m := by
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      rw [pow_succ 2 m]
      have hstep : (2 * (m + 1) + 1) ^ 2 ≤ 2 * (2 * m + 1) ^ 2 := by
        nlinarith
      nlinarith
  have hhalf : 16 ≤ n / 2 := by omega
  have hnle : n ≤ 2 * (n / 2) + 1 := by omega
  have hsq : n ^ 2 ≤ (2 * (n / 2) + 1) ^ 2 := by nlinarith
  exact hsq.trans (haux (n / 2) hhalf)

/-- The balanced product cover has the required quadratic denominator, with
an absolute constant independent of parity. -/
theorem balanced_product_lower {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ 2 ≤ 8 * (n / 2 : ℕ) * (n - n / 2 : ℕ) := by
  have hleft : (n : ℝ) ≤ 4 * (n / 2 : ℕ) := by
    exact_mod_cast (show n ≤ 4 * (n / 2) by omega)
  have hright : (n : ℝ) ≤ 2 * (n - n / 2 : ℕ) := by
    exact_mod_cast (show n ≤ 2 * (n - n / 2) by omega)
  have hprod := mul_le_mul hleft hright (by positivity : (0 : ℝ) ≤ n)
    (by positivity : (0 : ℝ) ≤ 4 * (n / 2 : ℕ))
  nlinarith

/-- Both exceptional faces are exponentially cheaper than the main budget.
This explicit bound is sufficient for every saving factor at most `n`. -/
theorem balanced_faces_le {n : ℕ} (hn : 32 ≤ n) :
    (2 : ℝ) ^ (n / 2) + 2 ^ (n - n / 2) ≤ 2 * 2 ^ n / (n : ℝ) ^ 2 := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hhalf : n / 2 ≤ n - n / 2 := by omega
  have hp : (2 : ℝ) ^ (n / 2) ≤ 2 ^ (n - n / 2) :=
    pow_le_pow_right₀ (by norm_num) hhalf
  have hsq : (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ (n / 2) := by
    exact_mod_cast square_le_two_pow_half hn
  apply (le_div_iff₀ (sq_pos_of_pos hnpos)).mpr
  have hpow : (2 : ℝ) ^ n = 2 ^ (n / 2) * 2 ^ (n - n / 2) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.div_le_self n 2)]
  rw [hpow]
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg (n : ℝ)),
    mul_nonneg (sub_nonneg.mpr hsq) (show (0 : ℝ) ≤ 2 ^ (n - n / 2) by positivity)]

/-- Quantitative balanced transfer for an arbitrary positive saving factor
bounded by the dimension. The bound includes every correction head. -/
theorem worstCaseHeadComplexity_balanced_le {n M : ℕ} {K d : ℝ}
    (hn : 32 ≤ n) (hK : 0 ≤ K) (hd : 0 < d) (hdn : d ≤ n)
    (hcompiler : HasReverseAxisCompiler (n / 2) (n - n / 2) M)
    (hbudget : (M : ℝ) ≤ K * n / d) :
    (worstCaseHeadComplexity n : ℝ) ≤ (3872 * K + 2) * 2 ^ n / ((n : ℝ) * d) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have ha : 0 < n / 2 := by omega
  have hb : 0 < n - n / 2 := by omega
  have ha' : (0 : ℝ) < (n / 2 : ℕ) := by exact_mod_cast ha
  have hb' : (0 : ℝ) < (n - n / 2 : ℕ) := by exact_mod_cast hb
  have hab : n / 2 + (n - n / 2) = n := Nat.add_sub_of_le (Nat.div_le_self n 2)
  have htransfer := worstCaseHeadComplexity_real_le_of_reverse_axis_compiler ha hb hcompiler
  rw [hab] at htransfer
  have hmain : 484 * (2 : ℝ) ^ n * M /
        ((n / 2 : ℕ) * (n - n / 2 : ℕ)) ≤ 3872 * K * 2 ^ n / ((n : ℝ) * d) := by
    have hprod := balanced_product_lower (show 2 ≤ n by omega)
    apply (div_le_div_iff₀ (mul_pos ha' hb') (mul_pos hnpos hd)).mpr
    have hbudget' : (M : ℝ) * d ≤ K * n := (le_div_iff₀ hd).mp hbudget
    have hmul := mul_le_mul_of_nonneg_left hbudget' (show 0 ≤ (n : ℝ) by positivity)
    have hprodK := mul_le_mul_of_nonneg_left hprod hK
    have hcore : (M : ℝ) * ((n : ℝ) * d) ≤
        8 * K * ((n / 2 : ℕ) * (n - n / 2 : ℕ)) := by
      nlinarith
    have := mul_le_mul_of_nonneg_left hcore (show 0 ≤ 484 * (2 : ℝ) ^ n by positivity)
    nlinarith
  have hfaces : (2 : ℝ) ^ (n / 2) + 2 ^ (n - n / 2) ≤
      2 * 2 ^ n / ((n : ℝ) * d) := by
    apply (balanced_faces_le hn).trans
    apply div_le_div_of_nonneg_left (by positivity) (mul_pos hnpos hd)
    nlinarith
  calc
    (worstCaseHeadComplexity n : ℝ) ≤
        484 * (2 : ℝ) ^ n * M / ((n / 2 : ℕ) * (n - n / 2 : ℕ)) +
          (2 ^ (n / 2) + 2 ^ (n - n / 2)) := by linarith
    _ ≤ 3872 * K * 2 ^ n / ((n : ℝ) * d) + 2 * 2 ^ n / ((n : ℝ) * d) :=
      add_le_add hmain hfaces
    _ = (3872 * K + 2) * 2 ^ n / ((n : ℝ) * d) := by ring

/-- General conditional asymptotic transfer. The hypotheses quantify over
all sufficiently large dimensions and supply the full worst-case compiler. -/
theorem worstCaseHeadComplexity_isBigO_of_compiler {K : ℝ} (hK : 0 ≤ K)
    (saving : ℕ → ℝ)
    (hcompiler : ∀ᶠ n : ℕ in atTop,
      0 < saving n ∧ saving n ≤ n ∧ ∃ M,
        HasReverseAxisCompiler (n / 2) (n - n / 2) M ∧
          (M : ℝ) ≤ K * n / saving n) :
    (fun n : ℕ ↦ (worstCaseHeadComplexity n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (2 : ℝ) ^ n / ((n : ℝ) * saving n)) := by
  apply Asymptotics.IsBigO.of_bound (3872 * K + 2)
  filter_upwards [eventually_ge_atTop (32 : ℕ), hcompiler] with n hn hc
  obtain ⟨hd, hdn, M, hcomp, hbudget⟩ := hc
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbound := worstCaseHeadComplexity_balanced_le hn hK hd hdn hcomp hbudget
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ worstCaseHeadComplexity n),
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n / ((n : ℝ) * saving n))]
  convert hbound using 1; ring

/-- Natural logarithms have the positive sublinear bounds used below. -/
theorem loglog_bounds {n : ℕ} (hn : 4 ≤ n) :
    0 < Real.log (Real.log n) ∧ Real.log (Real.log n) ≤ n := by
  have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hloggt : 1 < Real.log n := by
    have hexp : Real.exp 1 < (n : ℝ) := lt_of_lt_of_le Real.exp_one_lt_three (by linarith)
    simpa using Real.log_lt_log (Real.exp_pos 1) hexp
  refine ⟨Real.log_pos hloggt, ?_⟩
  have hlog := Real.log_le_sub_one_of_pos hnpos
  have hloglog := Real.log_le_sub_one_of_pos (show 0 < Real.log n by linarith)
  linarith

/-- The compiler budget requested in the question, including its additive
constant and shifted logarithm, implies precisely the requested global
log-log asymptotic. The compiler remains an explicit external hypothesis. -/
theorem worstCaseHeadComplexity_isBigO_loglog_of_compiler {K : ℝ} (hK : 0 ≤ K)
    (hcompiler : ∀ᶠ n : ℕ in atTop, ∃ M,
      HasReverseAxisCompiler (n / 2) (n - n / 2) M ∧
        (M : ℝ) ≤ K * (1 + n / Real.log (Real.log ((n : ℝ) + 4)))) :
    (fun n : ℕ ↦ (worstCaseHeadComplexity n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (2 : ℝ) ^ n / ((n : ℝ) * Real.log (Real.log n))) := by
  apply worstCaseHeadComplexity_isBigO_of_compiler (K := 2 * K) (by positivity)
    (fun n ↦ Real.log (Real.log n))
  filter_upwards [eventually_ge_atTop (4 : ℕ), hcompiler] with n hn hc
  obtain ⟨M, hcomp, hbudget⟩ := hc
  obtain ⟨hd, hdn⟩ := loglog_bounds hn
  refine ⟨hd, hdn, M, hcomp, ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hshift : Real.log (Real.log n) ≤ Real.log (Real.log ((n : ℝ) + 4)) :=
    Real.log_le_log hlogpos (Real.log_le_log hnpos (by linarith))
  have hdiv : (n : ℝ) / Real.log (Real.log ((n : ℝ) + 4)) ≤ n / Real.log (Real.log n) :=
    div_le_div_of_nonneg_left hnpos.le hd hshift
  have hone : (1 : ℝ) ≤ n / Real.log (Real.log n) := (le_div_iff₀ hd).mpr (by simpa using hdn)
  have hmul := mul_le_mul_of_nonneg_left (show
      1 + (n : ℝ) / Real.log (Real.log ((n : ℝ) + 4)) ≤
        2 * ((n : ℝ) / Real.log (Real.log n)) by linarith) hK
  have : (M : ℝ) ≤ K * (2 * ((n : ℝ) / Real.log (Real.log n))) := hbudget.trans hmul
  convert this using 1; ring

/-- The corresponding logarithmic local budget gives the stronger global
logarithmic bound, again conditional only on the displayed compiler input. -/
theorem worstCaseHeadComplexity_isBigO_log_of_compiler {K : ℝ} (hK : 0 ≤ K)
    (hcompiler : ∀ᶠ n : ℕ in atTop, ∃ M,
      HasReverseAxisCompiler (n / 2) (n - n / 2) M ∧
        (M : ℝ) ≤ K * (1 + n / Real.log ((n : ℝ) + 4))) :
    (fun n : ℕ ↦ (worstCaseHeadComplexity n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (2 : ℝ) ^ n / ((n : ℝ) * Real.log n)) := by
  apply worstCaseHeadComplexity_isBigO_of_compiler (K := 2 * K) (by positivity)
    (fun n ↦ Real.log n)
  filter_upwards [eventually_ge_atTop (4 : ℕ), hcompiler] with n hn hc
  obtain ⟨M, hcomp, hbudget⟩ := hc
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hdn : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos hnpos
    linarith
  refine ⟨hd, hdn, M, hcomp, ?_⟩
  have hshift : Real.log n ≤ Real.log ((n : ℝ) + 4) := Real.log_le_log hnpos (by linarith)
  have hdiv : (n : ℝ) / Real.log ((n : ℝ) + 4) ≤ n / Real.log n :=
    div_le_div_of_nonneg_left hnpos.le hd hshift
  have hone : (1 : ℝ) ≤ n / Real.log n := (le_div_iff₀ hd).mpr (by simpa using hdn)
  have hmul := mul_le_mul_of_nonneg_left (show
      1 + (n : ℝ) / Real.log ((n : ℝ) + 4) ≤ 2 * ((n : ℝ) / Real.log n) by linarith) hK
  have : (M : ℝ) ≤ K * (2 * ((n : ℝ) / Real.log n)) := hbudget.trans hmul
  convert this using 1; ring

end AxisZeroGluing
end HeadComplexity
