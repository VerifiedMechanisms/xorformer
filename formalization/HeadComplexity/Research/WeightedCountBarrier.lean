import HeadComplexity.Research.WeightedDegreeOptimization

set_option linter.style.header false

/-!
A finite obstruction for the numerical certificate supplied by normalized
weighted Warren counting. This does not assert that the represented class is
large: it asserts that this particular upper-bound expression is too large.
-/

noncomputable section
namespace HeadComplexity.WeightedCountBarrier
open Finset
open scoped BigOperators

variable {n H : ℕ}

def optimalBase (n H : ℕ) : ℝ :=
  16 * (Real.exp 1) ^ 2 * ((2 : ℝ) ^ n) ^ 2 * ((H : ℝ) - 1) /
    ((n : ℝ) ^ 2 * (H : ℝ) ^ 2)

theorem square_le_two_pow (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Nat.pow_succ 2 n]
    nlinarith

theorem base_ge_cube_size_div_dimension (hn : 0 < n) (hH : 2 ≤ H)
    (hp : 2 * n * H ≤ 2 ^ n) : (2 : ℝ) ^ n / n ≤ optimalBase n H := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hHR : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by linarith
  have hN : 0 < (2 : ℝ) ^ n := by positivity
  have hdim : 2 * (n : ℝ) * H ≤ (2 : ℝ) ^ n := by exact_mod_cast hp
  have hfac : (2 : ℝ) ≤ (2 : ℝ) ^ n / ((n : ℝ) * H) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith [hdim])
  have hhalf : (1 / 2 : ℝ) ≤ ((H : ℝ) - 1) / H :=
    (le_div_iff₀ hHpos).mpr (by linarith)
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have he2 : (1 : ℝ) ≤ 16 * (Real.exp 1) ^ 2 := by nlinarith
  calc
    _ = 1 * ((2 : ℝ) ^ n / n) * 2 * (1 / 2) := by ring
    _ ≤ (16 * (Real.exp 1) ^ 2) * ((2 : ℝ) ^ n / n) *
        ((2 : ℝ) ^ n / ((n : ℝ) * H)) * (((H : ℝ) - 1) / H) := by
      gcongr
    _ = optimalBase n H := by unfold optimalBase; field_simp

/-- If the width is already twice the quadratic-denominator scale, even the
optimized finite certificate exceeds the total number of Boolean tables. -/
theorem optimal_certificate_exceeds_all_tables (hn : 4 ≤ n) (hH : 2 ≤ H)
    (hp : 2 * n * H ≤ 2 ^ n) (hwidth : 2 * 2 ^ n ≤ n ^ 2 * H) :
    (2 : ℝ) ^ (2 ^ n) < 2 * optimalBase n H ^ (n * H) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < (2 : ℝ) ^ n := by positivity
  have hb := base_ge_cube_size_div_dimension (by omega : 0 < n) hH hp
  have hbp : 0 < optimalBase n H := (div_pos hN hnR).trans_le hb
  have hs : (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := by exact_mod_cast square_le_two_pow hn
  have hsq : (2 : ℝ) ^ n ≤ optimalBase n H ^ 2 := by
    have hdiv : (2 : ℝ) ^ n ≤ ((2 : ℝ) ^ n / n) ^ 2 := by
      rw [div_pow]
      apply (le_div_iff₀ (sq_pos_of_pos hnR)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hs hN.le]
    exact hdiv.trans (pow_le_pow_left₀ (by positivity) hb 2)
  have hl := Real.log_le_log hN hsq
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hw : 2 * (2 : ℝ) ^ n ≤ (n : ℝ) ^ 2 * H := by exact_mod_cast hwidth
  have hmul := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ (n : ℝ) * H by positivity)
  have hwlog := mul_le_mul_of_nonneg_right hw hl2.le
  have hexp : (2 : ℝ) ^ n * Real.log 2 ≤
      (n : ℝ) * H * Real.log (optimalBase n H) := by nlinarith
  have he := Real.exp_le_exp.mpr hexp
  have hleft : Real.exp ((2 : ℝ) ^ n * Real.log 2) = (2 : ℝ) ^ (2 ^ n) := by
    rw [show (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) by norm_cast,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hright : Real.exp ((n : ℝ) * H * Real.log (optimalBase n H)) =
      optimalBase n H ^ (n * H) := by
    rw [← Nat.cast_mul, Real.exp_nat_mul, Real.exp_log hbp]
  rw [hleft, hright] at he
  have hpow : 0 < optimalBase n H ^ (n * H) := pow_pos hbp _
  linarith

/-- The optimized certificate already fails at the quadratic scale itself.
The older factor-two threshold above is not needed. -/
theorem optimal_certificate_exceeds_all_tables_at_quadratic_scale
    (hn : 4 ≤ n) (hH : 2 ≤ H)
    (hp : 2 * n * H ≤ 2 ^ n) (hwidth : 2 ^ n ≤ n ^ 2 * H) :
    (2 : ℝ) ^ (2 ^ n) < 2 * optimalBase n H ^ (n * H) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hHR : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hHp : (0 : ℝ) < H := by linarith
  have hN : 0 < (2 : ℝ) ^ n := by positivity
  let U : ℝ := (n : ℝ) ^ 2 * H / (2 : ℝ) ^ n
  have hU : 1 ≤ U := by
    apply (le_div_iff₀ hN).mpr
    simpa only [one_mul] using (show (2 : ℝ) ^ n ≤ (n : ℝ) ^ 2 * H by
      exact_mod_cast hwidth)
  have hUpos : 0 < U := by linarith
  have hdim : 2 * (n : ℝ) * H ≤ (2 : ℝ) ^ n := by exact_mod_cast hp
  have hUupper : U ≤ (n : ℝ) / 2 := by
    apply (div_le_iff₀ hN).mpr
    nlinarith [mul_le_mul_of_nonneg_left hdim hnR.le]
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hhalf : (1 / 2 : ℝ) ≤ ((H : ℝ) - 1) / H :=
    (le_div_iff₀ hHp).mpr (by linarith)
  have hfactor : 1 ≤ 16 * (Real.exp 1) ^ 2 * (((H : ℝ) - 1) / H) := by
    have hs : (1 : ℝ) ≤ (Real.exp 1) ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hhalf
      (show 0 ≤ 16 * (Real.exp 1) ^ 2 by positivity)
    nlinarith
  have hb : (2 : ℝ) ^ n / U ≤ optimalBase n H := by
    calc
      _ = ((2 : ℝ) ^ n) ^ 2 / ((n : ℝ) ^ 2 * H) * 1 := by
        dsimp [U]
        field_simp
      _ ≤ ((2 : ℝ) ^ n) ^ 2 / ((n : ℝ) ^ 2 * H) *
          (16 * (Real.exp 1) ^ 2 * (((H : ℝ) - 1) / H)) := by
        exact mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = optimalBase n H := by unfold optimalBase; field_simp
  have hbp : 0 < optimalBase n H := (div_pos hN hUpos).trans_le hb
  have hlog := Real.log_le_log (div_pos hN hUpos) hb
  rw [Real.log_div hN.ne' hUpos.ne', Real.log_pow] at hlog
  have hlogU : Real.log U ≤ U - 1 := Real.log_le_sub_one_of_pos hUpos
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hAU : U ≤ (n : ℝ) * Real.log 2 := by
    exact hUupper.trans (by nlinarith [mul_le_mul_of_nonneg_left hl2 hnR.le])
  have hprod : 0 ≤ (U - 1) * ((n : ℝ) * Real.log 2 - U) :=
    mul_nonneg (by linarith) (by linarith)
  have hUlog : (n : ℝ) * Real.log 2 ≤ U * Real.log (optimalBase n H) := by
    have hh := mul_le_mul_of_nonneg_left
      (show (n : ℝ) * Real.log 2 - U + 1 ≤ Real.log (optimalBase n H) by
        linarith) hUpos.le
    nlinarith
  have hscale : (2 : ℝ) ^ n / n * U = (n : ℝ) * H := by
    dsimp [U]
    field_simp
  have hexp : (2 : ℝ) ^ n * Real.log 2 ≤
      (n : ℝ) * H * Real.log (optimalBase n H) := by
    have hh := mul_le_mul_of_nonneg_left hUlog (div_pos hN hnR).le
    calc
      _ = ((2 : ℝ) ^ n / n) * ((n : ℝ) * Real.log 2) := by field_simp
      _ ≤ ((2 : ℝ) ^ n / n) * (U * Real.log (optimalBase n H)) := hh
      _ = _ := by rw [← mul_assoc, hscale]
  have hleft : Real.exp ((2 : ℝ) ^ n * Real.log 2) = (2 : ℝ) ^ (2 ^ n) := by
    rw [show (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) by norm_cast,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hright : Real.exp ((n : ℝ) * H * Real.log (optimalBase n H)) =
      optimalBase n H ^ (n * H) := by
    rw [← Nat.cast_mul, Real.exp_nat_mul, Real.exp_log hbp]
  have hh := Real.exp_le_exp.mpr hexp
  rw [hleft, hright] at hh
  have hpow : 0 < optimalBase n H ^ (n * H) := pow_pos hbp _
  linarith

/-- Every positive block-weight choice has a numerical certificate at least
as large as the optimized one. The degree-cap premise is explicit. -/
theorem every_block_certificate_ge_optimal (hn : 0 < n) (hH : 2 ≤ H)
    (w u : Fin H → ℝ) (D : ℝ)
    (hw : ∀ i, 0 < w i) (hu : ∀ i, 0 < u i)
    (hcap : ∀ i, u i + (∑ j, w j) - w i ≤ D) :
    2 * optimalBase n H ^ (n * H) ≤
      2 * (4 * Real.exp 1 * D * (2 : ℝ) ^ n / (2 * n * H)) ^ (2 * n * H) /
        ((∏ i, w i) * (∏ i, u i)) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hHR : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by linarith
  let A : ℝ := 4 * Real.exp 1 * (2 : ℝ) ^ n / (2 * n * H)
  let P : ℝ := (∏ i, w i) * (∏ i, u i)
  have hP : 0 < P := mul_pos (prod_pos (fun i _ ↦ hw i)) (prod_pos (fun i _ ↦ hu i))
  have hratio : (4 * ((H : ℝ) - 1)) ^ (n * H) ≤ D ^ (2 * n * H) / P ^ n := by
    apply (le_div_iff₀ (pow_pos hP _)).mpr
    simpa only [P, mul_comm] using
      WeightedDegreeOptimization.degree_ratio_lower (n := n) hH w u D hw hu hcap
  have hb : optimalBase n H = A ^ 2 * (4 * ((H : ℝ) - 1)) := by
    dsimp [optimalBase, A]
    field_simp
    ring
  have hd : 4 * Real.exp 1 * D * (2 : ℝ) ^ n / (2 * n * H) = A * D := by
    dsimp [A]
    ring
  have hexp : 2 * n * H = 2 * (n * H) := by ring
  calc
    2 * optimalBase n H ^ (n * H) =
        2 * A ^ (2 * n * H) * (4 * ((H : ℝ) - 1)) ^ (n * H) := by
      rw [hb, mul_pow, ← pow_mul, hexp]
      ring
    _ ≤ 2 * A ^ (2 * n * H) * (D ^ (2 * n * H) / P ^ n) := by
      exact mul_le_mul_of_nonneg_left hratio (by dsimp [A]; positivity)
    _ = _ := by rw [hd, mul_pow]; ring

/-- Changing positive weights cannot make this particular counting formula
exclude even one truth table once the stated finite width threshold holds. -/
theorem every_block_certificate_exceeds_all_tables (hn : 4 ≤ n) (hH : 2 ≤ H)
    (hp : 2 * n * H ≤ 2 ^ n) (hwidth : 2 * 2 ^ n ≤ n ^ 2 * H)
    (w u : Fin H → ℝ) (D : ℝ)
    (hw : ∀ i, 0 < w i) (hu : ∀ i, 0 < u i)
    (hcap : ∀ i, u i + (∑ j, w j) - w i ≤ D) :
    (2 : ℝ) ^ (2 ^ n) <
      2 * (4 * Real.exp 1 * D * (2 : ℝ) ^ n / (2 * n * H)) ^ (2 * n * H) /
        ((∏ i, w i) * (∏ i, u i)) ^ n :=
  (optimal_certificate_exceeds_all_tables hn hH hp hwidth).trans_le
    (every_block_certificate_ge_optimal (by omega) hH w u D hw hu hcap)

theorem every_block_certificate_exceeds_all_tables_at_quadratic_scale
    (hn : 4 ≤ n) (hH : 2 ≤ H)
    (hp : 2 * n * H ≤ 2 ^ n) (hwidth : 2 ^ n ≤ n ^ 2 * H)
    (w u : Fin H → ℝ) (D : ℝ)
    (hw : ∀ i, 0 < w i) (hu : ∀ i, 0 < u i)
    (hcap : ∀ i, u i + (∑ j, w j) - w i ≤ D) :
    (2 : ℝ) ^ (2 ^ n) <
      2 * (4 * Real.exp 1 * D * (2 : ℝ) ^ n / (2 * n * H)) ^ (2 * n * H) /
        ((∏ i, w i) * (∏ i, u i)) ^ n :=
  (optimal_certificate_exceeds_all_tables_at_quadratic_scale hn hH hp hwidth).trans_le
    (every_block_certificate_ge_optimal (by omega) hH w u D hw hu hcap)

end HeadComplexity.WeightedCountBarrier
