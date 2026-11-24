import HeadComplexity.Research.WeightedNormalizedCounting

set_option linter.style.header false

/-!
The scalar optimization behind every positive block-weight choice for the
normalized cleared score. This is an obstruction to improving that particular
weighted degree estimate, not an upper bound on original head complexity.
-/

noncomputable section
namespace HeadComplexity.WeightedDegreeOptimization
open Finset
open scoped BigOperators

variable {H n : ℕ}

/-- The ordinary finite AM-GM inequality, in the form needed for block weights. -/
theorem product_le_mean_pow (hH : 0 < H) (v : Fin H → ℝ)
    (hv : ∀ i, 0 < v i) :
    (∏ i, v i) ≤ ((∑ i, v i) / H) ^ H := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hsum : 0 < ∑ i, v i := Finset.sum_pos (fun i _ ↦ hv i)
    (by exact ⟨⟨0, hH⟩, Finset.mem_univ _⟩)
  let m : ℝ := (∑ i, v i) / H
  have hm : 0 < m := div_pos hsum hHR
  have hlog (i : Fin H) : Real.log (v i) ≤ Real.log m + v i / m - 1 := by
    have hh := Real.log_le_sub_one_of_pos (div_pos (hv i) hm)
    rw [Real.log_div (hv i).ne' hm.ne'] at hh
    linarith
  have hlogs : (∑ i, Real.log (v i)) ≤ (H : ℝ) * Real.log m := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hlog i)
    simp only [sum_sub_distrib, sum_add_distrib, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, ← sum_div] at hh
    have hmean : (∑ i, v i) / m = H := by dsimp [m]; field_simp
    rw [hmean] at hh
    linarith
  calc
    (∏ i, v i) = Real.exp (∑ i, Real.log (v i)) := by
      rw [Real.exp_sum]
      simp_rw [Real.exp_log (hv _)]
    _ ≤ Real.exp ((H : ℝ) * Real.log m) := Real.exp_le_exp.mpr hlogs
    _ = m ^ H := by rw [Real.exp_nat_mul, Real.exp_log hm]

/-- A weighted degree cap bounds the two block means. -/
theorem mean_product_le (hH : 2 ≤ H) (w u : Fin H → ℝ) (D : ℝ)
    (hw : ∀ i, 0 < w i) (hu : ∀ i, 0 < u i)
    (hcap : ∀ i, u i + (∑ j, w j) - w i ≤ D) :
    ((∑ i, w i) / H) * ((∑ i, u i) / H) ≤
      D ^ 2 / (4 * ((H : ℝ) - 1)) := by
  have hHR : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by linarith
  have hHm : 0 < (H : ℝ) - 1 := by linarith
  have hW : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ ↦ (hw i).le)
  have hU : 0 ≤ ∑ i, u i := Finset.sum_nonneg (fun i _ ↦ (hu i).le)
  have hc := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hcap i)
  simp only [sum_sub_distrib, sum_add_distrib, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hc
  have hmul := mul_le_mul_of_nonneg_left hc hW
  have hquad := sq_nonneg ((H : ℝ) * D - 2 * ((H : ℝ) - 1) * (∑ i, w i))
  have hmain : 4 * ((H : ℝ) - 1) * (∑ i, w i) * (∑ i, u i) ≤
      (H : ℝ) ^ 2 * D ^ 2 := by nlinarith
  apply (le_div_iff₀ (by positivity : 0 < 4 * ((H : ℝ) - 1))).mpr
  field_simp
  nlinarith

/-- Among all head-block weights, the product at a fixed degree is maximized
by the same balanced choice used by the unrestricted weighted count. -/
theorem product_blocks_le (hH : 2 ≤ H) (w u : Fin H → ℝ) (D : ℝ)
    (hw : ∀ i, 0 < w i) (hu : ∀ i, 0 < u i)
    (hcap : ∀ i, u i + (∑ j, w j) - w i ≤ D) :
    (∏ i, w i) * (∏ i, u i) ≤
      (D ^ 2 / (4 * ((H : ℝ) - 1))) ^ H := by
  have hHpos : 0 < H := by omega
  have hW : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ ↦ (hw i).le)
  have hU : 0 ≤ ∑ i, u i := Finset.sum_nonneg (fun i _ ↦ (hu i).le)
  have hwmean := product_le_mean_pow hHpos w hw
  have humean := product_le_mean_pow hHpos u hu
  calc
    _ ≤ ((∑ i, w i) / H) ^ H * ((∑ i, u i) / H) ^ H :=
      mul_le_mul hwmean humean (Finset.prod_nonneg (fun i _ ↦ (hu i).le)) (by positivity)
    _ = (((∑ i, w i) / H) * ((∑ i, u i) / H)) ^ H := (mul_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (mean_product_le hH w u D hw hu hcap) H

/-- Repeating each head-block weight `n` times cannot remove the factor
`(4*(H-1))^(n*H)` from the weighted-degree ratio. -/
theorem degree_ratio_lower (hH : 2 ≤ H) (w u : Fin H → ℝ) (D : ℝ)
    (hw : ∀ i, 0 < w i) (hu : ∀ i, 0 < u i)
    (hcap : ∀ i, u i + (∑ j, w j) - w i ≤ D) :
    ((∏ i, w i) * (∏ i, u i)) ^ n *
      (4 * ((H : ℝ) - 1)) ^ (n * H) ≤ D ^ (2 * n * H) := by
  have hHR : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hHm : 0 < (H : ℝ) - 1 := by linarith
  have hwprod : 0 < ∏ i, w i := Finset.prod_pos (fun i _ ↦ hw i)
  have huprod : 0 < ∏ i, u i := Finset.prod_pos (fun i _ ↦ hu i)
  have hbase : 0 < 4 * ((H : ℝ) - 1) := by positivity
  have hh := pow_le_pow_left₀
    (show 0 ≤ (∏ i, w i) * (∏ i, u i) by positivity)
    (product_blocks_le hH w u D hw hu hcap) n
  have hpow : ((D ^ 2 / (4 * ((H : ℝ) - 1))) ^ H) ^ n =
      D ^ (2 * n * H) / (4 * ((H : ℝ) - 1)) ^ (n * H) := by
    rw [← pow_mul, div_pow, ← pow_mul]
    congr 1 <;> congr 1 <;> ring
  rw [hpow] at hh
  exact (le_div_iff₀ (pow_pos hbase _)).mp hh

/-- Uniform numerator weighting already attains the optimum. -/
theorem uniform_weight_identity (a k : ℝ) (hk : 0 < k) :
    (a + k) ^ 2 / k = 4 * a + (k - a) ^ 2 / k := by
  field_simp
  ring

end HeadComplexity.WeightedDegreeOptimization
