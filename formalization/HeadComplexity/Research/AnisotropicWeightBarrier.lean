import HeadComplexity.Research.WeightedCountBarrier

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.AnisotropicWeightBarrier
open Finset
open scoped BigOperators
variable {n H : ℕ}

/-- Coordinatewise weights cannot have a larger product than their block
maxima, each repeated n times. -/
theorem product_coordinates_le (w u : Fin H → Fin n → ℝ) (W U : Fin H → ℝ)
    (hw : ∀ h i, 0 < w h i) (hu : ∀ h i, 0 < u h i)
    (hW : ∀ h, 0 < W h) (hU : ∀ h, 0 < U h)
    (hwW : ∀ h i, w h i ≤ W h) (huU : ∀ h i, u h i ≤ U h) :
    (∏ h, ∏ i, w h i) * (∏ h, ∏ i, u h i) ≤
      ((∏ h, W h) * (∏ h, U h))^n := by
  have hwprod : (∏ h, ∏ i, w h i) ≤ (∏ h, W h)^n := by
    calc
      _ ≤ ∏ h, ∏ _i : Fin n, W h := by
        apply Finset.prod_le_prod₀
        · intro h _; exact Finset.prod_nonneg (fun i _ => (hw h i).le)
        · intro h _
          exact Finset.prod_le_prod₀ (fun i _ => (hw h i).le) (fun i _ => hwW h i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_fin, Finset.prod_pow]
  have huprod : (∏ h, ∏ i, u h i) ≤ (∏ h, U h)^n := by
    calc
      _ ≤ ∏ h, ∏ _i : Fin n, U h := by
        apply Finset.prod_le_prod₀
        · intro h _; exact Finset.prod_nonneg (fun i _ => (hu h i).le)
        · intro h _
          exact Finset.prod_le_prod₀ (fun i _ => (hu h i).le) (fun i _ => huU h i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_fin, Finset.prod_pow]
  rw [mul_pow]
  exact mul_le_mul hwprod huprod
    (Finset.prod_nonneg fun h _ => Finset.prod_nonneg fun i _ => (hu h i).le)
    (pow_nonneg (Finset.prod_nonneg fun h _ => (hW h).le) _)

/-- The sharp block optimization already bounds every coordinate grading
whose block maxima obey the cleared-score monomial degree constraints. -/
theorem coordinate_degree_ratio_lower (hH : 2 ≤ H)
    (w u : Fin H → Fin n → ℝ) (W U : Fin H → ℝ) (D : ℝ)
    (hw : ∀ h i, 0 < w h i) (hu : ∀ h i, 0 < u h i)
    (hW : ∀ h, 0 < W h) (hU : ∀ h, 0 < U h)
    (hwW : ∀ h i, w h i ≤ W h) (huU : ∀ h i, u h i ≤ U h)
    (hcap : ∀ h, U h+(∑ j, W j)-W h ≤ D) :
    ((∏ h, ∏ i, w h i)*(∏ h, ∏ i, u h i)) *
      (4*((H : ℝ)-1))^(n*H) ≤ D^(2*n*H) := by
  have hHR : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hprod := product_coordinates_le w u W U hw hu hW hU hwW huU
  have hbase : 0 ≤ 4*((H : ℝ)-1) := by linarith
  have hb : 0 ≤ (4*((H : ℝ)-1))^(n*H) := pow_nonneg hbase _
  exact (mul_le_mul_of_nonneg_right hprod hb).trans
    (WeightedDegreeOptimization.degree_ratio_lower hH W U D hW hU hcap)

/-- Direct comparison with the optimal unrestricted weighted certificate.
The degree-envelope hypothesis is explicit. -/
theorem every_coordinate_certificate_ge_optimal (hn : 0 < n) (hH : 2 ≤ H)
    (w u : Fin H → Fin n → ℝ) (W U : Fin H → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hw : ∀ h i, 0 < w h i) (hu : ∀ h i, 0 < u h i)
    (hW : ∀ h, 0 < W h) (hU : ∀ h, 0 < U h)
    (hwW : ∀ h i, w h i ≤ W h) (huU : ∀ h i, u h i ≤ U h)
    (hcap : ∀ h, U h+(∑ j, W j)-W h ≤ D) :
    2*WeightedCountBarrier.optimalBase n H^(n*H) ≤
      2*(4*Real.exp 1*D*(2 : ℝ)^n/(2*n*H))^(2*n*H) /
        ((∏ h, ∏ i, w h i)*(∏ h, ∏ i, u h i)) := by
  have hprod := product_coordinates_le w u W U hw hu hW hU hwW huU
  have hp : 0 < (∏ h, ∏ i, w h i)*(∏ h, ∏ i, u h i) :=
    mul_pos (Finset.prod_pos fun h _ => Finset.prod_pos fun i _ => hw h i)
      (Finset.prod_pos fun h _ => Finset.prod_pos fun i _ => hu h i)
  exact (WeightedCountBarrier.every_block_certificate_ge_optimal
    hn hH W U D hW hU hcap).trans
    (div_le_div_of_nonneg_left (by positivity) hp hprod)

/-- No positive coordinate grading of this chart can certify a missing table
at or above the quadratic width scale. -/
theorem every_coordinate_certificate_exceeds_all_tables
    (hn : 4 ≤ n) (hH : 2 ≤ H) (hp : 2*n*H ≤ 2^n) (hwidth : 2^n ≤ n^2*H)
    (w u : Fin H → Fin n → ℝ) (W U : Fin H → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hw : ∀ h i, 0 < w h i) (hu : ∀ h i, 0 < u h i)
    (hW : ∀ h, 0 < W h) (hU : ∀ h, 0 < U h)
    (hwW : ∀ h i, w h i ≤ W h) (huU : ∀ h i, u h i ≤ U h)
    (hcap : ∀ h, U h+(∑ j, W j)-W h ≤ D) :
    (2 : ℝ)^(2^n) <
      2*(4*Real.exp 1*D*(2 : ℝ)^n/(2*n*H))^(2*n*H) /
        ((∏ h, ∏ i, w h i)*(∏ h, ∏ i, u h i)) :=
  (WeightedCountBarrier.optimal_certificate_exceeds_all_tables_at_quadratic_scale
    hn hH hp hwidth).trans_le
    (every_coordinate_certificate_ge_optimal (by omega) hH w u W U D hD
      hw hu hW hU hwW huU hcap)

end HeadComplexity.AnisotropicWeightBarrier
