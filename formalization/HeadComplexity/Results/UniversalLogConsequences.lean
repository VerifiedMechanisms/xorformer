import HeadComplexity.Results.UniversalLogSaving

set_option linter.style.header false

namespace HeadComplexity

/-- The explicit logarithmic saving applies to every Boolean function in the
unchanged model, by the defining maximum property of worst-case complexity. -/
theorem HStar_real_le_log_saving {n : ℕ} (hn : 32 ≤ n)
    (f : (Fin n → Bool) → Bool) :
    (HStar n f : ℝ) ≤ 2323202 * (2 : ℝ) ^ n / ((n : ℝ) * Real.log n) := by
  have h : (HStar n f : ℝ) ≤ worstCaseHeadComplexity n := by
    exact_mod_cast HStar_le_worstCaseHeadComplexity f
  exact h.trans (worstCaseHeadComplexity_real_le_log_saving hn)

/-- The logarithmic upper bound excludes the previously proposed matching
lower alternative with any fixed positive constant. -/
theorem not_worstCaseHeadComplexity_eventual_linear_lower :
    ¬ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
      c * (2 : ℝ) ^ n / n ≤ (worstCaseHeadComplexity n : ℝ) := by
  rintro ⟨c, hc, N, hN⟩
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max (max (N : ℝ) 32) (Real.exp (2323202 / c)))
  have hnN : N ≤ n := by
    have h : (N : ℝ) < n := (le_max_left (N : ℝ) 32).trans_lt
      ((le_max_left _ _).trans_lt hn)
    exact (by exact_mod_cast h : N < n).le
  have hn32 : 32 ≤ n := by
    have h : (32 : ℝ) < n := (le_max_right (N : ℝ) 32).trans_lt
      ((le_max_left _ _).trans_lt hn)
    exact (by exact_mod_cast h : 32 < n).le
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have he : Real.exp (2323202 / c) < n := (le_max_right _ _).trans_lt hn
  have hlarge : 2323202 / c < Real.log n := by
    have h := Real.strictMonoOn_log (Real.exp_pos _) hnp he
    simpa only [Real.log_exp] using h
  have hcprod : 2323202 < c * Real.log n := by
    have h := (div_lt_iff₀ hc).mp hlarge
    nlinarith
  have hbound := (hN n hnN).trans (worstCaseHeadComplexity_real_le_log_saving hn32)
  have hcross := (div_le_div_iff₀ hnp (mul_pos hnp hlog)).mp hbound
  have hp : 0 < (2 : ℝ) ^ n := by positivity
  nlinarith [mul_pos hp hnp]

end HeadComplexity
