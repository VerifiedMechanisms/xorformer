import HeadComplexity.Results.UniversalLogSaving

set_option linter.style.header false

/-! An explicit version of the original local compiler request, for every
positive pair of block sizes. The affine-plane construction was supplied by
run `0f08fe6fb98a`; this corollary and its audit belong to the resumed run. -/

namespace HeadComplexity.AxisZeroGluing

/-- Every pair of positive block sizes has a strictly admissible axis-zero
compiler with an absolute logarithmic saving. No decoder premise remains. -/
theorem exists_reverse_axis_compiler_log_budget {r s : ℕ}
    (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ∃ M : ℕ, (M : ℝ) ≤ 1200 * (r + s) / Real.log (r + s) ∧
      HasReverseAxisCompiler r s M := by
  let m := r + s
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlog : 0 < Real.log m := Real.log_pos (by exact_mod_cast hm)
  by_cases hsmall : m < 5
  · have hcap : r ≤ 1 * 4 ^ 1 := by dsimp [m] at hsmall; omega
    have hcomp := hasReverseAxisCompiler_of_strictReverseGridCompiler
      (hasStrictReverseGridCompiler_affinePlane 1 r s (by omega) hcap)
    refine ⟨30, ?_, by norm_num at hcomp; exact hcomp⟩
    simp only [← Nat.cast_add]
    change (30 : ℝ) ≤ 1200 * m / Real.log m
    apply (le_div_iff₀ hlog).2
    have hlogle := Real.log_le_sub_one_of_pos hmp
    nlinarith
  · obtain ⟨a, ha, hcap, hsize⟩ := exists_affinePlaneScale m (by omega)
    have hcomp := hasReverseAxisCompiler_of_strictReverseGridCompiler
      (hasStrictReverseGridCompiler_affinePlane a r s (by omega)
        ((show r ≤ m by dsimp [m]; omega).trans hcap))
    refine ⟨3 * (2 * 4 ^ a + 1) + 3, ?_, hcomp⟩
    simp only [← Nat.cast_add]
    change ((3 * (2 * 4 ^ a + 1) + 3 : ℕ) : ℝ) ≤
      1200 * m / Real.log m
    have hb := affinePlane_axis_budget (n := 2 * m) (by omega) ha
      (by simpa using hcap) (by simpa using hsize)
    have hlog2 : 0 < Real.log (2 * m : ℕ) :=
      Real.log_pos (by exact_mod_cast (show 1 < 2 * m by omega))
    have hprod := (le_div_iff₀ hlog2).mp hb
    have hhead : ((3 * (2 * 4 ^ a + 1) + 3 : ℕ) : ℝ) ≤
        ((3 * (2 * 4 ^ a + 2 ^ a + 1) + 3 : ℕ) : ℝ) := by
      exact_mod_cast (show 3 * (2 * 4 ^ a + 1) + 3 ≤
        3 * (2 * 4 ^ a + 2 ^ a + 1) + 3 by nlinarith [Nat.zero_le (2 ^ a)])
    have hlogle : Real.log (m : ℝ) ≤ Real.log (2 * m : ℕ) := by
      apply Real.log_le_log hmp
      exact_mod_cast (show m ≤ 2 * m by omega)
    apply (le_div_iff₀ hlog).2
    calc
      ((3 * (2 * 4 ^ a + 1) + 3 : ℕ) : ℝ) * Real.log m ≤
          ((3 * (2 * 4 ^ a + 2 ^ a + 1) + 3 : ℕ) : ℝ) * Real.log m :=
        mul_le_mul_of_nonneg_right hhead hlog.le
      _ ≤ ((3 * (2 * 4 ^ a + 2 ^ a + 1) + 3 : ℕ) : ℝ) *
          Real.log (2 * m : ℕ) := mul_le_mul_of_nonneg_left hlogle (by positivity)
      _ ≤ 1200 * m := by push_cast at hprod ⊢; nlinarith

/-- Concrete local data satisfying both full Boolean axis identities, every
strict grid sign, and the logarithmic head budget in the original request. -/
theorem exists_reverse_axis_log_data {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (table : Fin r → Fin s → Bool) :
    ∃ H : ℕ, (H : ℝ) ≤ 1200 * (r + s) / Real.log (r + s) ∧
      ∃ L : ReverseAxisData r s H, ∀ i j,
        0 < outputSign (table i j) * L.score (localGrid i j) := by
  obtain ⟨M, hM, hc⟩ := exists_reverse_axis_compiler_log_budget hr hs
  obtain ⟨H, hH, L, hL⟩ := hc table
  have hh : (H : ℝ) ≤ M := by exact_mod_cast hH
  exact ⟨H, hh.trans hM, L, hL⟩

end HeadComplexity.AxisZeroGluing
