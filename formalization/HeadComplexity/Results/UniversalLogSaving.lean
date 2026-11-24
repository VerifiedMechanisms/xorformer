import HeadComplexity.Results.AffinePlaneCompiler
import HeadComplexity.Results.AffinePlaneSavingAsymptotics

set_option linter.style.header false

/-!
# Universal logarithmic saving in worst-case head complexity

The affine-plane Cauchy decoder, exact axis repair, and downward product-cover
assembly prove `W(n) = O(2^n / (n * log n))` for the original one-layer attention
model.  No definition of the model or head resource is changed.
-/

namespace HeadComplexity

open Filter Asymptotics
open AxisZeroGluing
open scoped Topology

private theorem affinePlaneCompiler_for_asymptotics (a r s : ℕ)
    (ha : 1 ≤ a) (hr : r ≤ a * 4 ^ a) :
    HasStrictReverseGridCompiler r s (2 * 4 ^ a + 2 ^ a + 1) := by
  intro table
  obtain ⟨H, hH, L, hL⟩ := hasStrictReverseGridCompiler_affinePlane a r s ha hr table
  exact ⟨H, by nlinarith [Nat.zero_le (2 ^ a)], L, hL⟩

/-- Unconditional logarithmic improvement over the universal linear saving,
stated against the repository's original worst-case head complexity. -/
theorem worstCaseHeadComplexity_isBigO_two_pow_div_mul_log :
    (fun n : ℕ ↦ (worstCaseHeadComplexity n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (2 : ℝ) ^ n / ((n : ℝ) * Real.log n)) :=
  worstCaseHeadComplexity_isBigO_log_of_affinePlaneCompiler
    affinePlaneCompiler_for_asymptotics

/-- An explicit eventual bound, including all axis-repair and exceptional-face
heads.  The numerical constant is deliberately not optimized. -/
theorem worstCaseHeadComplexity_real_le_log_saving {n : ℕ} (hn : 32 ≤ n) :
    (worstCaseHeadComplexity n : ℝ) ≤
      2323202 * (2 : ℝ) ^ n / ((n : ℝ) * Real.log n) := by
  obtain ⟨a, ha, hcap, hsize⟩ := exists_affinePlaneScale (n / 2) (by omega)
  have hcomp := hasReverseAxisCompiler_of_strictReverseGridCompiler
    (affinePlaneCompiler_for_asymptotics a (n / 2) (n - n / 2) (by omega) hcap)
  have hbudget := affinePlane_axis_budget (show 10 ≤ n by omega) ha hcap hsize
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogle : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos hnpos
    linarith
  have h := worstCaseHeadComplexity_balanced_le hn (K := 600) (by norm_num)
    hlogpos hlogle hcomp hbudget
  norm_num at h ⊢
  exact h

/-- The equivalent positive-constant, eventual-inequality formulation. -/
theorem worstCaseHeadComplexity_exists_log_saving :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (worstCaseHeadComplexity n : ℝ) ≤
        C * (2 : ℝ) ^ n / ((n : ℝ) * Real.log n) := by
  exact ⟨2323202, by norm_num, 32, fun _ hn ↦ worstCaseHeadComplexity_real_le_log_saving hn⟩

end HeadComplexity
