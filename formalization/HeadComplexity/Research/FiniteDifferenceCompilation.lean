import HeadComplexity.Research.TwoHeadProductCompilation

set_option linter.style.header false

/-!
Finite-difference compilation for an arbitrary finite family of positive
denominators. This verifies the analytic sign bridge before subset expansion.
The expansion has exponentially many possible directions, so this result
does not improve the original worst-case head lower bound.
-/

noncomputable section

namespace HeadComplexity.FiniteDifferenceCompilation

open Filter Finset
open scoped Topology BigOperators

def expDifference (b t : ℝ) : ℝ := (Real.exp (t*b)-1)/t

theorem expDifference_limit (b : ℝ) :
    Tendsto (expDifference b) (𝓝[>] 0) (𝓝 b) := by
  change Tendsto (fun t : ℝ => (Real.exp (t*b)-1)/t) (𝓝[>] 0) (𝓝 b)
  simpa [TwoHeadProductCompilation.compiled] using
    TwoHeadProductCompilation.compiled_scaled_limit 1 0 0 b

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def cleared (A B : ι → ℝ) : ℝ :=
  ∑ h, A h * ∏ g ∈ (univ.erase h), B g

def compiled (A B : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ h, A h * ∏ g ∈ (univ.erase h), expDifference (B g) t

theorem compiled_limit (A B : ι → ℝ) :
    Tendsto (compiled A B) (𝓝[>] 0) (𝓝 (cleared A B)) := by
  unfold compiled cleared
  apply tendsto_finsetSum
  intro h hh
  apply Tendsto.const_mul
  apply tendsto_finsetProd
  intro g hg
  exact expDifference_limit (B g)

theorem cleared_eq_score_mul_product (A B : ι → ℝ) (hB : ∀ h, B h ≠ 0) :
    cleared A B = (∑ h, A h/B h) * ∏ h, B h := by
  rw [sum_mul]
  apply sum_congr rfl
  intro h hh
  have he : (∏ g : ι, B g) = B h * ∏ g ∈ univ.erase h, B g :=
    (mul_prod_erase univ B (mem_univ h)).symm
  rw [he]
  field_simp [hB h]

theorem uniform_finite_head_sign_compilation {X : Type*} [Fintype X]
    (A B : ι → X → ℝ) (hB : ∀ h x, 0 < B h x)
    (hs : ∀ x, (∑ h, A h x/B h x) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → ∀ x,
      0 < (∑ h, A h x/B h x) * compiled (fun h => A h x) (fun h => B h x) t := by
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ x,
      0 < (∑ h, A h x/B h x) * compiled (fun h => A h x) (fun h => B h x) t := by
    rw [Filter.eventually_all]
    intro x
    have hp : 0 < (∑ h, A h x/B h x) * cleared (fun h => A h x) (fun h => B h x) := by
      rw [cleared_eq_score_mul_product _ _ (fun h => ne_of_gt (hB h x))]
      have hprod : 0 < ∏ h, B h x := prod_pos (fun h _ => hB h x)
      have hsq := mul_self_pos.mpr (hs x)
      nlinarith [mul_pos hsq hprod]
    exact ((compiled_limit (fun h => A h x) (fun h => B h x)).const_mul
      (∑ h, A h x/B h x)).eventually_const_lt hp
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨ε, hε, fun t ht hte => hsub ⟨?_, ht⟩⟩
  simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using hte

#print axioms uniform_finite_head_sign_compilation

end HeadComplexity.FiniteDifferenceCompilation
