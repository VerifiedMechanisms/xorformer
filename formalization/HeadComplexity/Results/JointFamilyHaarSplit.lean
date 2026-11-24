import HeadComplexity.Results.JointFamilyGatedDifferences

set_option linter.style.header false

namespace HeadComplexity.AxisZeroGluing

open Filter
open scoped BigOperators

noncomputable def jointFamilyHaarPair (D p a t : ℝ) : ℝ :=
  (a + t) / (D - p) - (a - t) / (D + t - p)

noncomputable def jointFamilyHaarNormalized (D p a t : ℝ) : ℝ :=
  a / ((D - p) * (D + t - p)) + 1 / (D - p) + 1 / (D + t - p)

theorem jointFamily_haar_pair_factor (D p a t : ℝ)
    (h₀ : D - p ≠ 0) (h₁ : D + t - p ≠ 0) :
    jointFamilyHaarPair D p a t = t * jointFamilyHaarNormalized D p a t := by
  unfold jointFamilyHaarPair jointFamilyHaarNormalized
  field_simp
  ring

theorem jointFamily_haar_normalized_limit (D p a c : ℝ) (h : D - p ≠ 0) :
    Tendsto (fun t : ℝ ↦ jointFamilyHaarNormalized D (p + c * t) a t)
      (nhds 0) (nhds (a / (D - p) ^ 2 + 2 / (D - p))) := by
  have ht : Tendsto (fun t : ℝ ↦ t) (nhds 0) (nhds 0) := tendsto_id
  have hD : Tendsto (fun t : ℝ ↦ D - (p + c * t)) (nhds 0) (nhds (D - p)) := by
    simpa using (tendsto_const_nhds (x := D)).sub
      ((tendsto_const_nhds (x := p)).add (ht.const_mul c))
  have hE : Tendsto (fun t : ℝ ↦ D + t - (p + c * t))
      (nhds 0) (nhds (D - p)) := by
    simpa using ((tendsto_const_nhds (x := D)).add ht).sub
      ((tendsto_const_nhds (x := p)).add (ht.const_mul c))
  have hh := ((tendsto_const_nhds (x := a)).div (hD.mul hE) (mul_ne_zero h h)).add
    ((tendsto_const_nhds (x := (1 : ℝ))).div hD h)
  have hh' := hh.add ((tendsto_const_nhds (x := (1 : ℝ))).div hE h)
  have he : a / ((D - p) * (D - p)) + 1 / (D - p) + 1 / (D - p) =
      a / (D - p) ^ 2 + 2 / (D - p) := by ring
  simpa only [jointFamilyHaarNormalized, Pi.div_apply, he] using hh'

/-- Splitting two equal-pole child banks by a new gap exposes the freely
chosen residue difference through a square-Cauchy kernel. The coefficient
`c` can encode either orientation of every final switch. -/
theorem jointFamily_haar_split_limit {m : ℕ} (D : ℝ)
    (p a v c : Fin m → ℝ) (δ : ℝ) (h : ∀ r, D - p r ≠ 0) :
    Tendsto (fun t : ℝ ↦ ∑ r : Fin m,
      (jointFamilyHaarNormalized D (p r + c r * t) (a r + δ * v r / 2) t -
       jointFamilyHaarNormalized D (p r + (1 - c r) * t) (a r - δ * v r / 2) t))
      (nhds 0) (nhds (δ * ∑ r : Fin m, v r / (D - p r) ^ 2)) := by
  have hh := tendsto_finsetSum (Finset.univ : Finset (Fin m)) (fun r _ ↦
    (jointFamily_haar_normalized_limit D (p r) (a r + δ * v r / 2) (c r) (h r)).sub
      (jointFamily_haar_normalized_limit D (p r) (a r - δ * v r / 2) (1 - c r) (h r)))
  have he : (∑ r : Fin m,
      ((a r + δ * v r / 2) / (D - p r) ^ 2 + 2 / (D - p r) -
       ((a r - δ * v r / 2) / (D - p r) ^ 2 + 2 / (D - p r)))) =
      δ * ∑ r : Fin m, v r / (D - p r) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  simpa only [he] using hh

/-- A solved square-Cauchy linear system supplies all new-stage signs at
once. Existing child signs are handled separately by their finite strict
margins. This statement does not assert that arbitrary child words have
a common residue vector. -/
theorem jointFamily_haar_split_strict_signs {m q : ℕ}
    (D : Fin q → ℝ) (p a v c : Fin m → ℝ) (σ : Fin q → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (h : ∀ s r, D s - p r ≠ 0)
    (hσ : ∀ s, σ s * σ s = 1)
    (hsolve : ∀ s, (∑ r : Fin m, v r / (D s - p r) ^ 2) = σ s) :
    ∀ᶠ t : ℝ in nhds 0, ∀ s,
      0 < σ s * ∑ r : Fin m,
        (jointFamilyHaarNormalized (D s) (p r + c r * t) (a r + δ * v r / 2) t -
         jointFamilyHaarNormalized (D s) (p r + (1 - c r) * t)
           (a r - δ * v r / 2) t) := by
  apply Filter.eventually_all.mpr
  intro s
  have hl := (jointFamily_haar_split_limit (D s) p a v c δ (h s)).const_mul (σ s)
  have he : σ s * (δ * ∑ r : Fin m, v r / (D s - p r) ^ 2) = δ := by
    rw [hsolve s]
    calc
      σ s * (δ * σ s) = δ * (σ s * σ s) := by ring
      _ = δ := by rw [hσ s, mul_one]
  rw [he] at hl
  exact hl.eventually (eventually_gt_nhds hδ)

end HeadComplexity.AxisZeroGluing
