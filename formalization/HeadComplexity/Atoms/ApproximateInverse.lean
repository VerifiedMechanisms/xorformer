import HeadComplexity.Atoms.CertifiedContraction
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option linter.style.header false

namespace HeadComplexity.ApproximateInverse

open ContinuousLinearMap Metric Set
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lower_bound (R J : E →L[ℝ] E) (q : ℝ)
    (hres : ‖ContinuousLinearMap.id ℝ E - R.comp J‖ ≤ q) (v : E) :
    (1 - q) * ‖v‖ ≤ ‖R‖ * ‖J v‖ := by
  have hb := (ContinuousLinearMap.id ℝ E - R.comp J).le_opNorm v
  have hq := mul_le_mul_of_nonneg_right hres (norm_nonneg v)
  have htri := norm_le_norm_add_norm_sub (R (J v)) v
  have hR := R.le_opNorm (J v)
  simp only [sub_apply, id_apply, comp_apply] at hb
  rw [norm_sub_rev] at htri
  nlinarith

theorem injective_of_residual (R J : E →L[ℝ] E) (q : ℝ) (hq : q < 1)
    (hres : ‖ContinuousLinearMap.id ℝ E - R.comp J‖ ≤ q) : Function.Injective J := by
  intro x y hxy
  have hk : J (x - y) = 0 := by simp [map_sub, hxy]
  have hb := lower_bound R J q hres (x - y)
  simp only [hk, norm_zero, mul_zero] at hb
  have hz : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

variable [FiniteDimensional ℝ E]

theorem approximate_inverse_injective (R J : E →L[ℝ] E) (q : ℝ) (hq : q < 1)
    (hres : ‖ContinuousLinearMap.id ℝ E - R.comp J‖ ≤ q) : Function.Injective R := by
  have hinj : Function.Injective (R.comp J) := by
    apply injective_of_residual (ContinuousLinearMap.id ℝ E) (R.comp J) q hq
    simpa using hres
  have hsurj := (LinearMap.injective_iff_surjective (f := (R.comp J).toLinearMap)).mp hinj
  apply (LinearMap.injective_iff_surjective (f := R.toLinearMap)).mpr
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨J x, hx⟩

noncomputable def equivOfResidual (R J : E →L[ℝ] E) (q : ℝ) (hq : q < 1)
    (hres : ‖ContinuousLinearMap.id ℝ E - R.comp J‖ ≤ q) : E ≃L[ℝ] E :=
  (LinearEquiv.ofInjectiveEndo J.toLinearMap (injective_of_residual R J q hq hres)).toContinuousLinearEquiv

theorem equivOfResidual_apply (R J : E →L[ℝ] E) (q : ℝ) (hq : q < 1)
    (hres : ‖ContinuousLinearMap.id ℝ E - R.comp J‖ ≤ q) (v : E) :
    equivOfResidual R J q hq hres v = J v := rfl

theorem inverse_norm_bound (R J : E →L[ℝ] E) (q M : ℝ) (hq : q < 1)
    (hres : ‖ContinuousLinearMap.id ℝ E - R.comp J‖ ≤ q) (hR : ‖R‖ ≤ M) :
    ‖(equivOfResidual R J q hq hres).symm.toContinuousLinearMap‖ ≤ M / (1 - q) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hR
  apply opNorm_le_bound _ (div_nonneg hM (sub_pos.mpr hq).le)
  intro v
  let e := equivOfResidual R J q hq hres
  have he : J (e.symm v) = v := e.apply_symm_apply v
  have hb := lower_bound R J q hres (e.symm v)
  rw [he] at hb
  have hr := mul_le_mul_of_nonneg_right hR (norm_nonneg v)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hq)).mpr
  simpa [mul_comm] using hb.trans hr

omit [FiniteDimensional ℝ E] in
theorem residual_near (R J J₀ : E →L[ℝ] E) (ε M δ : ℝ)
    (hε : ‖ContinuousLinearMap.id ℝ E - R.comp J₀‖ ≤ ε)
    (hM : ‖R‖ ≤ M) (hδ : ‖J - J₀‖ ≤ δ) :
    ‖ContinuousLinearMap.id ℝ E - R.comp J‖ ≤ ε + M * δ := by
  have heq : ContinuousLinearMap.id ℝ E - R.comp J =
      (ContinuousLinearMap.id ℝ E - R.comp J₀) - R.comp (J - J₀) := by
    ext v
    simp
  rw [heq]
  calc
    ‖(ContinuousLinearMap.id ℝ E - R.comp J₀) - R.comp (J - J₀)‖ ≤
        ‖ContinuousLinearMap.id ℝ E - R.comp J₀‖ + ‖R.comp (J - J₀)‖ := norm_sub_le _ _
    _ ≤ ε + M * δ := by
      apply add_le_add hε
      exact (opNorm_comp_le _ _).trans
        (mul_le_mul hM hδ (norm_nonneg _) ((norm_nonneg _).trans hM))

variable [CompleteSpace E]

theorem exists_zero_of_derivative_certificate
    (F : E → E) (J : E → E →L[ℝ] E) (R : E →L[ℝ] E) (c : E)
    (r ε M δ : ℝ) (q : ℝ≥0) (hr : 0 ≤ r) (hq : q < 1)
    (hF : ∀ z ∈ closedBall c r, HasFDerivAt F (J z) z)
    (hε : ‖ContinuousLinearMap.id ℝ E - R.comp (J c)‖ ≤ ε)
    (hR : ‖R‖ ≤ M)
    (hJ : ∀ z ∈ closedBall c r, ‖J z - J c‖ ≤ δ)
    (hbudget : ε + M * δ ≤ q)
    (hcenter : ‖R (F c)‖ ≤ (1 - (q : ℝ)) * r) :
    ∃ z ∈ closedBall c r, F z = 0 ∧ Function.Injective (J z) := by
  have hres (z) (hz : z ∈ closedBall c r) :
      ‖ContinuousLinearMap.id ℝ E - R.comp (J z)‖ ≤ q :=
    (residual_near R (J z) (J c) ε M δ hε hR (hJ z hz)).trans hbudget
  have hRinj := approximate_inverse_injective R (J c) q hq (hres c (mem_closedBall_self hr))
  have hLip : LipschitzOnWith q (fun z ↦ z - R (F z)) (closedBall c r) := by
    apply (convex_closedBall c r).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := fun z ↦ ContinuousLinearMap.id ℝ E - R.comp (J z))
    · intro z hz
      exact ((hasFDerivAt_id z).sub (R.hasFDerivAt.comp z (hF z hz))).hasFDerivWithinAt
    · intro z hz
      exact hres z hz
  obtain ⟨z, hz, hzero⟩ := CertifiedContraction.exists_zero_of_contraction
    F R hRinj c r hr q hq hLip hcenter
  exact ⟨z, hz, hzero, injective_of_residual R (J z) q hq (hres z hz)⟩

#print axioms inverse_norm_bound
#print axioms exists_zero_of_derivative_certificate

end HeadComplexity.ApproximateInverse
