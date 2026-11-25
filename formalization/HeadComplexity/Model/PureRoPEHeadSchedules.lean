import HeadComplexity.Model.RectangularPureRoPE

set_option linter.style.header false

/-!
# Pure rotary extraction with a separate schedule for each head

The fixed-standard architecture uses one common schedule. This module also
covers the broader reading of freely chosen frequencies in which each head
chooses its own frequency list. Extraction allows arbitrary finite head width
and arbitrary linear position maps; an unrotated extra coordinate is included.
All self logits still rotate both the query and its own key by the same map.
-/

namespace HeadComplexity

open scoped BigOperators InnerProductSpace

namespace RectangularPureRotaryFamily

variable {n dm dh H : ℕ}

/-- The same literal architecture, with only the schedule allowed to vary by head. -/
noncomputable def residualWithHeadSchedules (M : RectangularPureRotaryFamily n dm dh H)
    (R : Fin H → RotarySchedule n dh) (x : Fin n → Bool) : Vec dm :=
  M.tokenEmbed 2 + ∑ h, M.headUpdate (R h) h x

@[simp] theorem residualWithHeadSchedules_common
    (M : RectangularPureRotaryFamily n dm dh H) (R : RotarySchedule n dh)
    (x : Fin n → Bool) : M.residualWithHeadSchedules (fun _ ↦ R) x = M.residual R x := rfl

theorem headSchedules_score_eq (M : RectangularPureRotaryFamily n dm dh H)
    (R : Fin H → RotarySchedule n dh) (w : Vec dm) (τ : ℝ) (x : Fin n → Bool) :
    ⟪w, M.residualWithHeadSchedules R x⟫_ℝ - τ =
      (⟪w, M.tokenEmbed 2⟫_ℝ - τ) + ∑ h, (M.toAtom (R h) w h).eval x := by
  rw [residualWithHeadSchedules, inner_add_right, inner_sum]
  simp_rw [head_readout_eq_atom]
  ring

/-- Necessity does not assume shared frequencies, even width, or interpolation. -/
theorem pureRoPEComputable_of_headSchedules
    (M : RectangularPureRotaryFamily n dm dh H) (R : Fin H → RotarySchedule n dh)
    (f : (Fin n → Bool) → Bool)
    (hf : computesPred f (M.residualWithHeadSchedules R)) :
    pureRoPEComputable n H f := by
  obtain ⟨w, τ, hf⟩ := hf
  refine ⟨fun h ↦ M.toAtom (R h) w h, ⟪w, M.tokenEmbed 2⟫_ℝ - τ, fun x ↦ ?_⟩
  rw [← M.headSchedules_score_eq R w τ x, sub_pos]
  exact hf x

/-- Even headwise arbitrary schedules have an exact common-standard realization. -/
theorem exists_standard_score_of_headSchedules
    (M : RectangularPureRotaryFamily n dm dh H) (R : Fin H → RotarySchedule n dh)
    (w : Vec dm) (τ : ℝ) :
    ∃ (N : RectangularPureRotaryFamily n ((n + 2) * 2) ((n + 2) * 2) H)
      (v : Vec ((n + 2) * 2)) (θ : ℝ),
      ∀ x, ⟪v, N.residual (frequencySchedule (standardRotaryFrequency (n + 2))) x⟫_ℝ - θ =
        ⟪w, M.residualWithHeadSchedules R x⟫_ℝ - τ := by
  obtain ⟨N, v, θ, hN⟩ := exists_standardPureRotaryFamily_score
    (fun h ↦ M.toAtom (R h) w h) (⟪w, M.tokenEmbed 2⟫_ℝ - τ)
  refine ⟨ofSquare N, v, θ, fun x ↦ ?_⟩
  rw [ofSquare_residual, hN, M.headSchedules_score_eq]

end RectangularPureRotaryFamily

/-- A separate freely chosen frequency list per head, with common finite widths. -/
def rectangularHeadwiseFreePureRotaryComputable (n H : ℕ)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (dm : ℕ) (_ : 0 < dm) (m : ℕ) (_ : 0 < m) (ω : Fin H → Fin m → ℝ)
    (M : RectangularPureRotaryFamily n dm (m * 2) H),
    computesPred f (M.residualWithHeadSchedules (fun h ↦ frequencySchedule (ω h)))

theorem rectangularHeadwiseFreePureRotaryComputable_iff_scalar (n H : ℕ)
    (f : (Fin n → Bool) → Bool) :
    rectangularHeadwiseFreePureRotaryComputable n H f ↔ pureRoPEComputable n H f := by
  constructor
  · rintro ⟨dm, hdm, m, hm, ω, M, hf⟩
    exact M.pureRoPEComputable_of_headSchedules _ f hf
  · intro hf
    obtain ⟨dm, hdm, m, hm, M, hM⟩ :=
      (rectangularStandardPureRotaryComputable_iff_scalar n H f).mpr hf
    refine ⟨dm, hdm, m, hm, fun _ ↦ standardRotaryFrequency m, M, ?_⟩
    obtain ⟨w, τ, hclass⟩ := hM
    refine ⟨w, τ, fun x ↦ ?_⟩
    rw [RectangularPureRotaryFamily.residualWithHeadSchedules_common]
    exact hclass x

/-- Sharing the frequencies across heads does not reduce Boolean expressivity. -/
theorem rectangularHeadwiseFreePureRotaryComputable_iff_standard (n H : ℕ)
    (f : (Fin n → Bool) → Bool) :
    rectangularHeadwiseFreePureRotaryComputable n H f ↔
      rectangularStandardPureRotaryComputable n H f :=
  (rectangularHeadwiseFreePureRotaryComputable_iff_scalar n H f).trans
    (rectangularStandardPureRotaryComputable_iff_scalar n H f).symm

end HeadComplexity
