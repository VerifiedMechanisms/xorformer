import HeadComplexity.Model.RotaryInterpolation

set_option linter.style.header false

/-!
# The exact rectangular pure rotary architecture

This model keeps separate model and head widths and an explicit output
projection, as in `model.md`. Only additive positional embeddings are removed
and the same position rotations are applied to Q and K. The square construction
of `PureRotaryFamily` is a special case, with output projection the identity.
-/

namespace HeadComplexity

open scoped BigOperators InnerProductSpace

/-- The exact rectangular architecture with shared token embeddings and an
explicit output projection for every head. -/
structure RectangularPureRotaryFamily (n dm dh H : ℕ) where
  tokenEmbed : Fin 3 → Vec dm
  WQ : Fin H → Vec dm →ₗ[ℝ] Vec dh
  WK : Fin H → Vec dm →ₗ[ℝ] Vec dh
  WV : Fin H → Vec dm →ₗ[ℝ] Vec dh
  WO : Fin H → Vec dh →ₗ[ℝ] Vec dm

namespace RectangularPureRotaryFamily

variable {n dm dh H : ℕ}

noncomputable def logit (M : RectangularPureRotaryFamily n dm dh H)
    (R : RotarySchedule n dh) (h : Fin H) (p : SeqPos n) (t : Fin 3) : ℝ :=
  ⟪R p (M.WK h (M.tokenEmbed t)), R none (M.WQ h (M.tokenEmbed 2))⟫_ℝ

noncomputable def sigma (M : RectangularPureRotaryFamily n dm dh H)
    (R : RotarySchedule n dh) (h : Fin H) (x : Fin n → Bool) (p : SeqPos n) : ℝ :=
  Real.exp (M.logit R h p (Head.seqTok x p))

noncomputable def value (M : RectangularPureRotaryFamily n dm dh H) (h : Fin H)
    (x : Fin n → Bool) (p : SeqPos n) : Vec dh :=
  M.WV h (M.tokenEmbed (Head.seqTok x p))

noncomputable def denominator (M : RectangularPureRotaryFamily n dm dh H)
    (R : RotarySchedule n dh) (h : Fin H) (x : Fin n → Bool) : ℝ :=
  ∑ p, M.sigma R h x p

noncomputable def numerator (M : RectangularPureRotaryFamily n dm dh H)
    (R : RotarySchedule n dh) (h : Fin H) (x : Fin n → Bool) : Vec dh :=
  ∑ p, M.sigma R h x p • M.value h x p

/-- The output projection is applied to the ordinary softmax weighted value sum. -/
noncomputable def headUpdate (M : RectangularPureRotaryFamily n dm dh H)
    (R : RotarySchedule n dh) (h : Fin H) (x : Fin n → Bool) : Vec dm :=
  M.WO h ((M.denominator R h x)⁻¹ • M.numerator R h x)

noncomputable def residual (M : RectangularPureRotaryFamily n dm dh H)
    (R : RotarySchedule n dh) (x : Fin n → Bool) : Vec dm :=
  M.tokenEmbed 2 + ∑ h, M.headUpdate R h x

/-- Output projection and readout compose into the token-only scalar values. -/
noncomputable def toAtom (M : RectangularPureRotaryFamily n dm dh H)
    (R : RotarySchedule n dh) (w : Vec dm) (h : Fin H) : PureRoPEAtom n where
  a i := Real.exp (M.logit R h (some i) 0)
  b i := Real.exp (M.logit R h (some i) 1)
  γ := Real.exp (M.logit R h none 2)
  η := Real.exp (M.logit R h none 2) * ⟪w, M.WO h (M.WV h (M.tokenEmbed 2))⟫_ℝ
  v₀ := ⟪w, M.WO h (M.WV h (M.tokenEmbed 0))⟫_ℝ
  v₁ := ⟪w, M.WO h (M.WV h (M.tokenEmbed 1))⟫_ℝ
  ha _ := Real.exp_pos _
  hb _ := Real.exp_pos _
  hγ := Real.exp_pos _

theorem denominator_eq (M : RectangularPureRotaryFamily n dm dh H)
    (R : RotarySchedule n dh) (w : Vec dm) (h : Fin H) (x : Fin n → Bool) :
    M.denominator R h x =
      (M.toAtom R w h).γ + ∑ i, if x i then (M.toAtom R w h).b i
        else (M.toAtom R w h).a i := by
  rw [denominator, Fintype.sum_option]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x i <;> simp [sigma, Head.seqTok, hx, toAtom]

theorem numerator_readout (M : RectangularPureRotaryFamily n dm dh H)
    (R : RotarySchedule n dh) (w : Vec dm) (h : Fin H) (x : Fin n → Bool) :
    ⟪w, M.WO h (M.numerator R h x)⟫_ℝ =
      (M.toAtom R w h).η + ∑ i, if x i then (M.toAtom R w h).b i *
        (M.toAtom R w h).v₁ else (M.toAtom R w h).a i * (M.toAtom R w h).v₀ := by
  rw [numerator, map_sum, inner_sum, Fintype.sum_option]
  simp_rw [map_smul, inner_smul_right]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x i <;> simp [sigma, value, Head.seqTok, hx, toAtom]

/-- Literal rectangular necessity, at the level of exact per-head real scores. -/
theorem head_readout_eq_atom (M : RectangularPureRotaryFamily n dm dh H)
    (R : RotarySchedule n dh) (w : Vec dm) (h : Fin H) (x : Fin n → Bool) :
    ⟪w, M.headUpdate R h x⟫_ℝ = (M.toAtom R w h).eval x := by
  rw [headUpdate, map_smul, inner_smul_right, numerator_readout, denominator_eq M R w]
  rw [PureRoPEAtom.eval, div_eq_inv_mul]

/-- Exact affine score extraction includes both the fixed residual and threshold. -/
theorem residual_score_eq (M : RectangularPureRotaryFamily n dm dh H)
    (R : RotarySchedule n dh) (w : Vec dm) (τ : ℝ) (x : Fin n → Bool) :
    ⟪w, M.residual R x⟫_ℝ - τ =
      (⟪w, M.tokenEmbed 2⟫_ℝ - τ) + ∑ h, (M.toAtom R w h).eval x := by
  rw [residual, inner_add_right, inner_sum]
  simp_rw [head_readout_eq_atom]
  ring

theorem pureRoPEComputable_of_computesPred
    (M : RectangularPureRotaryFamily n dm dh H) (R : RotarySchedule n dh)
    (f : (Fin n → Bool) → Bool) (hf : computesPred f (M.residual R)) :
    pureRoPEComputable n H f := by
  obtain ⟨w, τ, hf⟩ := hf
  refine ⟨M.toAtom R w, ⟪w, M.tokenEmbed 2⟫_ℝ - τ, ?_⟩
  intro x
  rw [← M.residual_score_eq R w τ x, sub_pos]
  exact hf x

/-- The constructive square model is a special case with identity output map. -/
noncomputable def ofSquare {d : ℕ} (M : PureRotaryFamily n d H) :
    RectangularPureRotaryFamily n d d H where
  tokenEmbed := M.tokenEmbed
  WQ := M.WQ
  WK := M.WK
  WV := M.WV
  WO _ := LinearMap.id

@[simp] theorem ofSquare_residual {d : ℕ} (M : PureRotaryFamily n d H)
    (R : RotarySchedule n d) (x : Fin n → Bool) :
    (ofSquare M).residual R x = M.residual R x := rfl

/-- Every rectangular rotary real score is exactly realized by the standard
schedule at a common finite width. No change of the original width's frequency
schedule is used in the necessity direction. -/
theorem exists_standard_score (M : RectangularPureRotaryFamily n dm dh H)
    (R : RotarySchedule n dh) (w : Vec dm) (τ : ℝ) :
    ∃ (N : RectangularPureRotaryFamily n ((n + 2) * 2) ((n + 2) * 2) H)
      (v : Vec ((n + 2) * 2)) (θ : ℝ),
      ∀ x, ⟪v, N.residual (frequencySchedule (standardRotaryFrequency (n + 2))) x⟫_ℝ - θ =
        ⟪w, M.residual R x⟫_ℝ - τ := by
  obtain ⟨N, v, θ, hN⟩ := exists_standardPureRotaryFamily_score
    (M.toAtom R w) (⟪w, M.tokenEmbed 2⟫_ℝ - τ)
  refine ⟨ofSquare N, v, θ, fun x => ?_⟩
  rw [ofSquare_residual, hN, M.residual_score_eq]

end RectangularPureRotaryFamily

/-- Standard frequencies in the exact architecture, with positive model width
and positive even head width, and no restriction on their relative sizes. -/
def rectangularStandardPureRotaryComputable (n H : ℕ)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (dm : ℕ) (_ : 0 < dm) (m : ℕ) (_ : 0 < m)
    (M : RectangularPureRotaryFamily n dm (m * 2) H),
    computesPred f (M.residual (frequencySchedule (standardRotaryFrequency m)))

/-- Free frequencies, still shared across all heads, in the exact architecture. -/
def rectangularFreePureRotaryComputable (n H : ℕ)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (dm : ℕ) (_ : 0 < dm) (m : ℕ) (_ : 0 < m) (ω : Fin m → ℝ)
    (M : RectangularPureRotaryFamily n dm (m * 2) H),
    computesPred f (M.residual (frequencySchedule ω))

/-- Complete fixed-standard rotary-to-scalar bridge for the exact rectangular
architecture, including the boundary cases `n=0` and `H=0`. -/
theorem rectangularStandardPureRotaryComputable_iff_scalar (n H : ℕ)
    (f : (Fin n → Bool) → Bool) :
    rectangularStandardPureRotaryComputable n H f ↔ pureRoPEComputable n H f := by
  constructor
  · rintro ⟨dm, hdm, m, hm, M, hf⟩
    exact M.pureRoPEComputable_of_computesPred _ f hf
  · rintro ⟨p, c, hp⟩
    obtain ⟨M, w, τ, hM⟩ := exists_standardPureRotaryFamily_score p c
    refine ⟨(n + 2) * 2, by omega, n + 2, by omega,
      RectangularPureRotaryFamily.ofSquare M, w, τ, fun x => ?_⟩
    rw [RectangularPureRotaryFamily.ofSquare_residual]
    change τ < ⟪w, M.residual _ x⟫_ℝ ↔ _
    rw [← sub_pos, hM]
    exact hp x

/-- Complete free-frequency rotary-to-scalar bridge for the exact architecture. -/
theorem rectangularFreePureRotaryComputable_iff_scalar (n H : ℕ)
    (f : (Fin n → Bool) → Bool) :
    rectangularFreePureRotaryComputable n H f ↔ pureRoPEComputable n H f := by
  constructor
  · rintro ⟨dm, hdm, m, hm, ω, M, hf⟩
    exact M.pureRoPEComputable_of_computesPred _ f hf
  · intro hf
    obtain ⟨dm, hdm, m, hm, M, hM⟩ :=
      (rectangularStandardPureRotaryComputable_iff_scalar n H f).mpr hf
    exact ⟨dm, hdm, m, hm, standardRotaryFrequency m, M, hM⟩

/-- Standard and free frequencies have identical exact Boolean head budgets. -/
theorem rectangularStandardPureRotaryComputable_iff_free (n H : ℕ)
    (f : (Fin n → Bool) → Bool) :
    rectangularStandardPureRotaryComputable n H f ↔
      rectangularFreePureRotaryComputable n H f :=
  (rectangularStandardPureRotaryComputable_iff_scalar n H f).trans
    (rectangularFreePureRotaryComputable_iff_scalar n H f).symm

end HeadComplexity
