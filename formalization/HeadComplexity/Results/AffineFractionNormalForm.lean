import HeadComplexity.Atoms.AffineFraction
import HeadComplexity.Results.FractionalNormalForm

set_option linter.style.header false

/-!
# Theorem 10. Exact affine-ratio normal form

Combining the attention-to-atom correspondence with the exact coefficient
characterization preserves the entire scalar score, each head budget, and its
minimum. The constant absorbs the threshold and the input-independent residual.
Admissibility directly requires positivity on the cube and uniform denominator
slopes, with uniform numerator slopes required only for a constant denominator.
-/

namespace HeadComplexity

open scoped BigOperators InnerProductSpace

variable {n : ℕ}

/-- Exact score normal form for the literal shared-embedding model. The threshold
absorbs the constant query residual. This includes zero heads and zero inputs. -/
theorem shared_score_iff_affineFraction (H : ℕ) (Φ : (Fin n → Bool) → ℝ) :
    (∃ d, ∃ M : SharedHeadFamily n d H, ∃ (w : Vec d) (τ : ℝ),
      ∀ x, ⟪w, M.attnUpdate x⟫_ℝ - τ = Φ x) ↔
    ∃ (r : Fin H → AffineFraction n) (c : ℝ), (∀ h, (r h).Admissible) ∧
      ∀ x, c + ∑ h, (r h).eval x = Φ x := by
  constructor
  · rintro ⟨d, M, w, τ, hΦ⟩
    refine ⟨fun h ↦ (headToAtom (M.head h) w).toAffineFraction, -τ,
      fun h ↦ (headToAtom (M.head h) w).toAffineFraction_admissible, ?_⟩
    intro x
    rw [← hΦ x]
    change -τ + _ = ⟪w, ∑ h, (M.head h).attnUpdate x⟫_ℝ - τ
    simp_rw [inner_sum, head_readout_eq_eval, FracAtom.eval_eq]
    ring
  · rintro ⟨r, c, hr, hΦ⟩
    choose φ hφ using fun h ↦ (r h).exists_atom (hr h)
    refine ⟨H * 3, shareHeadEmbeddings (fun h ↦ atomHead' (φ h)),
      headBlockConcat (fun _ : Fin H ↦ fracReadout), -c, ?_⟩
    intro x
    rw [shareHeadEmbeddings_readout]
    change ⟪fracReadout, ∑ h, (atomHead' (φ h)).attnUpdate x⟫_ℝ - -c = Φ x
    rw [atomFamily'_readout]
    simpa only [FracAtom.eval_eq, hφ, sub_neg_eq_add, add_comm] using hΦ x

/-- A thresholded sum of `H` admissible affine ratios and one free constant. -/
def affineFractionComputable (n H : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (r : Fin H → AffineFraction n) (c : ℝ), (∀ h, (r h).Admissible) ∧
    ∀ x, (0 < c + ∑ h, (r h).eval x ↔ f x = true)

theorem fracComputable_iff_affineFractionComputable (H : ℕ)
    (f : (Fin n → Bool) → Bool) :
    fracComputable n H f ↔ affineFractionComputable n H f := by
  constructor
  · rintro ⟨φ, c, hf⟩
    exact ⟨fun h ↦ (φ h).toAffineFraction, c,
      fun h ↦ (φ h).toAffineFraction_admissible, by simpa only [FracAtom.eval_eq] using hf⟩
  · rintro ⟨r, c, hr, hf⟩
    choose φ hφ using fun h ↦ (r h).exists_atom (hr h)
    exact ⟨φ, c, by simpa only [FracAtom.eval_eq, hφ] using hf⟩

theorem computableWithHeadsN_iff_affineFractionComputable (H : ℕ)
    (f : (Fin n → Bool) → Bool) :
    computableWithHeadsN n H f ↔ affineFractionComputable n H f :=
  (computableWithHeadsN_iff_fracComputable H f).trans
    (fracComputable_iff_affineFractionComputable H f)

theorem computableWithSharedHeadsN_iff_affineFractionComputable (H : ℕ)
    (f : (Fin n → Bool) → Bool) :
    computableWithSharedHeadsN n H f ↔ affineFractionComputable n H f :=
  (computableWithSharedHeadsN_iff_fracComputable H f).trans
    (fracComputable_iff_affineFractionComputable H f)

/-- Least number of admissible affine ratios computing a Boolean function. -/
noncomputable def LaffineFrac (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact if h : ∃ H, affineFractionComputable n H f then Nat.find h else 0

theorem Lfrac_eq_LaffineFrac (f : (Fin n → Bool) → Bool) :
    Lfrac n f = LaffineFrac n f := by
  have h : fracComputable n = affineFractionComputable n :=
    funext fun H ↦ funext fun g ↦ propext (fracComputable_iff_affineFractionComputable H g)
  unfold Lfrac LaffineFrac
  rw [h]

theorem HStar_eq_LaffineFrac (f : (Fin n → Bool) → Bool) :
    HStar n f = LaffineFrac n f :=
  (HStar_eq_Lfrac f).trans (Lfrac_eq_LaffineFrac f)

theorem SharedHStar_eq_LaffineFrac (f : (Fin n → Bool) → Bool) :
    SharedHStar n f = LaffineFrac n f :=
  (SharedHStar_eq_Lfrac f).trans (Lfrac_eq_LaffineFrac f)

end HeadComplexity
