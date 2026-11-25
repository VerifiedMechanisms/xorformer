import HeadComplexity.Research.ActiveMarginImprovement

set_option linter.style.header false

/-! Quantitative patching needs a gap off the exceptional set, not just a
bound on the number of exactly active constraints. The patch may have arbitrary
values elsewhere, provided its full-cube amplitude is controlled. -/

noncomputable section
namespace HeadComplexity.ExceptionalMarginRepair

open RelativeMarginQuantifiers ActiveMarginImprovement

theorem signed_score_ge_neg_amplitude {n K : ℕ}
    (f : (Fin n → Bool) → Bool) (psi : Fin K → FracAtom n) (d : ℝ)
    (x : Fin n → Bool) :
    -amplitude psi d ≤ signedLabel f x * score psi d x := by
  have hh : |signedLabel f x * score psi d x| ≤ amplitude psi d := by
    rw [abs_mul, abs_signedLabel, one_mul]
    exact abs_score_le_amplitude psi d x
  exact (neg_le_neg hh).trans (neg_abs_le _)

/-- A unit-gap patch on the exceptional set, of amplitude at most B, repairs
a score with relative gap tau everywhere else to margin at least tau/(3B).
All heads remain genuine and the width is the sum of the two input widths. -/
theorem relativeMargin_ge_of_exceptional_patch {n H K : ℕ}
    (f : (Fin n → Bool) → Bool) (E : Set (Fin n → Bool))
    (phi : Fin H → FracAtom n) (psi : Fin K → FracAtom n) (c d τ B : ℝ)
    (hs : StrictlyRepresents f phi c) (hτ : 0 < τ) (hτone : τ ≤ 1)
    (hB : 1 ≤ B) (hamp : amplitude psi d ≤ B)
    (hout : ∀ x, x ∉ E → τ * amplitude phi c ≤ signedLabel f x * score phi c x)
    (hin : ∀ x, x ∈ E → 1 ≤ signedLabel f x * score psi d x) :
    ∃ ε : ℝ, 0 < ε ∧
      StrictlyRepresents f (correctedHeads phi psi ε) (c + ε * d) ∧
      τ / (3 * B) ≤ relativeMargin f (correctedHeads phi psi ε) (c + ε * d) := by
  let D := amplitude phi c
  let ε := τ * D / (2 * B)
  have hD : 0 < D := amplitude_pos_of_strict hs
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hε : 0 < ε := by dsimp [ε]; positivity
  have heB : ε * B = τ * D / 2 := by
    dsimp [ε]
    field_simp
  have hehalf : ε ≤ τ * D / 2 := by nlinarith
  have hgap (x : Fin n → Bool) :
      ε ≤ signedLabel f x * score (correctedHeads phi psi ε) (c + ε * d) x := by
    rw [corrected_score, mul_add, ← mul_assoc]
    by_cases hx : x ∈ E
    · have h0 := hs x
      have h1 := hin x hx
      nlinarith
    · have h0 := hout x hx
      have h1 := signed_score_ge_neg_amplitude f psi d x
      have h2 : -B ≤ signedLabel f x * score psi d x := by linarith
      dsimp [D] at heB hehalf
      nlinarith
  have hs' : StrictlyRepresents f (correctedHeads phi psi ε) (c + ε * d) :=
    fun x ↦ hε.trans_le (hgap x)
  refine ⟨ε, hε, hs', (le_relativeMargin_iff hs').mpr fun x ↦ ?_⟩
  have hampl := corrected_amplitude_le phi psi c d hε.le
  have hbound : amplitude (correctedHeads phi psi ε) (c + ε * d) ≤ D + ε * B := by
    have hh := mul_le_mul_of_nonneg_left hamp hε.le
    dsimp [D]
    linarith
  have hγ : 0 ≤ τ / (3 * B) := by positivity
  calc
    τ / (3 * B) * amplitude (correctedHeads phi psi ε) (c + ε * d)
        ≤ τ / (3 * B) * (D + ε * B) := mul_le_mul_of_nonneg_left hbound hγ
    _ = ε * ((2 + τ) / 3) := by
      dsimp [ε]
      field_simp
    _ ≤ ε := by nlinarith
    _ ≤ _ := hgap x

end HeadComplexity.ExceptionalMarginRepair
