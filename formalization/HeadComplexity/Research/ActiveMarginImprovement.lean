import HeadComplexity.Research.MarginInvariance

set_option linter.style.header false

/-! A correction that improves every active margin constraint improves the
whole finite truth table for a sufficiently small positive step. This is a
local statement; it supplies no bound on the step or repeated width growth. -/

noncomputable section

namespace HeadComplexity.ActiveMarginImprovement

open scoped BigOperators
open RelativeMarginQuantifiers

/-- Strict improvement on the zero-slack coordinates persists on a finite set. -/
theorem finite_positive_perturbation {X : Type*} [Finite X] [Nonempty X]
    (a b : X → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hb : ∀ x, a x = 0 → 0 < b x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, 0 < a x + ε * b x := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  have hlocal (x : X) : ∃ d : ℝ, 0 < d ∧
      ∀ t : ℝ, 0 < t → t ≤ d → 0 < a x + t * b x := by
    by_cases hx : a x = 0
    · refine ⟨1, one_pos, fun t ht _ ↦ ?_⟩
      rw [hx, zero_add]
      exact mul_pos ht (hb x hx)
    · have hax : 0 < a x := lt_of_le_of_ne (ha x) (Ne.symm hx)
      refine ⟨a x / (2 * (|b x| + 1)), by positivity, ?_⟩
      intro t ht htd
      have hprod : t * (2 * (|b x| + 1)) ≤ a x :=
        (le_div_iff₀ (by positivity : 0 < 2 * (|b x| + 1))).mp htd
      have habs := abs_nonneg (b x)
      have hlo := neg_abs_le (b x)
      have hmul := mul_le_mul_of_nonneg_left hlo ht.le
      nlinarith
  choose d hd hstep using hlocal
  let ε := Finset.univ.inf' Finset.univ_nonempty d
  have hε : 0 < ε := by
    change 0 < Finset.univ.inf' Finset.univ_nonempty d
    rw [Finset.lt_inf'_iff]
    exact fun x _ ↦ hd x
  exact ⟨ε, hε, fun x ↦ hstep x ε hε (Finset.inf'_le _ (Finset.mem_univ x))⟩

variable {n H K : ℕ}

def correctedHeads (phi : Fin H → FracAtom n) (psi : Fin K → FracAtom n)
    (ε : ℝ) : Fin (H + K) → FracAtom n :=
  Fin.addCases phi (fun h ↦ (psi h).scale ε)

theorem corrected_score (phi : Fin H → FracAtom n) (psi : Fin K → FracAtom n)
    (c d ε : ℝ) (x : Fin n → Bool) :
    score (correctedHeads phi psi ε) (c + ε * d) x =
      score phi c x + ε * score psi d x := by
  simp [score, correctedHeads, Fin.sum_univ_add, mul_add, Finset.mul_sum]
  ring

theorem corrected_amplitude_le (phi : Fin H → FracAtom n)
    (psi : Fin K → FracAtom n) (c d : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    amplitude (correctedHeads phi psi ε) (c + ε * d) ≤
      amplitude phi c + ε * amplitude psi d := by
  simp only [amplitude, correctedHeads, Fin.sum_univ_add, Fin.addCases_left,
    Fin.addCases_right, atomSup_scale, abs_of_nonneg hε, ← Finset.mul_sum]
  have hh := abs_add_le c (ε * d)
  rw [abs_mul, abs_of_nonneg hε] at hh
  nlinarith

/-- Improving all active full-cube constraints gives a genuine original-model
representation at width H+K with strictly larger relative margin. The theorem
does not assert a quantitative gain or a bounded-width iteration. -/
theorem exists_strict_margin_improvement
    (f : (Fin n → Bool) → Bool)
    (phi : Fin H → FracAtom n) (psi : Fin K → FracAtom n) (c d : ℝ)
    (hs : StrictlyRepresents f phi c)
    (hactive : ∀ x,
      signedLabel f x * score phi c x = relativeMargin f phi c * amplitude phi c →
      relativeMargin f phi c * amplitude psi d < signedLabel f x * score psi d x) :
    ∃ ε : ℝ, 0 < ε ∧
      StrictlyRepresents f (correctedHeads phi psi ε) (c + ε * d) ∧
      relativeMargin f phi c <
        relativeMargin f (correctedHeads phi psi ε) (c + ε * d) := by
  let γ := relativeMargin f phi c
  let D := amplitude phi c
  let E := amplitude psi d
  let a := fun x ↦ signedLabel f x * score phi c x - γ * D
  let b := fun x ↦ signedLabel f x * score psi d x - γ * E
  have hg : 0 < γ := relativeMargin_pos hs
  have ha : ∀ x, 0 ≤ a x := by
    intro x
    have hx := (le_relativeMargin_iff hs).mp (le_refl (relativeMargin f phi c)) x
    dsimp [a, γ, D]
    linarith
  have hb : ∀ x, a x = 0 → 0 < b x := by
    intro x hx
    have he : signedLabel f x * score phi c x = γ * D := by
      dsimp [a] at hx
      linarith
    have hp := hactive x he
    dsimp [b, γ, E]
    linarith
  obtain ⟨ε, hε, hp⟩ := finite_positive_perturbation a b ha hb
  have hamp := corrected_amplitude_le phi psi c d hε.le
  have hstrict (x : Fin n → Bool) :
      γ * amplitude (correctedHeads phi psi ε) (c + ε * d) <
        signedLabel f x * score (correctedHeads phi psi ε) (c + ε * d) x := by
    have hh := hp x
    dsimp [a, b] at hh
    rw [corrected_score]
    have hm := mul_le_mul_of_nonneg_left hamp hg.le
    dsimp [D, E] at hh
    nlinarith
  have hs' : StrictlyRepresents f (correctedHeads phi psi ε) (c + ε * d) := by
    intro x
    exact lt_of_le_of_lt
      (mul_nonneg hg.le (amplitude_nonneg _ _)) (hstrict x)
  refine ⟨ε, hε, hs', ?_⟩
  change γ < minimumSignedScore f (correctedHeads phi psi ε) (c + ε * d) /
    amplitude (correctedHeads phi psi ε) (c + ε * d)
  rw [lt_div_iff₀ (amplitude_pos_of_strict hs')]
  unfold minimumSignedScore
  rw [Finset.lt_inf'_iff]
  exact fun x _ ↦ hstrict x

/-- A unit-gap interpolant on the active set suffices when its amplitude is
strictly below the reciprocal of the current margin. -/
theorem exists_improvement_of_active_interpolation
    (f : (Fin n → Bool) → Bool)
    (phi : Fin H → FracAtom n) (psi : Fin K → FracAtom n) (c d B : ℝ)
    (hs : StrictlyRepresents f phi c) (hB : amplitude psi d ≤ B)
    (hsmall : relativeMargin f phi c * B < 1)
    (hactive : ∀ x,
      signedLabel f x * score phi c x = relativeMargin f phi c * amplitude phi c →
      1 ≤ signedLabel f x * score psi d x) :
    ∃ ε : ℝ, 0 < ε ∧
      StrictlyRepresents f (correctedHeads phi psi ε) (c + ε * d) ∧
      relativeMargin f phi c <
        relativeMargin f (correctedHeads phi psi ε) (c + ε * d) := by
  apply exists_strict_margin_improvement f phi psi c d hs
  intro x hx
  have hm := mul_le_mul_of_nonneg_left hB (relativeMargin_pos hs).le
  exact (hm.trans_lt hsmall).trans_le (hactive x hx)

end HeadComplexity.ActiveMarginImprovement
