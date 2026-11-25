import HeadComplexity.Research.MidrangeMarginCentering
import HeadComplexity.Research.MarginInvariance

set_option linter.style.header false

noncomputable section
namespace HeadComplexity.SignedCenteredCertificate
open Finset RelativeMarginQuantifiers MidrangeMarginCentering
open scoped BigOperators

variable {n H : ℕ}

theorem rangeMax_eq_atomSup_of_centered (φ : FracAtom n)
    (hcenter : rangeMin φ + rangeMax φ = 0) : rangeMax φ = atomSup φ := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro x hx
    exact (le_abs_self _).trans (abs_eval_le_atomSup φ x)
  · apply Finset.sup'_le
    intro x hx
    apply abs_le.mpr
    constructor
    · linarith [rangeMin_le_eval φ x]
    · exact eval_le_rangeMax φ x

theorem rangeMin_eq_neg_atomSup_of_centered (φ : FracAtom n)
    (hcenter : rangeMin φ + rangeMax φ = 0) : rangeMin φ = -atomSup φ := by
  rw [rangeMax_eq_atomSup_of_centered φ hcenter] at hcenter
  linarith

theorem rangeMin_negate_eq (φ : FracAtom n)
    (hcenter : rangeMin φ + rangeMax φ = 0) :
    rangeMin (φ.scale (-1)) = -atomSup (φ.scale (-1)) := by
  have hsup : atomSup (φ.scale (-1)) = atomSup φ := by simp [atomSup_scale]
  rw [hsup]
  apply le_antisymm
  · obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_sup'
      (Finset.univ_nonempty : (Finset.univ : Finset (Fin n → Bool)).Nonempty) φ.eval
    have hh := rangeMin_le_eval (φ.scale (-1)) x
    change rangeMax φ = φ.eval x at he
    rw [← rangeMax_eq_atomSup_of_centered φ hcenter]
    simp only [FracAtom.scale_eval, neg_one_mul] at hh
    linarith
  · apply Finset.le_inf'
    intro x hx
    simp only [FracAtom.scale_eval, neg_one_mul]
    exact neg_le_neg ((le_abs_self _).trans (abs_eval_le_atomSup φ x))

theorem signedLabel_complement (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    signedLabel (fun y => !(f y)) x = -signedLabel f x := by
  cases hf : f x <;> simp [signedLabel,hf]

theorem negate_score (φ : Fin H → FracAtom n) (b : ℝ) (x : Fin n → Bool) :
    score (fun h => (φ h).scale (-1)) (-b) x = -score φ b x := by
  simpa using score_scale φ b (-1) x

theorem negate_relativeMargin (f : (Fin n → Bool) → Bool)
    (φ : Fin H → FracAtom n) (b : ℝ) :
    relativeMargin (fun x => !(f x)) (fun h => (φ h).scale (-1)) (-b) =
      relativeMargin f φ b := by
  have ha : amplitude (fun h => (φ h).scale (-1)) (-b) = amplitude φ b := by
    simpa using amplitude_scale φ b (-1)
  have hm : minimumSignedScore (fun x => !(f x))
      (fun h => (φ h).scale (-1)) (-b) = minimumSignedScore f φ b := by
    unfold minimumSignedScore
    simp_rw [signedLabel_complement, negate_score, neg_mul_neg]
  unfold relativeMargin
  rw [hm,ha]

/-- At unchanged original width, either the table or its complement has
centered genuine heads, a nonpositive bias, and at least the original margin.
Each centered head has its minimum exactly opposite its full-cube norm. -/
theorem exists_signed_centered_certificate
    {f : (Fin n → Bool) → Bool} {γ : ℝ} (hf : HasRelativeMargin n H f γ) :
    ∃ (g : (Fin n → Bool) → Bool) (φ : Fin H → FracAtom n) (b : ℝ),
      (g = f ∨ g = (fun x => !(f x))) ∧ b ≤ 0 ∧
      StrictlyRepresents g φ b ∧ γ ≤ relativeMargin g φ b ∧
      ∀ h, rangeMin (φ h) = -atomSup (φ h) := by
  obtain ⟨φ,b,hs,hmargin,hcenter⟩ := exists_centered_certificate hf
  by_cases hb : b ≤ 0
  · exact ⟨f,φ,b,Or.inl rfl,hb,hs,hmargin,
      fun h => rangeMin_eq_neg_atomSup_of_centered (φ h) (hcenter h)⟩
  · refine ⟨(fun x => !(f x)),(fun h => (φ h).scale (-1)), -b,
      Or.inr rfl,?_,?_,?_,fun h => rangeMin_negate_eq (φ h) (hcenter h)⟩
    · linarith
    · intro x
      rw [signedLabel_complement, negate_score, neg_mul_neg]
      exact hs x
    · simpa only [negate_relativeMargin] using hmargin

end HeadComplexity.SignedCenteredCertificate
