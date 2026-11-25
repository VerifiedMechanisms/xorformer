import HeadComplexity.Research.RelativeMarginQuantifiers
import HeadComplexity.Atoms.Restriction

set_option linter.style.header false

noncomputable section
namespace HeadComplexity.RelativeMarginRestriction
open RelativeMarginQuantifiers
open scoped BigOperators

variable {m n H : ℕ}

theorem atomSup_restrict_le (φ : FracAtom n) (ρ : CoordFace m n) :
    atomSup (φ.restrict ρ) ≤ atomSup φ := by
  unfold atomSup
  apply Finset.sup'_le
  intro x _
  rw [FracAtom.restrict_eval]
  exact abs_eval_le_atomSup φ (ρ.apply x)

theorem amplitude_restrict_le (φ : Fin H → FracAtom n) (c : ℝ)
    (ρ : CoordFace m n) :
    amplitude (fun h => (φ h).restrict ρ) c ≤ amplitude φ c := by
  unfold amplitude
  exact add_le_add le_rfl (Finset.sum_le_sum fun h _ => atomSup_restrict_le (φ h) ρ)

theorem score_restrict (φ : Fin H → FracAtom n) (c : ℝ)
    (ρ : CoordFace m n) (x : Fin m → Bool) :
    score (fun h => (φ h).restrict ρ) c x = score φ c (ρ.apply x) := by
  simp [score]

theorem relativeMargin_restrict_ge {f : (Fin n → Bool) → Bool}
    {φ : Fin H → FracAtom n} {c : ℝ} (hs : StrictlyRepresents f φ c)
    (ρ : CoordFace m n) :
    relativeMargin f φ c ≤ relativeMargin (fun x => f (ρ.apply x))
      (fun h => (φ h).restrict ρ) c := by
  have hs' : StrictlyRepresents (fun x => f (ρ.apply x))
      (fun h => (φ h).restrict ρ) c := by
    intro x
    simpa [signedLabel, score_restrict] using hs (ρ.apply x)
  apply (le_relativeMargin_iff hs').mpr
  intro x
  have h := (le_relativeMargin_iff hs).mp (le_refl _) (ρ.apply x)
  have ha := mul_le_mul_of_nonneg_left (amplitude_restrict_le φ c ρ)
    (relativeMargin_pos hs).le
  simpa [signedLabel, score_restrict] using ha.trans h

theorem hasRelativeMargin_restrict {f : (Fin n → Bool) → Bool} {γ : ℝ}
    (hf : HasRelativeMargin n H f γ) (ρ : CoordFace m n) :
    HasRelativeMargin m H (fun x => f (ρ.apply x)) γ := by
  obtain ⟨φ,c,hs,hγ⟩ := hf
  refine ⟨fun h => (φ h).restrict ρ, c, ?_, hγ.trans (relativeMargin_restrict_ge hs ρ)⟩
  intro x
  simpa [signedLabel, score_restrict] using hs (ρ.apply x)

end HeadComplexity.RelativeMarginRestriction
