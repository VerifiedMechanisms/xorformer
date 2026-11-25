import HeadComplexity.Research.NonnegativePartitionEmbedding
import HeadComplexity.Research.SignedCenteredCertificate

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.SameWidthPositiveNormalization
open Finset RelativeMarginQuantifiers MidrangeMarginCentering NonnegativePartitionEmbedding
open scoped BigOperators

variable {n H : ℕ}

/-- A positive normal form retaining the actual whole-cube amplitude. -/
def HasNormalizedMargin (n H : ℕ) (f : (Fin n → Bool) → Bool) (γ : ℝ) : Prop :=
  ∃ φ : Fin H → FracAtom n,
    (∀ h x, 0 ≤ (φ h).eval x) ∧
    (∀ h, ∃ x, (φ h).eval x = 0) ∧
    amplitude φ (-1) ≤ 3 ∧ StrictlyRepresents f φ (-1) ∧
    γ ≤ relativeMargin f φ (-1)

/-- Centered heads with nonpositive bias normalize at unchanged width. -/
theorem normalize_of_centered_nonpositive
    {f : (Fin n → Bool) → Bool} {φ : Fin H → FracAtom n} {bias γ : ℝ}
    (hs : StrictlyRepresents f φ bias) (hγ : γ ≤ relativeMargin f φ bias)
    (hb : bias ≤ 0) (hc : ∀ h, rangeMin (φ h) = -atomSup (φ h)) :
    HasNormalizedMargin n H f (γ/3) := by
  let A := amplitude φ bias
  have hA : 0 < A := amplitude_pos_of_strict hs
  have hAe : A = -bias+∑ h, atomSup (φ h) := by
    simp [A,amplitude,abs_of_nonpos hb]
  let ε := 1/A
  have hε : 0 < ε := div_pos zero_lt_one hA
  have hεA : ε*A = 1 := div_mul_cancel₀ _ hA.ne'
  let ψ : Fin H → FracAtom n := fun h => (minCenter (φ h)).scale ε
  have he (x : Fin n → Bool) : score ψ (-1) x = ε*score φ bias x := by
    simp only [score,ψ,FracAtom.scale_eval,minCenter_eval,hc,sub_neg_eq_add,
      ← Finset.mul_sum,Finset.sum_add_distrib]
    nlinarith [hεA]
  have hstrict : StrictlyRepresents f ψ (-1) := by
    intro x
    rw [he]
    have hh := mul_pos hε (hs x)
    nlinarith
  have hsum : ∑ h, atomSup (φ h) ≤ A := by rw [hAe]; linarith
  have hD : amplitude ψ (-1) ≤ 3 := by
    simp only [amplitude,abs_neg,abs_one,ψ,atomSup_scale,abs_of_pos hε,← Finset.mul_sum]
    have hc' := sum_le_sum (s := Finset.univ) fun h _ => minCenter_atomSup_le (φ h)
    simp only [← Finset.mul_sum] at hc'
    have hh := mul_le_mul_of_nonneg_left hc' hε.le
    have hh' := mul_le_mul_of_nonneg_left hsum hε.le
    nlinarith
  refine ⟨ψ,?_,?_,hD,hstrict,?_⟩
  · intro h x
    simp only [ψ,FracAtom.scale_eval]
    exact mul_nonneg hε.le (minCenter_nonneg (φ h) x)
  · intro h
    obtain ⟨x,hx⟩ := minCenter_has_zero (φ h)
    exact ⟨x,by simp [ψ,hx]⟩
  · have hr : 0 ≤ relativeMargin f φ bias := (relativeMargin_pos hs).le
    have hmargin : relativeMargin f φ bias / 3 ≤ relativeMargin f ψ (-1) := by
      apply (le_relativeMargin_iff hstrict).mpr
      intro x
      have hx := (le_relativeMargin_iff hs).mp (le_refl (relativeMargin f φ bias)) x
      have hm := mul_le_mul_of_nonneg_left hx hε.le
      calc
        relativeMargin f φ bias / 3 * amplitude ψ (-1) ≤ relativeMargin f φ bias := by nlinarith
        _ = ε*(relativeMargin f φ bias * amplitude φ bias) := by
          change _ = ε*(relativeMargin f φ bias*A)
          calc
            _ = relativeMargin f φ bias*(ε*A) := by rw [hεA]; ring
            _ = _ := by ring
        _ ≤ ε*(signedLabel f x*score φ bias x) := hm
        _ = signedLabel f x*score ψ (-1) x := by rw [he]; ring
    exact (div_le_div_of_nonneg_right hγ (by norm_num)).trans hmargin


/-- Every original margin certificate has a positive normal form at unchanged
width, for its labels or their global complement, with loss at most three. -/
theorem hasNormalizedMargin_or_complement
    {f : (Fin n → Bool) → Bool} {γ : ℝ}
    (hf : HasRelativeMargin n H f γ) :
    HasNormalizedMargin n H f (γ/3) ∨
      HasNormalizedMargin n H (fun x => !(f x)) (γ/3) := by
  obtain ⟨g,φ,b,hg,hb,hs,hm,hc⟩ :=
    SignedCenteredCertificate.exists_signed_centered_certificate hf
  have hn := normalize_of_centered_nonpositive hs hm hb hc
  rcases hg with rfl | rfl
  · exact Or.inl hn
  · exact Or.inr hn

/-- Original unrestricted computability reduces, up to complementation, to
bounded nonnegative min-zero heads without increasing their number. -/
theorem normalized_or_complement_of_computable
    {f : (Fin n → Bool) → Bool} (hf : computableWithHeadsN n H f) :
    HasNormalizedMargin n H f 0 ∨
      HasNormalizedMargin n H (fun x => !(f x)) 0 := by
  obtain ⟨γ,hγ,hfγ⟩ := exists_positive_margin_of_computable hf
  have hf0 : HasRelativeMargin n H f 0 := hasRelativeMargin_mono hγ.le hfγ
  simpa using hasNormalizedMargin_or_complement hf0

end HeadComplexity.SameWidthPositiveNormalization
