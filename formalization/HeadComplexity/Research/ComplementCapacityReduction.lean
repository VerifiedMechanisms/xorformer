import HeadComplexity.Research.RelativeMarginQuantifiers
import HeadComplexity.Research.SameWidthPositiveNormalization

set_option linter.style.header false

noncomputable section
namespace HeadComplexity.ComplementCapacityReduction
open RelativeMarginQuantifiers SameWidthPositiveNormalization

/-- An involutive choice of orientation loses at most a factor two in a
finite count. No injective parameterization of representations is needed. -/
theorem ncard_le_twice_of_involution {α : Type*} [Finite α]
    (source target : Set α) (τ : α → α) (hτ : Function.Involutive τ)
    (hcover : ∀ a ∈ source, a ∈ target ∨ τ a ∈ target) :
    source.ncard ≤ 2 * target.ncard := by
  have hsub : source ⊆ target ∪ τ '' target := by
    intro a ha
    rcases hcover a ha with h | h
    · exact Or.inl h
    · exact Or.inr ⟨τ a, h, hτ a⟩
  calc
    source.ncard ≤ (target ∪ τ '' target).ncard := Set.ncard_le_ncard hsub
    _ ≤ target.ncard + (τ '' target).ncard := Set.ncard_union_le _ _
    _ ≤ target.ncard + target.ncard := Nat.add_le_add_left Set.ncard_image_le _
    _ = 2 * target.ncard := by omega

/-- Specialization to full Boolean truth tables and simultaneous label
complementation. The operation acts on outputs, not on input coordinates. -/
theorem ncard_le_twice_of_complement {X : Type*} [Finite X]
    (source target : Set (X → Bool))
    (hcover : ∀ f ∈ source, f ∈ target ∨ (fun x => !(f x)) ∈ target) :
    source.ncard ≤ 2 * target.ncard := by
  apply ncard_le_twice_of_involution source target (fun f x => !(f x)) _ hcover
  intro f
  funext x
  exact Bool.not_not _

def normalizedFunctions (n H : ℕ) (γ : ℝ) : Set ((Fin n → Bool) → Bool) :=
  {f | HasNormalizedMargin n H f γ}

theorem normalized_subset_highMargin (n H : ℕ) (γ : ℝ) :
    normalizedFunctions n H γ ⊆ highMarginFunctions n H γ := by
  rintro f ⟨φ, _, _, _, hs, hm⟩
  exact ⟨φ, -1, hs, hm⟩

theorem normalized_card_le_original (n H : ℕ) (γ : ℝ) :
    (normalizedFunctions n H γ).ncard ≤ (headComputableFunctions n H).ncard := by
  apply Set.ncard_le_ncard (ht := Set.toFinite _)
  intro f hf
  exact computable_of_hasRelativeMargin (normalized_subset_highMargin n H γ hf)

/-- Every unrestricted table or its label complement has the positive normal
form, so its capacity can lose at most a factor two at unchanged width. -/
theorem original_card_le_twice_normalized (n H : ℕ) :
    (headComputableFunctions n H).ncard ≤ 2 * (normalizedFunctions n H 0).ncard := by
  apply ncard_le_twice_of_complement
  intro f hf
  exact normalized_or_complement_of_computable hf

/-- The analogous finite cover retains a quantitative source margin, losing
at most three in margin and two in truth-table count. -/
theorem highMargin_card_le_twice_normalized (n H : ℕ) (γ : ℝ) :
    (highMarginFunctions n H γ).ncard ≤
      2 * (normalizedFunctions n H (γ/3)).ncard := by
  apply ncard_le_twice_of_complement
  intro f hf
  exact hasNormalizedMargin_or_complement hf

end HeadComplexity.ComplementCapacityReduction
