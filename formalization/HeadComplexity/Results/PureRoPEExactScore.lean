import HeadComplexity.Model.PureRoPERealization

set_option linter.style.header false

/-! # Exact score and positive-weight realization by literal pure RoPE

These statements concern exact real values, including the full residual stream.
The Boolean separation uses the independently proved universal vanilla lower
bound; an exact-score comparison alone is not used as a Boolean lower bound.
-/

namespace HeadComplexity

noncomputable section
open scoped BigOperators InnerProductSpace

/-- At every head count, the literal standard-frequency architecture has
exactly the pure scalar normal form, including an arbitrary affine readout
from the full residual stream. -/
theorem pureRoPE_residual_score_iff_atoms {n H : ℕ}
    (Φ : (Fin n → Bool) → ℝ) :
    (∃ (d m : ℕ), 0 < d ∧ 0 < m ∧
      ∃ M : PureRoPEFamily n d m H, ∃ (w : Vec d) (τ : ℝ),
        ∀ x, ⟪w, M.residual x⟫_ℝ - τ = Φ x) ↔
      ∃ (p : Fin H → PureRoPEAtom n) (c : ℝ),
        ∀ x, c + ∑ h, (p h).eval x = Φ x := by
  constructor
  · rintro ⟨d, m, _, _, M, w, τ, hscore⟩
    refine ⟨M.scalarAtom w, ⟪w, M.tokenEmbed 2⟫_ℝ - τ, ?_⟩
    intro x
    have hx := hscore x
    rw [PureRoPEFamily.residual, inner_add_right, M.readout_eq_atoms w x] at hx
    linarith
  · rintro ⟨p, c, hp⟩
    obtain ⟨M, _, _, _, _, hresidual⟩ := PureRoPERealization.exists_family p
    refine ⟨3, n + 2, by omega, by omega, M, RoPETokenMaps.embedding 0, -c, ?_⟩
    intro x
    rw [hresidual x]
    have hx := hp x
    linarith

/-- Any prescribed positive token-position attention weights and positive
query self-weight are simultaneously realized by standard fixed-frequency
rotary matrices. The head count is unchanged, all heads share three token
embeddings, and the explicit head width is `2*(n+2)`. -/
theorem pureRoPE_exists_exact_positive_weights {n H : ℕ}
    (a b : Fin H → Fin n → ℝ) (γ : Fin H → ℝ)
    (ha : ∀ h i, 0 < a h i) (hb : ∀ h i, 0 < b h i) (hγ : ∀ h, 0 < γ h) :
    ∃ M : PureRoPEFamily n 3 (n + 2) H,
      (∀ h i, M.weight h (some i) 0 = a h i) ∧
      (∀ h i, M.weight h (some i) 1 = b h i) ∧
      (∀ h, M.weight h none 2 = γ h) := by
  let p : Fin H → PureRoPEAtom n := fun h ↦
    { a := a h
      b := b h
      γ := γ h
      η := 0
      v₀ := 0
      v₁ := 0
      ha := ha h
      hb := hb h
      hγ := hγ h }
  obtain ⟨M, hzero, hone, hquery, _, _⟩ := PureRoPERealization.exists_family p
  exact ⟨M, hzero, hone, hquery⟩

end
end HeadComplexity
