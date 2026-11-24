import HeadComplexity.Model.PureRoPE

set_option linter.style.header false

/-! # Position-index and residual conventions for literal pure rotary attention

The model uses positions 0,...,n-1 for bits and n for the query. Simultaneously
shifting every position preserves logits exactly, so the one-indexed positions
1,...,n and n+1 in the mathematical specification give the identical model.
Separate model and head dimensions, output projections, query self-attention,
and the fixed residual token are precisely the conventions of `model.md`.
-/

namespace HeadComplexity.RoPEArchitectureConventions

noncomputable section
open scoped InnerProductSpace

theorem rotate_inner_shift {m : ℕ} (p q c : ℝ) (k v : Vec (m * 2)) :
    ⟪PureRoPERotation.rotate m (p + c) k,
      PureRoPERotation.rotate m (q + c) v⟫_ℝ =
      ⟪PureRoPERotation.rotate m p k, PureRoPERotation.rotate m q v⟫_ℝ := by
  have hsub : (p + c) - (q + c) = p - q := by ring
  rw [PureRoPERotation.rotate_inner_relative, PureRoPERotation.rotate_inner_relative, hsub]

def oneIndexedPosition {n : ℕ} (p : SeqPos n) : ℝ := pureRoPEPosition p + 1

@[simp] theorem oneIndexedPosition_bit {n : ℕ} (i : Fin n) :
    oneIndexedPosition (some i) = (i.val : ℝ) + 1 := rfl

@[simp] theorem oneIndexedPosition_query {n : ℕ} :
    oneIndexedPosition (none : SeqPos n) = (n : ℝ) + 1 := rfl

theorem oneIndexed_logit_eq {n d m H : ℕ} (M : PureRoPEFamily n d m H)
    (h : Fin H) (p : SeqPos n) (t : Fin 3) :
    ⟪PureRoPERotation.rotate m (oneIndexedPosition p) (M.WK h (M.tokenEmbed t)),
      PureRoPERotation.rotate m (oneIndexedPosition (none : SeqPos n))
        (M.WQ h (M.tokenEmbed 2))⟫_ℝ =
      ⟪PureRoPERotation.rotate m (pureRoPEPosition p) (M.WK h (M.tokenEmbed t)),
        PureRoPERotation.rotate m n (M.WQ h (M.tokenEmbed 2))⟫_ℝ := by
  exact rotate_inner_shift (pureRoPEPosition p) n 1 _ _

theorem oneIndexed_weight_eq {n d m H : ℕ} (M : PureRoPEFamily n d m H)
    (h : Fin H) (p : SeqPos n) (t : Fin 3) :
    Real.exp ⟪PureRoPERotation.rotate m (oneIndexedPosition p) (M.WK h (M.tokenEmbed t)),
      PureRoPERotation.rotate m (oneIndexedPosition (none : SeqPos n))
        (M.WQ h (M.tokenEmbed 2))⟫_ℝ = M.weight h p t := by
  rw [oneIndexed_logit_eq]
  rfl

/-- Query self-attention is present and agrees under the same index shift. -/
theorem oneIndexed_query_weight_eq {n d m H : ℕ} (M : PureRoPEFamily n d m H)
    (h : Fin H) :
    Real.exp ⟪PureRoPERotation.rotate m ((n : ℝ) + 1) (M.WK h (M.tokenEmbed 2)),
      PureRoPERotation.rotate m ((n : ℝ) + 1) (M.WQ h (M.tokenEmbed 2))⟫_ℝ =
      M.weight h none 2 :=
  oneIndexed_weight_eq M h none 2

/-- The residual connection changes only the freely chosen readout threshold. -/
theorem residual_computability_iff {n d m H : ℕ} (M : PureRoPEFamily n d m H)
    (f : (Fin n → Bool) → Bool) :
    computesPred f M.residual ↔ computesPred f M.attnUpdate :=
  M.computesPred_residual_iff_attnUpdate f

end
end HeadComplexity.RoPEArchitectureConventions
