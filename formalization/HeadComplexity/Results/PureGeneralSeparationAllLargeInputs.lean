import HeadComplexity.Results.PureGeneralSeparation
import HeadComplexity.Results.InputPaddingInvariance

set_option linter.style.header false

/-!
# Separation at every large input length and every head budget above two

Exact invariance under adjoining unused inputs transports the replicated-grid
separation to every sufficiently large input length. The original vanilla
architecture, strict Boolean threshold, and both rotary frequency conventions
are retained.
-/

namespace HeadComplexity

/-- For each head budget above two, every sufficiently large input length
has a Boolean function with that exact pure rotary minimum and a strictly
larger vanilla minimum. -/
theorem pureRoPE_separation_every_budget_every_large_input_length
    (H : ℕ) (hH : 3 ≤ H) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ f : (Fin n → Bool) → Bool,
      PureRoPEHStar n f = H ∧ H + 1 ≤ SharedHStar n f ∧
      SharedHStar n f ≤ 2 ^ H - 2 ∧
      StandardPureRoPEHStar n f = H ∧ FreePureRoPEHStar n f = H := by
  obtain ⟨m, hm⟩ :=
    (PureGeneralReplicatedGrid.eventually_complexity_separation_general H hH).exists
  refine ⟨PureGeneralReplicatedGrid.groupCount H * m, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨InputPadding.classifier k (PureGeneralReplicatedGrid.classifier H m), ?_⟩
  simpa only [InputPadding.pureHStar_classifier, InputPadding.sharedHStar_classifier,
    InputPadding.standardHStar_classifier, InputPadding.freeHStar_classifier] using hm

end HeadComplexity
