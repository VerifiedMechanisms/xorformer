module

public import HeadComplexity.Attention.WeightedSum

/-!
# Head complexity

The minimum feasible head budget exists by the weighted-sum construction.
Padding turns its least-element specification into the budget API.
-/

@[expose] public section

open scoped BigOperators

namespace HeadComplexity

variable {n H : ℕ} {f : (Fin n → Bool) → Bool}

/-- Every Boolean function on a finite cube is computable with some finite number of heads. -/
private theorem exists_computableWithHeads (f : (Fin n → Bool) → Bool) :
    ∃ H, ComputableWithHeads f H :=
  ⟨2 ^ n - 1, computableWithHeads_universal f⟩

/-- The least number of heads that compute a Boolean function. -/
@[no_expose]
noncomputable def headComplexity (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (exists_computableWithHeads f)

/-- A Boolean function is computable with its minimum number of heads. -/
theorem computableWithHeads_headComplexity (f : (Fin n → Bool) → Bool) :
    ComputableWithHeads f (headComplexity f) := by
  classical
  exact Nat.find_spec (exists_computableWithHeads f)

/-- Any feasible head budget is an upper bound on the head complexity. -/
theorem ComputableWithHeads.headComplexity_le (h : ComputableWithHeads f H) :
    headComplexity f ≤ H := by
  classical
  exact Nat.find_min' (exists_computableWithHeads f) h

/-- Head complexity is the least element of the set of feasible head budgets. -/
theorem isLeast_headComplexity (f : (Fin n → Bool) → Bool) :
    IsLeast {H | ComputableWithHeads f H} (headComplexity f) :=
  ⟨computableWithHeads_headComplexity f, fun _ h ↦ h.headComplexity_le⟩

/-- The head complexity is also the least number of admissible affine fractions whose sum, with
a constant, has the required signs. -/
theorem isLeast_headComplexity_affineFractions (f : (Fin n → Bool) → Bool) :
    IsLeast {H | ∃ (c : ℝ) (r : Fin H → Attention.AffineFraction n),
      (∀ h, (r h).Admissible) ∧ Function.SignRepresents (fun x ↦ c + ∑ h, (r h).eval x) f}
      (headComplexity f) := by
  simpa only [← computableWithHeads_iff_exists_affineFractions] using isLeast_headComplexity f

/-- The head complexity is at most a given budget exactly when that budget is feasible. -/
theorem headComplexity_le_iff_computableWithHeads :
    headComplexity f ≤ H ↔ ComputableWithHeads f H :=
  ⟨fun h ↦ (computableWithHeads_headComplexity f).mono h, fun h ↦ h.headComplexity_le⟩

/-- A budget is strictly below the head complexity exactly when no model at that budget computes
the function. -/
theorem lt_headComplexity_iff_not_computableWithHeads :
    H < headComplexity f ↔ ¬ComputableWithHeads f H := by
  rw [← not_le, headComplexity_le_iff_computableWithHeads]

/-- The minimum is the next budget exactly when the next budget is feasible and the current
budget is infeasible. -/
theorem headComplexity_eq_succ_iff :
    headComplexity f = H + 1 ↔ ComputableWithHeads f (H + 1) ∧ ¬ComputableWithHeads f H := by
  rw [← headComplexity_le_iff_computableWithHeads, ← lt_headComplexity_iff_not_computableWithHeads]
  constructor
  · intro h
    exact ⟨h.le, h.symm ▸ Nat.lt_succ_self H⟩
  · rintro ⟨hle, hlt⟩
    exact Nat.le_antisymm hle (Nat.succ_le_of_lt hlt)

/-- If a Boolean function depends only on a positive weighted sum, one fewer head than the
number of distinct sum values suffices. -/
theorem headComplexity_le_of_factorsThrough_weightedSum (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hf : f.FactorsThrough (weightedSum w)) :
    headComplexity f ≤ (Finset.univ.image (weightedSum w)).card - 1 :=
  (computableWithHeads_of_factorsThrough_weightedSum w hw hf).headComplexity_le

/-- Every Boolean function of `n` bits is computable with at most `2 ^ n - 1` heads. -/
theorem headComplexity_le_two_pow_sub_one (f : (Fin n → Bool) → Bool) :
    headComplexity f ≤ 2 ^ n - 1 :=
  (computableWithHeads_universal f).headComplexity_le

end HeadComplexity
