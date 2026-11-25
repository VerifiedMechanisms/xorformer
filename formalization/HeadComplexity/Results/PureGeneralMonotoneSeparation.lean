import HeadComplexity.Results.PureGeneralMonotonicity
import HeadComplexity.Results.ReplicatedMonotonicity
import HeadComplexity.Results.PureGeneralSeparationAllLargeInputs
import HeadComplexity.Results.RoPEUniversalBudgets

/-!
# Pure rotary separation among monotone Boolean functions

Every classifier in the explicit source family is coordinatewise monotone.
The full arbitrary-head separation therefore persists within monotone Boolean
functions, including at every sufficiently large input length after adjoining
ignored variables. The original vanilla minimum is used in the final statement.
-/

namespace HeadComplexity

open Filter

namespace PureGeneralReplicatedGrid

theorem classifier_monotone (H m : ℕ) : Monotone (classifier H m) := by
  intro x y hxy
  have hq (x : Fin (groupCount H * m) → Bool) (g : Fin (groupCount H)) :
      |coordinate x g| ≤ 1 := ReplicatedInputCopy.coordinate_abs_le_one x g
  have hxy' : ∀ g, coordinate x g ≤ coordinate y g :=
    ReplicatedInputCopy.coordinate_monotone (groupCount H) m hxy
  have hs := score_monotone_on_cube (hq x) (hq y) hxy'
  rw [Bool.le_iff_imp]
  simp only [classifier, decide_eq_true_eq]
  exact fun hx ↦ hx.trans_le hs

end PureGeneralReplicatedGrid

theorem exists_monotone_pure_not_vanilla_at_head_budget (H : ℕ) (hH : 3 ≤ H) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      Monotone f ∧ pureRoPEComputable n H f ∧ ¬ computableWithHeadsN n H f := by
  obtain ⟨m, hm, hmpos⟩ :=
    ((PureGeneralReplicatedGrid.eventually_not_vanilla_general H hH).and
      (eventually_gt_atTop (0 : ℕ))).exists
  refine ⟨_, PureGeneralReplicatedGrid.classifier H m,
    PureGeneralReplicatedGrid.classifier_monotone H m,
    PureGeneralReplicatedGrid.pure_computable H m hmpos, ?_⟩
  exact fun hc ↦ hm (computableWithSharedHeadsN_of_computableWithHeadsN hc)

/-- Restricting the universal question to monotone Boolean functions does
not change its sharp head-budget cutoff. -/
theorem universal_monotone_pure_to_vanilla_iff_head_le_two (H : ℕ) :
    (∀ (n : ℕ) (f : (Fin n → Bool) → Bool), Monotone f →
      pureRoPEComputable n H f → computableWithHeadsN n H f) ↔ H ≤ 2 := by
  constructor
  · intro h
    by_contra hH
    obtain ⟨n, f, hmono, hp, hv⟩ :=
      exists_monotone_pure_not_vanilla_at_head_budget H (by omega)
    exact hv (h n f hmono hp)
  · intro hH n f _ hp
    exact (universal_pure_to_original_vanilla_iff_head_le_two H).mpr hH n f hp

/-- Monotone counterexamples exist at every sufficiently large input length,
with exact pure minimum and the established vanilla interval. -/
theorem monotone_pureRoPE_separation_every_budget_every_large_input_length
    (H : ℕ) (hH : 3 ≤ H) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ f : (Fin n → Bool) → Bool,
      Monotone f ∧ PureRoPEHStar n f = H ∧ H + 1 ≤ HStar n f ∧
      HStar n f ≤ 2 ^ H - 2 ∧
      StandardPureRoPEHStar n f = H ∧ FreePureRoPEHStar n f = H := by
  obtain ⟨m, hm⟩ :=
    (PureGeneralReplicatedGrid.eventually_complexity_separation_general H hH).exists
  refine ⟨PureGeneralReplicatedGrid.groupCount H * m, fun n hn ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨InputPadding.classifier k (PureGeneralReplicatedGrid.classifier H m),
    InputPadding.classifier_monotone k
      (PureGeneralReplicatedGrid.classifier_monotone H m), ?_⟩
  simpa only [InputPadding.pureHStar_classifier,
    ← SharedHStar_eq_HStar, InputPadding.sharedHStar_classifier,
    InputPadding.standardHStar_classifier, InputPadding.freeHStar_classifier] using hm

end HeadComplexity
