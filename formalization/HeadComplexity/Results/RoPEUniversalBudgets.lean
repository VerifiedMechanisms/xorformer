import HeadComplexity.Results.PureGeneralSeparation
import HeadComplexity.Results.RoPEBoundaryCases
import HeadComplexity.Model.PureRoPEHeadSchedules

set_option linter.style.header false

/-!
# The universal pure-to-vanilla implication holds exactly through two heads

This classifies every head budget. Zero input lengths and zero heads are
included in the universal quantifiers. Literal fixed-frequency and free-frequency
rotary attention have the same classification by the exact scalar bridge.
-/

namespace HeadComplexity

open Filter

/-- Every head budget above two has an actual Boolean counterexample. -/
theorem exists_pure_not_vanilla_at_head_budget (H : ℕ) (hH : 3 ≤ H) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      pureRoPEComputable n H f ∧ ¬ computableWithSharedHeadsN n H f := by
  obtain ⟨m, hm, hmpos⟩ :=
    ((PureGeneralReplicatedGrid.eventually_not_vanilla_general H hH).and
      (eventually_gt_atTop (0 : ℕ))).exists
  exact ⟨_, PureGeneralReplicatedGrid.classifier H m,
    PureGeneralReplicatedGrid.pure_computable H m hmpos, hm⟩

/-- The universal head-preserving reverse implication is valid exactly for
zero, one, and two heads. -/
theorem universal_pure_to_vanilla_iff_head_le_two (H : ℕ) :
    (∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
      pureRoPEComputable n H f → computableWithSharedHeadsN n H f) ↔ H ≤ 2 := by
  constructor
  · intro h
    by_contra hH
    obtain ⟨n, f, hp, hv⟩ := exists_pure_not_vanilla_at_head_budget H (by omega)
    exact hv (h n f hp)
  · intro hH n f hp
    exact (pureRoPEComputable_iff_vanilla_of_le_two f hH).mp hp

theorem universal_pure_vanilla_budget_equivalence_iff_head_le_two (H : ℕ) :
    (∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
      pureRoPEComputable n H f ↔ computableWithSharedHeadsN n H f) ↔ H ≤ 2 := by
  constructor
  · intro h
    exact (universal_pure_to_vanilla_iff_head_le_two H).mp
      (fun n f ↦ (h n f).mp)
  · intro hH n f
    exact pureRoPEComputable_iff_vanilla_of_le_two f hH

/-- The same complete classification for literal standard fixed frequencies. -/
theorem universal_standard_rotary_to_vanilla_iff_head_le_two (H : ℕ) :
    (∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
      rectangularStandardPureRotaryComputable n H f →
        computableWithSharedHeadsN n H f) ↔ H ≤ 2 := by
  constructor
  · intro h
    apply (universal_pure_to_vanilla_iff_head_le_two H).mp
    intro n f hp
    exact h n f ((rectangularStandardPureRotaryComputable_iff_scalar n H f).mpr hp)
  · intro hH n f hp
    apply (pureRoPEComputable_iff_vanilla_of_le_two f hH).mp
    exact (rectangularStandardPureRotaryComputable_iff_scalar n H f).mp hp

/-- The same complete classification for literal freely chosen frequencies. -/
theorem universal_free_rotary_to_vanilla_iff_head_le_two (H : ℕ) :
    (∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
      rectangularFreePureRotaryComputable n H f →
        computableWithSharedHeadsN n H f) ↔ H ≤ 2 := by
  constructor
  · intro h
    apply (universal_pure_to_vanilla_iff_head_le_two H).mp
    intro n f hp
    exact h n f ((rectangularFreePureRotaryComputable_iff_scalar n H f).mpr hp)
  · intro hH n f hp
    apply (pureRoPEComputable_iff_vanilla_of_le_two f hH).mp
    exact (rectangularFreePureRotaryComputable_iff_scalar n H f).mp hp

/-- Allowing each head to choose its own frequencies gives the same complete
classification, including zero inputs and zero heads. -/
theorem universal_headwise_free_rotary_to_vanilla_iff_head_le_two (H : ℕ) :
    (∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
      rectangularHeadwiseFreePureRotaryComputable n H f →
        computableWithSharedHeadsN n H f) ↔ H ≤ 2 := by
  constructor
  · intro h
    apply (universal_pure_to_vanilla_iff_head_le_two H).mp
    intro n f hp
    exact h n f ((rectangularHeadwiseFreePureRotaryComputable_iff_scalar n H f).mpr hp)
  · intro hH n f hp
    apply (pureRoPEComputable_iff_vanilla_of_le_two f hH).mp
    exact (rectangularHeadwiseFreePureRotaryComputable_iff_scalar n H f).mp hp

end HeadComplexity
