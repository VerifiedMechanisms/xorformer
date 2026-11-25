import HeadComplexity.Results.PureThreeAveragedSeparation
import HeadComplexity.Results.PureThreeAveragedWitness
import HeadComplexity.Results.PureThreeReplicatedGridConsequences
import HeadComplexity.Results.RoPEGeneralBounds

set_option linter.style.header false

/-!
# A Boolean separation between pure rotary and vanilla attention

The explicit replicated-grid family is computable with three pure heads,
including literal standard-frequency and free-frequency rotary realizations.
For all sufficiently large replication counts it is not computable with
three vanilla heads in the unchanged shared-embedding architecture.

The proof is existential in the replication count. No numerical threshold
and no equality of real-valued scores are asserted.
-/

namespace HeadComplexity.PureThreeReplicatedGrid

open scoped Topology
open Filter

/-- The full lower bound, with no unproved witness or polynomial premise. -/
theorem eventually_not_vanilla_three :
    ∀ᶠ m in atTop, ¬ computableWithSharedHeadsN (18 * m) 3 (classifier m) := by
  filter_upwards [PureThreeSeparationLimit.eventually_no_physical_averaged_witness,
    eventually_gt_atTop (0 : ℕ)] with m hm hmpos
  intro hf
  exact hm (PureThreeAveragedWitness.averagedWitness_of_vanilla m hmpos hf)

/-- The explicit family eventually has pure minimum three and vanilla minimum
between four and six, under the unchanged shared-embedding definitions. -/
theorem eventually_complexity_separation :
    ∀ᶠ m in atTop,
      PureRoPEHStar (18 * m) (classifier m) = 3 ∧
      4 ≤ SharedHStar (18 * m) (classifier m) ∧
      SharedHStar (18 * m) (classifier m) ≤ 6 ∧
      StandardPureRoPEHStar (18 * m) (classifier m) = 3 ∧
      FreePureRoPEHStar (18 * m) (classifier m) = 3 := by
  filter_upwards [eventually_not_vanilla_three, eventually_gt_atTop (0 : ℕ)]
    with m hnot hm
  obtain ⟨hp, hv, hs, hf⟩ := complexities_of_not_vanilla_three m hm hnot
  have hupper := HStar_le_improved_exponential_pureRoPEHStar (classifier m)
    (by omega : 2 ≤ PureRoPEHStar (18 * m) (classifier m))
  rw [hp] at hupper
  norm_num at hupper
  rw [SharedHStar_eq_HStar]
  exact ⟨hp, hv, hupper, hs, hf⟩

theorem exists_complexity_separation :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      PureRoPEHStar n f = 3 ∧ 4 ≤ SharedHStar n f ∧ SharedHStar n f ≤ 6 ∧
      StandardPureRoPEHStar n f = 3 ∧ FreePureRoPEHStar n f = 3 := by
  obtain ⟨m, hm⟩ := eventually_complexity_separation.exists
  exact ⟨18 * m, classifier m, hm⟩

/-- Both literal rotary-frequency conventions realize a three-head classifier
which has no three-head vanilla representation. -/
theorem exists_rotary_three_not_vanilla_three :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      rectangularStandardPureRotaryComputable n 3 f ∧
      rectangularFreePureRotaryComputable n 3 f ∧
      ¬ computableWithSharedHeadsN n 3 f := by
  obtain ⟨m, hm, hmpos⟩ :=
    (eventually_not_vanilla_three.and (eventually_gt_atTop (0 : ℕ))).exists
  exact ⟨18 * m, classifier m, standard_computable m hmpos, free_computable m hmpos, hm⟩

end HeadComplexity.PureThreeReplicatedGrid

namespace HeadComplexity

/-- The requested universal reverse implication is false already at three heads. -/
theorem not_universal_pureRoPE_to_vanilla_three :
    ¬ (∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
      pureRoPEComputable n 3 f → computableWithSharedHeadsN n 3 f) := by
  intro h
  obtain ⟨n, f, hs, _, hv⟩ := PureThreeReplicatedGrid.exists_rotary_three_not_vanilla_three
  exact hv (h n f ((rectangularStandardPureRotaryComputable_iff_scalar n 3 f).mp hs))

/-- Consequently pure rotary and vanilla minimum head counts are not
universally equal. -/
theorem not_universal_pureRoPEHStar_eq_SharedHStar :
    ¬ (∀ (n : ℕ) (f : (Fin n → Bool) → Bool), PureRoPEHStar n f = SharedHStar n f) := by
  intro h
  obtain ⟨n, f, hp, hv, _⟩ := PureThreeReplicatedGrid.exists_complexity_separation
  have he := h n f
  omega

theorem not_universal_pureRoPEHStar_eq_HStar :
    ¬ (∀ (n : ℕ) (f : (Fin n → Bool) → Bool), PureRoPEHStar n f = HStar n f) := by
  intro h
  apply not_universal_pureRoPEHStar_eq_SharedHStar
  intro n f
  rw [SharedHStar_eq_HStar]
  exact h n f

theorem not_universal_standardPureRoPEHStar_eq_SharedHStar :
    ¬ (∀ (n : ℕ) (f : (Fin n → Bool) → Bool), StandardPureRoPEHStar n f = SharedHStar n f) := by
  intro h
  apply not_universal_pureRoPEHStar_eq_SharedHStar
  intro n f
  rw [← standardPureRoPEHStar_eq_scalar]
  exact h n f

theorem not_universal_freePureRoPEHStar_eq_SharedHStar :
    ¬ (∀ (n : ℕ) (f : (Fin n → Bool) → Bool), FreePureRoPEHStar n f = SharedHStar n f) := by
  intro h
  apply not_universal_pureRoPEHStar_eq_SharedHStar
  intro n f
  rw [← freePureRoPEHStar_eq_scalar]
  exact h n f

end HeadComplexity
