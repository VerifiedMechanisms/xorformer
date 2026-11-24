import HeadComplexity.Results.PureRoPEReplicationStrict
import HeadComplexity.Results.ThreeFractionsSevenHeads

set_option linter.style.header false

/-!
# Formalized upper bounds for the explicit replicated function

These are unconditional upper bounds in the existing models. The complete
vanilla lower bound and exact pure minimum are proved in
Results/PureRoPEExplicitSeparation.lean, which imports this module.
-/

namespace HeadComplexity.PureRoPEReplicationBounds

open PureRoPEReplication PureRoPEReplicationStrict

theorem explicit_pureHStar_le_three :
    PureRoPEHStar (14 * replicationCount) explicitUnshiftedFunction ≤ 3 := by
  classical
  exact Nat.find_min' _ explicitUnshiftedFunction_pure_three

/-- The seven heads inhabit the literal shared-embedding vanilla model. -/
theorem explicit_shared_vanilla_seven :
    computableWithSharedHeadsN (14 * replicationCount) 7 explicitUnshiftedFunction :=
  vanilla_seven_of_pureRoPE_three explicitUnshiftedFunction_pure_three

theorem explicit_sharedHStar_le_seven :
    SharedHStar (14 * replicationCount) explicitUnshiftedFunction ≤ 7 := by
  classical
  have hex : ∃ k, computableWithSharedHeadsN (14 * replicationCount) k
      explicitUnshiftedFunction := ⟨7, explicit_shared_vanilla_seven⟩
  unfold SharedHStar
  rw [dif_pos hex]
  exact Nat.find_min' hex explicit_shared_vanilla_seven

theorem explicit_vanillaHStar_le_seven :
    HStar (14 * replicationCount) explicitUnshiftedFunction ≤ 7 := by
  simpa only [SharedHStar_eq_HStar] using explicit_sharedHStar_le_seven

end HeadComplexity.PureRoPEReplicationBounds
