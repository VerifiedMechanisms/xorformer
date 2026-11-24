import HeadComplexity.Polynomial.PureCubicOrientedBase
import HeadComplexity.Results.ThreeFractionsFiveHeads

set_option linter.style.header false

/-! # Five vanilla heads suffice for the explicit replicated separation -/

namespace HeadComplexity.PureRoPEReplicationFive

noncomputable section
open RoPETwoHead PureRoPEReplication PureRoPEReplicationStrict
open PureCubicOrientedBase ThreeFractionsSevenHeads

def shiftedNumerators {m : ℕ} : Fin 3 → Form (14 * m) :=
  ![(numeratorForm 0).lin (denominatorForm 0) 1 (bias m),
    numeratorForm 1, numeratorForm 2]

theorem shifted_cubic {m : ℕ} (x : Fin (14 * m) → Bool) :
    cubic shiftedNumerators denominatorForm x = clearedScore (bias m) x := by
  simp only [cubic, shiftedNumerators, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Form.lin_eval, numeratorForm_eval,
    denominatorForm_eval, clearedScore, ThreeHeadCubicFace.cleared]
  ring

theorem shifted_cubic_ne {m : ℕ} (hm : 0 < m) (x : Fin (14 * m) → Bool) :
    cubic shiftedNumerators denominatorForm x ≠ 0 := by
  rw [shifted_cubic, clearedScore_eq hm]
  have hs : score (bias m) x ≠ 0 := by
    intro hz
    have hh := (full_cube_strict hm x).2
    rw [hz, abs_zero] at hh
    exact (not_le_of_gt (epsilon_positive hm)) hh
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (denominator_positive hm x 0).ne'
    (denominator_positive hm x 1).ne') (denominator_positive hm x 2).ne') hs

/-- The result is in the literal shared-embedding vanilla architecture. -/
theorem unshifted_shared_vanilla_five {m : ℕ} (hm : 0 < m) :
    computableWithSharedHeadsN (14 * m) 5 (unshiftedFunction (m := m)) := by
  apply ThreeFractionsFiveHeads.computable_five shiftedNumerators denominatorForm
    baseForm 10 unshiftedFunction
  · intro x
    exact lt_trans (by norm_num) (baseForm_gt_eight hm x)
  · exact Or.inr (baseForm_slopes hm)
  · exact baseForm_relation
  · exact shifted_cubic_ne hm
  · intro x
    rw [shifted_cubic]
    exact (full_cube_sign hm (bias m) x).trans
      (by rw [biasedFunction_eq_unshifted hm])

theorem explicit_shared_vanilla_five :
    computableWithSharedHeadsN (14 * replicationCount) 5 explicitUnshiftedFunction :=
  unshifted_shared_vanilla_five replicationCount_positive

theorem explicit_sharedHStar_le_five :
    SharedHStar (14 * replicationCount) explicitUnshiftedFunction ≤ 5 := by
  classical
  have hex : ∃ k, computableWithSharedHeadsN (14 * replicationCount) k
      explicitUnshiftedFunction := ⟨5, explicit_shared_vanilla_five⟩
  unfold SharedHStar
  rw [dif_pos hex]
  exact Nat.find_min' hex explicit_shared_vanilla_five

theorem explicit_vanillaHStar_le_five :
    HStar (14 * replicationCount) explicitUnshiftedFunction ≤ 5 := by
  simpa only [SharedHStar_eq_HStar] using explicit_sharedHStar_le_five

end
end HeadComplexity.PureRoPEReplicationFive
