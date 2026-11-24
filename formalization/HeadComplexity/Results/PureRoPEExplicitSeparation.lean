import HeadComplexity.Polynomial.PureCubicFiniteRigidity
import HeadComplexity.Polynomial.ThreeHeadMeanSign
import HeadComplexity.Polynomial.ReplicatedMeanGrid
import HeadComplexity.Results.PureRoPEReplicationBounds
import HeadComplexity.Results.PureRoPEReplicationFive
import HeadComplexity.Results.FourHeadLocalPattern

set_option linter.style.header false

/-!
# An explicit finite Boolean separation between pure rotary and vanilla heads

The function uses fourteen groups of 2^400000 bits. Its exact rational pure
atoms, strict full-cube margin, and finite-grid classifier are defined in the
replication modules. The lower bound quantifies over every vanilla-admissible
representation, including arbitrary real parameters, untied replicas, constant
heads, and zero scores on false inputs.
-/

namespace HeadComplexity.PureRoPEExplicitSeparation
noncomputable section
open scoped BigOperators
open MvPolynomial PureRoPEReplication PureRoPEReplicationStrict
open ThreeHeadMeanGap ThreeHeadMeanSign PureCubicFiniteRigidity
open PureRoPEReplicationBounds

theorem replicationCount_gt_two : 2 < replicationCount := by
  unfold replicationCount
  have bound (k : ℕ) (hk : 2 < k) : 2 < 2 ^ k :=
    lt_trans hk Nat.lt_two_pow_self
  exact bound 400000 (by decide)

/-- The lower bound applies to the literal original vanilla architecture. -/
theorem not_vanilla_three :
    ¬ computableWithHeadsN (14 * replicationCount) 3 explicitUnshiftedFunction := by
  intro hc
  obtain ⟨r, c, hr, hclass⟩ :=
    (computableWithHeadsN_iff_affineFractionComputable 3 explicitUnshiftedFunction).mp hc
  have hsign := meanCleared_sign replicationCount_gt_two r c hr hclass
  have hn : meanCleared r c ≠ 0 := by
    intro hz
    have hp := (hsign (fun _ ↦ true)).mpr (unshifted_all_true replicationCount_positive)
    simp only [hz, map_zero, lt_self_iff_false] at hp
  obtain ⟨a, ha, hclose⟩ := finite_sign_rigidity (meanCleared r c)
    (meanCleared_degree r c) hn
    (ReplicatedMeanGrid.rawTarget_classifier_grid replicationCount_positive _ hsign)
  exact not_meanCleared_close replicationCount_gt_two r c hr a ha (fun d ↦ (hclose d).le)

theorem vanillaHStar_ge_four :
    4 ≤ HStar (14 * replicationCount) explicitUnshiftedFunction := by
  by_contra h
  have hle : HStar (14 * replicationCount) explicitUnshiftedFunction ≤ 3 := by omega
  apply not_vanilla_three
  apply (computableWithHeadsN_iff_affineFractionComputable 3 explicitUnshiftedFunction).mpr
  exact FourHeadLocalPattern.affineComputable_mono hle
    ((computableWithHeadsN_iff_affineFractionComputable _ explicitUnshiftedFunction).mp
      (HStar_computable explicitUnshiftedFunction))

theorem pureHStar_eq_three :
    PureRoPEHStar (14 * replicationCount) explicitUnshiftedFunction = 3 :=
  ThreeHeadReplication.exact_three_of_upper_and_vanilla_lower explicitUnshiftedFunction
    explicitUnshiftedFunction_pure_three vanillaHStar_ge_four

theorem strict_separation :
    PureRoPEHStar (14 * replicationCount) explicitUnshiftedFunction <
      HStar (14 * replicationCount) explicitUnshiftedFunction := by
  rw [pureHStar_eq_three]
  exact lt_of_lt_of_le (by norm_num) vanillaHStar_ge_four

theorem vanillaHStar_bounds :
    4 ≤ HStar (14 * replicationCount) explicitUnshiftedFunction ∧
      HStar (14 * replicationCount) explicitUnshiftedFunction ≤ 5 :=
  ⟨vanillaHStar_ge_four, PureRoPEReplicationFive.explicit_vanillaHStar_le_five⟩

theorem shared_strict_separation :
    PureRoPEHStar (14 * replicationCount) explicitUnshiftedFunction <
      SharedHStar (14 * replicationCount) explicitUnshiftedFunction := by
  simpa only [SharedHStar_eq_HStar] using strict_separation

/-- A concrete witness disproves universal equality of the two minima. -/
theorem not_universal_equality :
    ¬ ∀ (n : ℕ) (f : (Fin n → Bool) → Bool), PureRoPEHStar n f = HStar n f := by
  intro h
  exact (ne_of_lt strict_separation) (h _ _)

end
end HeadComplexity.PureRoPEExplicitSeparation
