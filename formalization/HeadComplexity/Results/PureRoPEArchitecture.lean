import HeadComplexity.Model.PureRoPERealization
import HeadComplexity.Results.PureRoPEExplicitSeparation

set_option linter.style.header false

/-! # Literal rotary architecture and its exact head complexity

The standard-frequency, fixed-query, token-only-value architecture has exactly
the pure scalar normal form at every head count. Including the residual stream
does not change its classifiers or its minimum number of heads.
-/

namespace HeadComplexity
noncomputable section

variable {n H : ℕ}

theorem computableWithPureRoPEHeadsN_iff_pureRoPEComputable
    (f : (Fin n → Bool) → Bool) :
    computableWithPureRoPEHeadsN n H f ↔ pureRoPEComputable n H f :=
  ⟨pureRoPEComputable_of_architecture, architecture_of_pureRoPEComputable⟩

/-- Literal standard rotary attention, including the fixed query residual. -/
def computableWithPureRoPEResidualHeadsN (n H : ℕ)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (d m : ℕ), 0 < d ∧ 0 < m ∧
    ∃ M : PureRoPEFamily n d m H, computesPred f M.residual

theorem computableWithPureRoPEResidualHeadsN_iff
    (f : (Fin n → Bool) → Bool) :
    computableWithPureRoPEResidualHeadsN n H f ↔ computableWithPureRoPEHeadsN n H f := by
  constructor
  · rintro ⟨d,m,hd,hm,M,hM⟩
    exact ⟨d,m,hd,hm,M,(M.computesPred_residual_iff_attnUpdate f).mp hM⟩
  · rintro ⟨d,m,hd,hm,M,hM⟩
    exact ⟨d,m,hd,hm,M,(M.computesPred_residual_iff_attnUpdate f).mpr hM⟩

theorem computableWithPureRoPEResidualHeadsN_iff_pureRoPEComputable
    (f : (Fin n → Bool) → Bool) :
    computableWithPureRoPEResidualHeadsN n H f ↔ pureRoPEComputable n H f :=
  (computableWithPureRoPEResidualHeadsN_iff f).trans
    (computableWithPureRoPEHeadsN_iff_pureRoPEComputable f)

/-- Every scalar classifier has a shared-embedding realization with model
width three and exactly `n + 2` rotary pairs, including the full residual. -/
theorem pureRoPEComputable_residual_fixed_width
    {f : (Fin n → Bool) → Bool} (hf : pureRoPEComputable n H f) :
    ∃ M : PureRoPEFamily n 3 (n + 2) H, computesPred f M.residual := by
  obtain ⟨p,c,hp⟩ := hf
  obtain ⟨M,_,_,_,_,hM⟩ := PureRoPERealization.exists_family p
  refine ⟨M,RoPETokenMaps.embedding 0,-c,fun x ↦ ?_⟩
  rw [hM]
  exact (show -c < ∑ h, (p h).eval x ↔ 0 < c + ∑ h, (p h).eval x by
    constructor <;> intro h <;> linarith).trans (hp x)

theorem exists_literalPureRoPEComputable (f : (Fin n → Bool) → Bool) :
    ∃ H, computableWithPureRoPEHeadsN n H f := by
  obtain ⟨H,hH⟩ := exists_pureRoPEComputable f
  exact ⟨H,architecture_of_pureRoPEComputable hH⟩

/-- The exact minimum in the literal standard-frequency rotary architecture. -/
def LiteralPureRoPEHStar (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (exists_literalPureRoPEComputable f)

theorem literalPureRoPEHStar_computable (f : (Fin n → Bool) → Bool) :
    computableWithPureRoPEHeadsN n (LiteralPureRoPEHStar n f) f := by
  classical
  exact Nat.find_spec (exists_literalPureRoPEComputable f)

theorem literalPureRoPEHStar_eq_pureRoPEHStar (f : (Fin n → Bool) → Bool) :
    LiteralPureRoPEHStar n f = PureRoPEHStar n f := by
  classical
  apply Nat.le_antisymm
  · exact Nat.find_min' _
      (architecture_of_pureRoPEComputable (pureRoPEHStar_computable f))
  · exact Nat.find_min' _
      (pureRoPEComputable_of_architecture (literalPureRoPEHStar_computable f))

theorem exists_literalPureRoPEResidualComputable (f : (Fin n → Bool) → Bool) :
    ∃ H, computableWithPureRoPEResidualHeadsN n H f := by
  obtain ⟨H,hH⟩ := exists_literalPureRoPEComputable f
  exact ⟨H,(computableWithPureRoPEResidualHeadsN_iff f).mpr hH⟩

/-- The same minimum when the output is read from the full residual stream. -/
def LiteralPureRoPEResidualHStar (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (exists_literalPureRoPEResidualComputable f)

theorem literalPureRoPEResidualHStar_eq (f : (Fin n → Bool) → Bool) :
    LiteralPureRoPEResidualHStar n f = LiteralPureRoPEHStar n f := by
  classical
  unfold LiteralPureRoPEResidualHStar LiteralPureRoPEHStar
  apply Nat.find_congr'
  exact computableWithPureRoPEResidualHeadsN_iff f

theorem literalPureRoPEResidualHStar_eq_pureRoPEHStar (f : (Fin n → Bool) → Bool) :
    LiteralPureRoPEResidualHStar n f = PureRoPEHStar n f := by
  rw [literalPureRoPEResidualHStar_eq, literalPureRoPEHStar_eq_pureRoPEHStar]

namespace PureRoPEArchitecture
open PureRoPEReplication PureRoPEReplicationStrict

theorem explicit_literal_residual_model_three :
    ∃ M : PureRoPEFamily (14 * replicationCount) 3 (14 * replicationCount + 2) 3,
      computesPred explicitUnshiftedFunction M.residual :=
  pureRoPEComputable_residual_fixed_width explicitUnshiftedFunction_pure_three

theorem explicit_literal_pureHStar_eq_three :
    LiteralPureRoPEHStar (14 * replicationCount) explicitUnshiftedFunction = 3 := by
  rw [literalPureRoPEHStar_eq_pureRoPEHStar]
  exact PureRoPEExplicitSeparation.pureHStar_eq_three

theorem explicit_literal_residualHStar_eq_three :
    LiteralPureRoPEResidualHStar (14 * replicationCount) explicitUnshiftedFunction = 3 := by
  rw [literalPureRoPEResidualHStar_eq]
  exact explicit_literal_pureHStar_eq_three

/-- The separation now quantifies over literal rotary matrices and literal
original vanilla architectures, at unrestricted positive finite widths. -/
theorem explicit_literal_strict_separation :
    LiteralPureRoPEHStar (14 * replicationCount) explicitUnshiftedFunction <
      HStar (14 * replicationCount) explicitUnshiftedFunction := by
  rw [literalPureRoPEHStar_eq_pureRoPEHStar]
  exact PureRoPEExplicitSeparation.strict_separation

theorem explicit_literal_complexities :
    LiteralPureRoPEHStar (14 * replicationCount) explicitUnshiftedFunction = 3 ∧
      4 ≤ HStar (14 * replicationCount) explicitUnshiftedFunction ∧
      HStar (14 * replicationCount) explicitUnshiftedFunction ≤ 5 :=
  ⟨explicit_literal_pureHStar_eq_three, PureRoPEExplicitSeparation.vanillaHStar_bounds⟩

theorem explicit_literal_shared_strict_separation :
    LiteralPureRoPEHStar (14 * replicationCount) explicitUnshiftedFunction <
      SharedHStar (14 * replicationCount) explicitUnshiftedFunction := by
  simpa only [SharedHStar_eq_HStar] using explicit_literal_strict_separation

theorem explicit_literal_residual_strict_separation :
    LiteralPureRoPEResidualHStar (14 * replicationCount) explicitUnshiftedFunction <
      HStar (14 * replicationCount) explicitUnshiftedFunction := by
  rw [literalPureRoPEResidualHStar_eq]
  exact explicit_literal_strict_separation

theorem not_universal_literal_equality :
    ¬ ∀ (n : ℕ) (f : (Fin n → Bool) → Bool), LiteralPureRoPEHStar n f = HStar n f := by
  intro h
  exact (ne_of_lt explicit_literal_strict_separation) (h _ _)

theorem not_universal_literal_residual_equality :
    ¬ ∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
      LiteralPureRoPEResidualHStar n f = HStar n f := by
  intro h
  exact (ne_of_lt explicit_literal_residual_strict_separation) (h _ _)

end PureRoPEArchitecture
end
end HeadComplexity
