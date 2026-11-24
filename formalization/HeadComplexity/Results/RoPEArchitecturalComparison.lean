import HeadComplexity.Model.RectangularPureRoPE
import HeadComplexity.Results.RoPETwoHeads

set_option linter.style.header false

/-!
# Architectural pure rotary comparisons

These statements compose the literal rectangular rotary bridge with the
unchanged vanilla architecture. Equality is established at head budgets zero,
one, and two. No arbitrary-head reverse implication is asserted.
-/

namespace HeadComplexity

theorem standardPureRotaryComputable_of_vanilla {n H : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : computableWithSharedHeadsN n H f) :
    rectangularStandardPureRotaryComputable n H f :=
  (rectangularStandardPureRotaryComputable_iff_scalar n H f).mpr
    (pureRoPEComputable_of_vanilla hf)

theorem freePureRotaryComputable_of_vanilla {n H : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : computableWithSharedHeadsN n H f) :
    rectangularFreePureRotaryComputable n H f :=
  (rectangularFreePureRotaryComputable_iff_scalar n H f).mpr
    (pureRoPEComputable_of_vanilla hf)

theorem standardPureRotaryComputable_iff_vanilla_of_le_two {n H : ℕ}
    (f : (Fin n → Bool) → Bool) (hH : H ≤ 2) :
    rectangularStandardPureRotaryComputable n H f ↔
      computableWithSharedHeadsN n H f :=
  (rectangularStandardPureRotaryComputable_iff_scalar n H f).trans
    (pureRoPEComputable_iff_vanilla_of_le_two f hH)

theorem freePureRotaryComputable_iff_vanilla_of_le_two {n H : ℕ}
    (f : (Fin n → Bool) → Bool) (hH : H ≤ 2) :
    rectangularFreePureRotaryComputable n H f ↔
      computableWithSharedHeadsN n H f :=
  (rectangularFreePureRotaryComputable_iff_scalar n H f).trans
    (pureRoPEComputable_iff_vanilla_of_le_two f hH)

theorem exists_standardPureRotaryComputable {n : ℕ}
    (f : (Fin n → Bool) → Bool) :
    ∃ H, rectangularStandardPureRotaryComputable n H f := by
  obtain ⟨H, hH⟩ := exists_pureRoPEComputable f
  exact ⟨H, (rectangularStandardPureRotaryComputable_iff_scalar n H f).mpr hH⟩

theorem exists_freePureRotaryComputable {n : ℕ}
    (f : (Fin n → Bool) → Bool) :
    ∃ H, rectangularFreePureRotaryComputable n H f := by
  obtain ⟨H, hH⟩ := exists_pureRoPEComputable f
  exact ⟨H, (rectangularFreePureRotaryComputable_iff_scalar n H f).mpr hH⟩

/-- Minimum head count in the literal fixed-standard rectangular architecture. -/
noncomputable def StandardPureRoPEHStar (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (exists_standardPureRotaryComputable f)

/-- Minimum head count in the literal free-frequency rectangular architecture. -/
noncomputable def FreePureRoPEHStar (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (exists_freePureRotaryComputable f)

theorem standardPureRoPEHStar_eq_scalar {n : ℕ} (f : (Fin n → Bool) → Bool) :
    StandardPureRoPEHStar n f = PureRoPEHStar n f := by
  classical
  apply le_antisymm
  · exact Nat.find_min' _
      ((rectangularStandardPureRotaryComputable_iff_scalar n _ f).mpr
        (pureRoPEHStar_computable f))
  · exact Nat.find_min' _
      ((rectangularStandardPureRotaryComputable_iff_scalar n _ f).mp
        (Nat.find_spec (exists_standardPureRotaryComputable f)))

theorem freePureRoPEHStar_eq_scalar {n : ℕ} (f : (Fin n → Bool) → Bool) :
    FreePureRoPEHStar n f = PureRoPEHStar n f := by
  classical
  apply le_antisymm
  · exact Nat.find_min' _
      ((rectangularFreePureRotaryComputable_iff_scalar n _ f).mpr
        (pureRoPEHStar_computable f))
  · exact Nat.find_min' _
      ((rectangularFreePureRotaryComputable_iff_scalar n _ f).mp
        (Nat.find_spec (exists_freePureRotaryComputable f)))

theorem architecturalPureRoPEHStar_le_vanilla {n : ℕ}
    (f : (Fin n → Bool) → Bool) :
    StandardPureRoPEHStar n f ≤ HStar n f ∧ FreePureRoPEHStar n f ≤ HStar n f := by
  rw [standardPureRoPEHStar_eq_scalar, freePureRoPEHStar_eq_scalar]
  exact ⟨pureRoPEHStar_le_vanilla f, pureRoPEHStar_le_vanilla f⟩

theorem architecturalPureRoPEHStar_eq_vanilla_of_le_two {n : ℕ}
    (f : (Fin n → Bool) → Bool) (hf : PureRoPEHStar n f ≤ 2) :
    StandardPureRoPEHStar n f = HStar n f ∧ FreePureRoPEHStar n f = HStar n f := by
  rw [standardPureRoPEHStar_eq_scalar, freePureRoPEHStar_eq_scalar]
  exact ⟨pureRoPEHStar_eq_vanilla_of_le_two f hf,
    pureRoPEHStar_eq_vanilla_of_le_two f hf⟩

end HeadComplexity
