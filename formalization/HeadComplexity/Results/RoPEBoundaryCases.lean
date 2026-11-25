import HeadComplexity.Results.RoPEArchitecturalComparison

set_option linter.style.header false

/-!
# Empty inputs and zero-head boundaries

These statements make the boundary cases explicit without changing either
architecture or its strict positive-score threshold convention.
-/

namespace HeadComplexity

/-- With no attention heads, the free threshold represents precisely constants. -/
theorem pureRoPEComputable_zero_iff_constant {n : ℕ}
    (f : (Fin n → Bool) → Bool) :
    pureRoPEComputable n 0 f ↔ ∃ b : Bool, ∀ x, f x = b := by
  constructor
  · rintro ⟨p, c, hc⟩
    simp only [Fin.sum_univ_zero, add_zero] at hc
    refine ⟨f (fun _ ↦ false), fun x ↦ ?_⟩
    apply Bool.eq_iff_iff.mpr
    exact (hc x).symm.trans (hc (fun _ ↦ false))
  · rintro ⟨b, hb⟩
    refine ⟨Fin.elim0, if b then 1 else -1, fun x ↦ ?_⟩
    rw [hb x]
    cases b <;> norm_num

theorem vanilla_zero_iff_constant {n : ℕ} (f : (Fin n → Bool) → Bool) :
    computableWithSharedHeadsN n 0 f ↔ ∃ b : Bool, ∀ x, f x = b :=
  (pureRoPEComputable_iff_vanilla_of_le_two f (by norm_num)).symm.trans
    (pureRoPEComputable_zero_iff_constant f)

theorem standardPureRotaryComputable_zero_iff_constant {n : ℕ}
    (f : (Fin n → Bool) → Bool) :
    rectangularStandardPureRotaryComputable n 0 f ↔ ∃ b : Bool, ∀ x, f x = b :=
  (rectangularStandardPureRotaryComputable_iff_scalar n 0 f).trans
    (pureRoPEComputable_zero_iff_constant f)

theorem freePureRotaryComputable_zero_iff_constant {n : ℕ}
    (f : (Fin n → Bool) → Bool) :
    rectangularFreePureRotaryComputable n 0 f ↔ ∃ b : Bool, ∀ x, f x = b :=
  (rectangularFreePureRotaryComputable_iff_scalar n 0 f).trans
    (pureRoPEComputable_zero_iff_constant f)

theorem pureRoPEComputable_empty_zero (f : (Fin 0 → Bool) → Bool) :
    pureRoPEComputable 0 0 f := by
  apply (pureRoPEComputable_zero_iff_constant f).mpr
  exact ⟨f Fin.elim0, fun x ↦ congrArg f (Subsingleton.elim x Fin.elim0)⟩

/-- Every classifier on an empty input is constant, so all four minima vanish. -/
theorem empty_input_head_minima (f : (Fin 0 → Bool) → Bool) :
    PureRoPEHStar 0 f = 0 ∧ SharedHStar 0 f = 0 ∧
      StandardPureRoPEHStar 0 f = 0 ∧ FreePureRoPEHStar 0 f = 0 := by
  have hp : PureRoPEHStar 0 f = 0 := by
    classical
    apply Nat.eq_zero_of_le_zero
    exact Nat.find_min' (exists_pureRoPEComputable f) (pureRoPEComputable_empty_zero f)
  have hv := pureRoPEHStar_eq_vanilla_of_le_two f (by omega : PureRoPEHStar 0 f ≤ 2)
  rw [standardPureRoPEHStar_eq_scalar, freePureRoPEHStar_eq_scalar, SharedHStar_eq_HStar]
  exact ⟨hp, hv.symm.trans hp, hp, hp⟩

end HeadComplexity
