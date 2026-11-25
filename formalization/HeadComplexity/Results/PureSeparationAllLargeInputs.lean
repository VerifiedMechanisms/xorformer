import HeadComplexity.Results.PureThreeSeparation
import HeadComplexity.Results.VanillaInputRestriction

set_option linter.style.header false

/-!
# Pure rotary separation at every sufficiently large input length

Adding unused bits preserves the pure head budget by a strict finite margin.
Any vanilla representation of the padded classifier would restrict to one of
the original classifier, so its lower bound persists.
-/

namespace HeadComplexity

theorem complexity_bounds_of_pure_three_not_vanilla_three {n : ℕ}
    (f : (Fin n → Bool) → Bool) (hp : pureRoPEComputable n 3 f)
    (hv : ¬ computableWithSharedHeadsN n 3 f) :
    PureRoPEHStar n f = 3 ∧ 4 ≤ SharedHStar n f ∧ SharedHStar n f ≤ 6 ∧
      StandardPureRoPEHStar n f = 3 ∧ FreePureRoPEHStar n f = 3 := by
  classical
  have hple : PureRoPEHStar n f ≤ 3 := Nat.find_min' (exists_pureRoPEComputable f) hp
  have hvle : ¬ HStar n f ≤ 3 := by
    intro hle
    exact hv (computableWithSharedHeadsN_mono hle
      (computableWithSharedHeadsN_of_computableWithHeadsN (HStar_computable f)))
  have hpgt : ¬ PureRoPEHStar n f ≤ 2 := by
    intro hle
    have he := pureRoPEHStar_eq_vanilla_of_le_two f hle
    omega
  have he : PureRoPEHStar n f = 3 := by omega
  have hu := HStar_le_improved_exponential_pureRoPEHStar f
    (by omega : 2 ≤ PureRoPEHStar n f)
  rw [he] at hu
  norm_num at hu
  rw [SharedHStar_eq_HStar, standardPureRoPEHStar_eq_scalar, freePureRoPEHStar_eq_scalar]
  exact ⟨he, by omega, hu, he, he⟩

/-- A three-head pure versus four-or-more-head vanilla Boolean separation
exists at every sufficiently large finite input length. -/
theorem pureRoPE_separation_every_large_input_length :
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ f : (Fin n → Bool) → Bool,
      PureRoPEHStar n f = 3 ∧ 4 ≤ SharedHStar n f ∧ SharedHStar n f ≤ 6 ∧
      StandardPureRoPEHStar n f = 3 ∧ FreePureRoPEHStar n f = 3 := by
  obtain ⟨N, f, hs, _, hv⟩ := PureThreeReplicatedGrid.exists_rotary_three_not_vanilla_three
  have hp : pureRoPEComputable N 3 f :=
    (rectangularStandardPureRotaryComputable_iff_scalar N 3 f).mp hs
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨InputPadding.classifier k f, ?_⟩
  exact complexity_bounds_of_pure_three_not_vanilla_three _
    (InputPadding.pure_computable k f hp) (InputPadding.not_vanilla_classifier hv)

end HeadComplexity
