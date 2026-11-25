import HeadComplexity.Results.PureThreeReplicatedGrid
import HeadComplexity.Results.RoPEArchitecturalComparison
import HeadComplexity.Results.RoPESmallInputs

set_option linter.style.header false

/-!
# Conditional complexity consequences for the replicated-grid family

The upper representation is unconditional. The premise excluding three
vanilla heads is explicit here. The continuous compactness argument proves
that premise for sufficiently large replication counts in the separate
`Results/PureThreeSeparation` module.
-/

namespace HeadComplexity.PureThreeReplicatedGrid

/-- Given exclusion of three vanilla heads, the explicit pure family has
minimum exactly three under both literal rotary-frequency conventions. -/
theorem complexities_of_not_vanilla_three (m : ℕ) (hm : 0 < m)
    (hnot : ¬ computableWithSharedHeadsN (18 * m) 3 (classifier m)) :
    PureRoPEHStar (18 * m) (classifier m) = 3 ∧
      4 ≤ HStar (18 * m) (classifier m) ∧
      StandardPureRoPEHStar (18 * m) (classifier m) = 3 ∧
      FreePureRoPEHStar (18 * m) (classifier m) = 3 := by
  classical
  have hp : PureRoPEHStar (18 * m) (classifier m) ≤ 3 :=
    Nat.find_min' (exists_pureRoPEComputable (classifier m)) (pure_computable m hm)
  have hv : ¬ HStar (18 * m) (classifier m) ≤ 3 := by
    intro hle
    apply hnot
    apply computableWithSharedHeadsN_mono hle
    exact computableWithSharedHeadsN_of_computableWithHeadsN (HStar_computable (classifier m))
  have hp' : ¬ PureRoPEHStar (18 * m) (classifier m) ≤ 2 := by
    intro hle
    have he := pureRoPEHStar_eq_vanilla_of_le_two (classifier m) hle
    omega
  have he : PureRoPEHStar (18 * m) (classifier m) = 3 := by omega
  refine ⟨he, by omega, ?_, ?_⟩
  · rw [standardPureRoPEHStar_eq_scalar, he]
  · rw [freePureRoPEHStar_eq_scalar, he]

/-- A reusable wrapper retaining the lower-bound premise explicitly. -/
theorem eventual_complexities_of_eventual_not_vanilla_three
    (hnot : ∃ M : ℕ, ∀ m, M ≤ m →
      ¬ computableWithSharedHeadsN (18 * m) 3 (classifier m)) :
    ∃ M : ℕ, ∀ m, M ≤ m →
      PureRoPEHStar (18 * m) (classifier m) = 3 ∧
        4 ≤ HStar (18 * m) (classifier m) ∧
        StandardPureRoPEHStar (18 * m) (classifier m) = 3 ∧
        FreePureRoPEHStar (18 * m) (classifier m) = 3 := by
  obtain ⟨M, hM⟩ := hnot
  refine ⟨max 1 M, fun m hm ↦ ?_⟩
  apply complexities_of_not_vanilla_three m (by omega)
  exact hM m (by omega)

end HeadComplexity.PureThreeReplicatedGrid
