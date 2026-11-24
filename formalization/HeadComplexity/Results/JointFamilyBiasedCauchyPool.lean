import HeadComplexity.Results.JointFamilyHaarSplit

set_option linter.style.header false

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

noncomputable def jointFamilyPoolKernel (i j : Fin 5) : ℝ :=
  (1 - ((i.val : ℝ) + j.val) / 20) ^ (-2 : ℤ)

def jointFamilyPoolSigma : Fin 5 → ℝ := ![1, -1, -1, 1, -1]
def jointFamilyPoolTau : Fin 5 → ℝ := ![1, -1, 1, -1, 1]

noncomputable def jointFamilyPoolScore (σ v : Fin 5 → ℝ) (i : Fin 5) : ℝ :=
  ∑ j : Fin 5, jointFamilyPoolKernel i j * σ j * v j

noncomputable def jointFamilyPoolRows (v : Fin 5 → ℝ) : Fin 6 → ℝ :=
  ![jointFamilyPoolScore jointFamilyPoolSigma v 0 - jointFamilyPoolScore jointFamilyPoolSigma v 2,
    jointFamilyPoolScore jointFamilyPoolSigma v 3 - jointFamilyPoolScore jointFamilyPoolSigma v 1,
    jointFamilyPoolScore jointFamilyPoolSigma v 3 - jointFamilyPoolScore jointFamilyPoolSigma v 4,
    jointFamilyPoolScore jointFamilyPoolTau v 0 - jointFamilyPoolScore jointFamilyPoolTau v 3,
    jointFamilyPoolScore jointFamilyPoolTau v 2 - jointFamilyPoolScore jointFamilyPoolTau v 1,
    jointFamilyPoolScore jointFamilyPoolTau v 4 - jointFamilyPoolScore jointFamilyPoolTau v 1]

def jointFamilyPoolWeights : Fin 6 → ℝ :=
  ![35440369309187123991238756359,
    48100423689034343765990264800,
    27825587852781609089724953159,
    155051395568004155558762660391,
    414026926739031151586594347641,
    15762369118876666914542659559]

theorem jointFamily_biased_pool_identity (v : Fin 5 → ℝ) :
    (∑ i : Fin 6, jointFamilyPoolWeights i * jointFamilyPoolRows v i) = 0 := by
  norm_num [jointFamilyPoolWeights, jointFamilyPoolRows, jointFamilyPoolScore,
    jointFamilyPoolKernel, jointFamilyPoolSigma, jointFamilyPoolTau, Fin.sum_univ_succ]
  ring

/-- Even with a separate unrestricted bias for each word, the same residue
difference cannot solve these two conjugated square-Cauchy systems. This
does not exclude independent higher-order residue perturbations. -/
theorem jointFamily_no_biased_cauchy_pool :
    ¬ ∃ (v : Fin 5 → ℝ) (b c : ℝ),
      (∀ i, 0 < jointFamilyPoolSigma i * (jointFamilyPoolScore jointFamilyPoolSigma v i + b)) ∧
      (∀ i, 0 < jointFamilyPoolTau i * (jointFamilyPoolScore jointFamilyPoolTau v i + c)) := by
  rintro ⟨v, b, c, hs, ht⟩
  have hs₀ := hs 0
  have hs₁ := hs 1
  have hs₂ := hs 2
  have hs₃ := hs 3
  have hs₄ := hs 4
  have ht₀ := ht 0
  have ht₁ := ht 1
  have ht₂ := ht 2
  have ht₃ := ht 3
  have ht₄ := ht 4
  norm_num [jointFamilyPoolSigma, jointFamilyPoolTau] at hs₀ hs₁ hs₂ hs₃ hs₄ ht₀ ht₁ ht₂ ht₃ ht₄
  have hr : ∀ i, 0 < jointFamilyPoolRows v i := by
    intro i
    fin_cases i <;> norm_num [jointFamilyPoolRows, jointFamilyPoolSigma,
      jointFamilyPoolTau] <;> linarith
  have hw : ∀ i, 0 < jointFamilyPoolWeights i := by
    intro i
    fin_cases i <;> norm_num [jointFamilyPoolWeights]
  have hp : 0 < ∑ i : Fin 6, jointFamilyPoolWeights i * jointFamilyPoolRows v i :=
    Finset.sum_pos (fun i _ ↦ mul_pos (hw i) (hr i)) Finset.univ_nonempty
  rw [jointFamily_biased_pool_identity] at hp
  exact (lt_irrefl _ hp)

end HeadComplexity.AxisZeroGluing
