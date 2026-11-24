import HeadComplexity.Polynomial.LowRankCrossRecovery

set_option linter.style.header false

/-!
# Squarefree entries determine a cubic tensor with rank-six Hessians

The tensor is the symmetric third derivative, so its slice at coordinate k is
exactly the Hessian at e_k. Distinct entries are the squarefree coefficients;
repeated entries are twice or six times the corresponding monomial coefficient.
-/

namespace HeadComplexity.SymmetricCubicRecovery
noncomputable section

variable {ι : Type*} [Fintype ι]

def slice (T : ι → ι → ι → ℝ) (k : ι) : Matrix ι ι ℝ := fun i j ↦ T i j k

def Symmetric (T : ι → ι → ι → ℝ) : Prop :=
  (∀ i j k, T i j k = T j i k) ∧ (∀ i j k, T i j k = T i k j)

/-- Six row and six column indices avoiding two coordinates, with all cross
entries squarefree and an invertible target cross block. -/
def CrossCondition (T : ι → ι → ι → ℝ) : Prop :=
  ∀ i k, i ≠ k → ∃ a b : Fin 6 → ι,
    (∀ p, a p ≠ i ∧ a p ≠ k ∧ b p ≠ i ∧ b p ≠ k) ∧
    (∀ p q, a p ≠ b q) ∧ ((slice T k).submatrix a b).det ≠ 0

/-- Exact uniqueness holds against every competitor whose coordinate Hessians
have rank at most six, including competitors using unrelated latent forms. -/
theorem eq_of_squarefree [Nontrivial ι] (T U : ι → ι → ι → ℝ)
    (hT : Symmetric T) (hU : Symmetric U)
    (hrT : ∀ k, (slice T k).rank ≤ 6) (hrU : ∀ k, (slice U k).rank ≤ 6)
    (hc : CrossCondition T)
    (hsq : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → T i j k = U i j k) : T = U := by
  have htwo (i k : ι) (hik : i ≠ k) : T i i k = U i i k := by
    obtain ⟨a, b, hav, hab, hdet⟩ := hc i k hik
    apply LowRankCrossRecovery.entry_eq_of_cross_data
      (slice T k) (slice U k) a b (hrT k) (hrU k) hdet i i
    · intro p q
      exact hsq _ _ _ (hab p q) (hav p).2.1 (hav q).2.2.2
    · intro p
      exact hsq _ _ _ (hav p).2.2.1.symm hik (hav p).2.2.2
    · intro q
      exact hsq _ _ _ (hav q).1 (hav q).2.1 hik
  have hthree (k : ι) : T k k k = U k k k := by
    obtain ⟨i, hik⟩ := exists_ne k
    obtain ⟨a, b, hav, hab, hdet⟩ := hc i k hik
    apply LowRankCrossRecovery.entry_eq_of_cross_data
      (slice T k) (slice U k) a b (hrT k) (hrU k) hdet k k
    · intro p q
      exact hsq _ _ _ (hab p q) (hav p).2.1 (hav q).2.2.2
    · intro p
      change T k (b p) k = U k (b p) k
      rw [hT.2, hU.2]
      exact htwo k (b p) (hav p).2.2.2.symm
    · intro q
      change T (a q) k k = U (a q) k k
      rw [hT.1, hU.1, hT.2, hU.2]
      exact htwo k (a q) (hav q).2.1.symm
  funext i j k
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      exact hthree i
    · exact htwo i k hik
  · by_cases hik : i = k
    · subst k
      rw [hT.2, hU.2]
      exact htwo i j hij
    · by_cases hjk : j = k
      · subst k
        rw [hT.1, hU.1, hT.2, hU.2]
        exact htwo j i (Ne.symm hij)
      · exact hsq i j k hij hik hjk

end
end HeadComplexity.SymmetricCubicRecovery
