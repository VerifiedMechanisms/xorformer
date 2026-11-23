import HeadComplexity.Atoms.FiniteRatioCalculus

set_option linter.style.header false

namespace HeadComplexity.FiniteRatioCalculus

open scoped BigOperators
open ContinuousLinearMap

variable {p m k : ℕ}

theorem rowForm_of_basis_values (L : (Fin p → ℝ) →L[ℝ] ℝ) :
    rowForm (fun i ↦ L (Pi.single i 1)) = L := by
  classical
  ext z
  have hz : z = ∑ i : Fin p, z i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [hz]
  rw [map_sum, rowForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

theorem matrixMap_of_basis_values (L : (Fin p → ℝ) →L[ℝ] (Fin m → ℝ)) :
    matrixMap (fun r c ↦ L (Pi.single c 1) r) = L := by
  ext z r
  have hh := congrArg (fun K : (Fin p → ℝ) →L[ℝ] ℝ ↦ K z)
    (rowForm_of_basis_values ((ContinuousLinearMap.proj r).comp L))
  simpa [matrixMap] using hh

theorem matrixMap_sub (A B : Fin m → Fin p → ℝ) :
    matrixMap (fun r c ↦ A r c - B r c) = matrixMap A - matrixMap B := by
  ext z r
  simp [matrixMap_apply, sub_mul, Finset.sum_sub_distrib]

theorem matrixMap_comp (A : Fin m → Fin p → ℝ) (B : Fin p → Fin k → ℝ) :
    (matrixMap A).comp (matrixMap B) = matrixMap (fun r c ↦ ∑ j, A r j * B j c) := by
  ext z r
  simp only [comp_apply, matrixMap_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem matrixMap_identity : matrixMap (fun r c : Fin p ↦ if r = c then (1 : ℝ) else 0) =
    ContinuousLinearMap.id ℝ (Fin p → ℝ) := by
  ext z r
  simp [matrixMap_apply]

theorem matrixMap_entry_bound (A : Fin m → Fin p → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hA : ∀ r c, |A r c| ≤ ε) : ‖matrixMap A‖ ≤ p * ε := by
  apply matrixMap_norm _ _ (mul_nonneg (Nat.cast_nonneg _) hε)
  intro r
  calc
    ∑ c, |A r c| ≤ ∑ _ : Fin p, ε := Finset.sum_le_sum fun c _ ↦ hA r c
    _ = p * ε := by simp

theorem piMap_norm_bound (L : Fin m → (Fin p → ℝ) →L[ℝ] ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hL : ∀ r, ‖L r‖ ≤ M) : ‖ContinuousLinearMap.pi L‖ ≤ M := by
  apply opNorm_le_bound _ hM
  intro z
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM (norm_nonneg _))).2
  intro r
  exact ((L r).le_opNorm z).trans (mul_le_mul_of_nonneg_right (hL r) (norm_nonneg _))

#print axioms matrixMap_of_basis_values
#print axioms matrixMap_comp

end HeadComplexity.FiniteRatioCalculus
