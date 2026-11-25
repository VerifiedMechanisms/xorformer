import HeadComplexity.Polynomial.RoPEGroupSymmetrization
import HeadComplexity.Polynomial.RoPEMixedTensor
import HeadComplexity.Atoms.RoPETensorFactors

set_option linter.style.header false

/-!
# The cubic tensor retained by group averaging

The mixed tensor is exactly unchanged by averaging and replica collapse.
Strict global orientation of a nonconstant denominator gives a nonnegative,
nonzero row in the first block after replica aggregation.
-/

namespace HeadComplexity.RoPEAveragedTensor

open scoped BigOperators
open MvPolynomial RoPEMixedTensor RoPEThreeTensor RoPEGroupSymmetrization

theorem mixedTensor_averagedGroupPolynomial {m : ℕ} (hm : 0 < m)
    (P : MvPolynomial (Fin 18 × Fin m) ℝ) (hP : P.totalDegree ≤ 3) :
    mixedTensor (averagedGroupPolynomial P) = mixedTensor (rename Prod.fst P) := by
  funext i j k
  apply averagedGroupPolynomial_coeff_top_squarefree hm P (mixedExponent i j k)
    (mixedExponent_squarefree i j k)
  have he := mixedExponent_degree i j k
  change (mixedExponent i j k).sum (fun _ a ↦ a) = 3 at he
  simpa only [he] using hP

noncomputable def aggregateRows {m : ℕ}
    (A : Fin 3 → Fin 18 × Fin m → ℝ) (b : Fin 3) : Matrix (Fin 3) (Fin 6) ℝ :=
  fun h j ↦ ∑ r, A h (blockIndex b j, r)

def GloballyOriented {σ : Type*} (D : σ → ℝ) : Prop :=
  (∀ p, 0 < D p) ∨ (∀ p, D p < 0) ∨ (∀ p, D p = 0)

/-- The strict global sign supplied by the literal vanilla normal form
survives aggregation in every block, including the first one. -/
theorem aggregateRows_positive {m : ℕ} (hm : 0 < m)
    (D : Fin 3 → Fin 18 × Fin m → ℝ) (h : Fin 3)
    (hD : ∀ p, 0 < D h p) (b : Fin 3) (j : Fin 6) :
    0 < aggregateRows D b h j := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact Finset.sum_pos (fun r _ ↦ hD _) Finset.univ_nonempty

theorem aggregateRows_negative {m : ℕ} (hm : 0 < m)
    (D : Fin 3 → Fin 18 × Fin m → ℝ) (h : Fin 3)
    (hD : ∀ p, D h p < 0) (b : Fin 3) (j : Fin 6) :
    aggregateRows D b h j < 0 := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact Finset.sum_neg (fun r _ ↦ hD _) Finset.univ_nonempty

/-- A nonzero tangent tensor must retain at least one nonconstant denominator;
global orientation then supplies the simplex normal used in the limit proof.
No full-rank assumption is imposed on the three denominator rows. -/
theorem exists_oriented_aggregate_row {m : ℕ} (hm : 0 < m)
    (D N : Fin 3 → Fin 18 × Fin m → ℝ)
    (hD : ∀ h, GloballyOriented (D h))
    (hT : factorTensor (aggregateRows D 0) (aggregateRows N 0)
      (aggregateRows D 1) (aggregateRows N 1)
      (aggregateRows D 2) (aggregateRows N 2) ≠ 0) :
    ∃ h σ, (∀ j, 0 ≤ σ * aggregateRows D 0 h j) ∧
      0 < ∑ j, σ * aggregateRows D 0 h j := by
  classical
  by_contra hn
  have hz (h : Fin 3) (p : Fin 18 × Fin m) : D h p = 0 := by
    rcases hD h with hp | hm' | hz
    · exfalso
      apply hn
      refine ⟨h, 1, fun j ↦ ?_, ?_⟩
      · simpa only [one_mul] using (aggregateRows_positive hm D h hp 0 j).le
      · simp only [one_mul]
        exact Finset.sum_pos (fun j _ ↦ aggregateRows_positive hm D h hp 0 j)
          Finset.univ_nonempty
    · exfalso
      apply hn
      refine ⟨h, -1, fun j ↦ ?_, ?_⟩
      · simpa only [neg_one_mul] using (neg_pos.mpr (aggregateRows_negative hm D h hm' 0 j)).le
      · simp only [neg_one_mul]
        exact Finset.sum_pos
          (fun j _ ↦ neg_pos.mpr (aggregateRows_negative hm D h hm' 0 j))
          Finset.univ_nonempty
    · exact hz p
  have hzero (b : Fin 3) : aggregateRows D b = 0 := by
    ext h j
    simp only [aggregateRows, hz, Finset.sum_const_zero, Matrix.zero_apply]
  apply hT
  rw [hzero, hzero, hzero]
  funext i
  simp [factorTensor, crossContraction]

end HeadComplexity.RoPEAveragedTensor
