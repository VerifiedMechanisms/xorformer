import HeadComplexity.Polynomial.MeanGridSignProbe
import HeadComplexity.Polynomial.PureCubicRawKernel
import Mathlib.Data.Fintype.Fin

set_option linter.style.header false

/-! # Every finite mean-grid point is an actual replicated Boolean input -/

namespace HeadComplexity.ReplicatedMeanGrid

noncomputable section

open MvPolynomial PureRoPECenteredConstruction PureRoPEReplication MeanGridSignProbe
open PureCubicRawKernel PureRoPEReplicationStrict
open scoped BigOperators

def gridInput {n m : ℕ} (k : Fin n → Fin (m + 1)) (p : Fin (n * m)) : Bool :=
  decide (((finProdFinEquiv (m := n) (n := m)).symm p).2.val <
    (k ((finProdFinEquiv (m := n) (n := m)).symm p).1).val)

theorem spin_decide (p : Prop) [Decidable p] :
    spin (decide p) = 2 * (if p then (1 : ℝ) else 0) - 1 := by
  by_cases hp : p <;> norm_num [spin, hp]

theorem initial_spin_sum (m : ℕ) (k : Fin (m + 1)) :
    (∑ r : Fin m, spin (decide (r.val < k.val))) = 2 * (k.val : ℝ) - m := by
  simp_rw [spin_decide]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_boole, Fin.card_filter_val_lt, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [min_eq_right (show k.val ≤ m by omega)]

theorem means_gridInput {n m : ℕ} (hm : 0 < m) (k : Fin n → Fin (m + 1)) :
    means (gridInput k) = fun i ↦ gridValue m (k i) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  funext i
  simp only [means, gridInput, Equiv.symm_apply_apply, initial_spin_sum, gridValue]
  field_simp
  ring

/-- Surjectivity holds even at the endpoints and at target ties. -/
theorem means_surjective_grid {n m : ℕ} (hm : 0 < m) (k : Fin n → Fin (m + 1)) :
    ∃ x : Fin (n * m) → Bool, means x = fun i ↦ gridValue m (k i) :=
  ⟨gridInput k, means_gridInput hm k⟩

theorem same_classifier_on_grid {m : ℕ} (hm : 0 < m)
    (P Q : MvPolynomial (Fin 14) ℝ)
    (h : ∀ x : Fin (14 * m) → Bool,
      (0 < eval (means x) P ↔ 0 < eval (means x) Q)) :
    ∀ k : Fin 14 → Fin (m + 1),
      (0 < eval (fun i ↦ gridValue m (k i)) P ↔
        0 < eval (fun i ↦ gridValue m (k i)) Q) := by
  intro k
  simpa only [means_gridInput hm k] using h (gridInput k)

theorem rawTarget_classifier_grid {m : ℕ} (hm : 0 < m)
    (Q : MvPolynomial (Fin 14) ℝ)
    (h : ∀ x : Fin (14 * m) → Bool,
      (0 < eval (means x) Q ↔ unshiftedFunction x = true)) :
    ∀ k : Fin 14 → Fin (m + 1),
      (0 < eval (fun i ↦ gridValue m (k i)) rawTarget ↔
        0 < eval (fun i ↦ gridValue m (k i)) Q) := by
  apply same_classifier_on_grid hm rawTarget Q
  intro x
  rw [h x, eval_rawTarget_means]
  simp [unshiftedFunction]

end
end HeadComplexity.ReplicatedMeanGrid
