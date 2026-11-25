import HeadComplexity.Polynomial.ThresholdDegreePullback

/-! # Exact group means after duplicating every input coordinate -/

namespace HeadComplexity.ReplicatedInputCopy

open scoped BigOperators

/-- Each old replica receives k copies inside its original coordinate group. -/
def projection (G m k : ℕ) : Fin (G * (m * k)) → Fin (G * m) := fun p ↦
  finProdFinEquiv
    (((finProdFinEquiv (m := G) (n := m * k)).symm p).1,
      ((finProdFinEquiv (m := m) (n := k)).symm
        (((finProdFinEquiv (m := G) (n := m * k)).symm p).2)).1)

@[simp] theorem projection_pair (G m k : ℕ) (g : Fin G) (r : Fin m) (s : Fin k) :
    projection G m k (finProdFinEquiv (g, finProdFinEquiv (r, s))) =
      finProdFinEquiv (g, r) := by simp [projection]

noncomputable def coordinate (G m : ℕ) (x : Fin (G * m) → Bool) (g : Fin G) : ℝ :=
  (∑ r : Fin m, (2 * boolToReal (x (finProdFinEquiv (g, r))) - 1)) / m

theorem coordinate_copy {G m k : ℕ} (hk : 0 < k)
    (x : Fin (G * m) → Bool) :
    coordinate G (m * k) (x ∘ projection G m k) = coordinate G m x := by
  funext g
  unfold coordinate
  rw [← (finProdFinEquiv (m := m) (n := k)).sum_comp]
  simp only [Fintype.sum_prod_type, Function.comp_apply, projection_pair,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum, Nat.cast_mul]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  by_cases hm : m = 0
  · subst m; simp
  · have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    field_simp

end HeadComplexity.ReplicatedInputCopy
