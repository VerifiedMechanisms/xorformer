import HeadComplexity.Polynomial.ReplicatedInputCopy
import HeadComplexity.Results.RoPEDummyExtension

/-!
# Monotone group means and unused-input extensions

Boolean inputs carry the standard order false < true. Centered group means
preserve this coordinatewise order, including the empty-replica convention.
Adding ignored input variables also preserves monotonicity of classifiers.
-/

namespace HeadComplexity.ReplicatedInputCopy

open scoped BigOperators

theorem boolToReal_monotone : Monotone boolToReal := by
  intro a b hab
  cases a <;> cases b <;> simp_all [Bool.le_iff_imp, boolToReal]

theorem coordinate_monotone (G m : ℕ) : Monotone (coordinate G m) := by
  intro x y hxy g
  unfold coordinate
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
  apply Finset.sum_le_sum
  intro r _
  have h := boolToReal_monotone (hxy (finProdFinEquiv (g, r)))
  linarith

theorem coordinate_abs_le_one {G m : ℕ} (x : Fin (G * m) → Bool) (g : Fin G) :
    |coordinate G m x g| ≤ 1 := by
  by_cases hm : m = 0
  · subst m
    simp [coordinate]
  have hm' : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  rw [coordinate, abs_div, abs_of_pos hm', div_le_one hm']
  calc
    |∑ r : Fin m, (2 * boolToReal (x (finProdFinEquiv (g, r))) - 1)| ≤
        ∑ r : Fin m, |2 * boolToReal (x (finProdFinEquiv (g, r))) - 1| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = (m : ℝ) := by
      have hb (r : Fin m) : |2 * boolToReal (x (finProdFinEquiv (g, r))) - 1| = 1 := by
        cases x (finProdFinEquiv (g, r)) <;> norm_num [boolToReal]
      simp only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]

end HeadComplexity.ReplicatedInputCopy

namespace HeadComplexity.InputPadding

theorem project_monotone (n k : ℕ) : Monotone (project (n := n) (k := k)) :=
  fun _ _ h i ↦ h (i.castAdd k)

theorem classifier_monotone {n : ℕ} (k : ℕ) {f : (Fin n → Bool) → Bool}
    (hf : Monotone f) : Monotone (classifier k f) :=
  hf.comp (project_monotone n k)

end HeadComplexity.InputPadding
