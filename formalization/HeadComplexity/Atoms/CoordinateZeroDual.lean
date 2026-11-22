import HeadComplexity.Atoms.CoordinateZeroDualData

set_option linter.style.header false

/-! Exact nonzero norm-gradient dual coordinates at the Boolean regular zero.
The inverse-function and constrained-minimum consequences are written proofs. -/
namespace HeadComplexity.CoordinateZeroFiber

open scoped BigOperators

def normDual (r : Fin 96) : ℚ :=
  rowScale r * dualNumerator r / (3 * dualDenominator)

theorem rowScale_pos (r : Fin 96) : 0 < rowScale r := by
  have hp (h : Fin 3) : (0 : ℚ) < den h (indices r) := by
    exact_mod_cast sample_denominators_positive r h
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  unfold rowScale
  positivity

theorem normDual_ne_zero (r : Fin 96) : normDual r ≠ 0 := by
  have hn : (dualNumerator r : ℚ) ≠ 0 := by exact_mod_cast dualNumerator_ne_zero r
  have hd : (dualDenominator : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt dualDenominator_pos
  exact div_ne_zero (mul_ne_zero (ne_of_gt (rowScale_pos r)) hn)
    (mul_ne_zero (by norm_num) hd)

theorem normDual_equation (c : Fin 96) :
    (∑ r, jacobian r c * normDual r) = (normGradientNumerator c : ℚ) / 3 := by
  have hd : (dualDenominator : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt dualDenominator_pos
  have hm (r : Fin 96) : (clearedJacobian r c : ℚ) = rowScale r * jacobian r c := by
    have he := congrFun (congrFun clearedJacobian_eq r) c
    simpa [Matrix.map_apply, Matrix.diagonal_mul] using he
  calc
    (∑ r, jacobian r c * normDual r) =
        (∑ r, (rowScale r * jacobian r c) * (dualNumerator r : ℚ)) /
          (3 * dualDenominator) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r _
      unfold normDual
      ring
    _ = ((∑ r, clearedJacobian r c * dualNumerator r : ℤ) : ℚ) /
          (3 * dualDenominator) := by
      push_cast
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [hm r]
    _ = (normGradientNumerator c : ℚ) / 3 := by
      rw [cleared_dual_equation]
      push_cast
      field_simp

def normDualLabel (r : Fin 96) : ℚ := if 0 < dualNumerator r then 1 else -1

theorem normDualLabel_mul_pos (r : Fin 96) : 0 < normDualLabel r * normDual r := by
  have hr := rowScale_pos r
  have hd : (0 : ℚ) < dualDenominator := by exact_mod_cast dualDenominator_pos
  unfold normDualLabel normDual
  split_ifs with h
  · have hn : (0 : ℚ) < dualNumerator r := by exact_mod_cast h
    positivity
  · have hn : (dualNumerator r : ℚ) < 0 := by
      exact_mod_cast lt_of_le_of_ne (le_of_not_gt h) (dualNumerator_ne_zero r)
    have he : (rowScale r * (dualNumerator r : ℚ)) / (3 * dualDenominator) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hr hn) (by positivity)
    linarith

#print axioms normDual_ne_zero
#print axioms normDual_equation
#print axioms normDualLabel_mul_pos

end HeadComplexity.CoordinateZeroFiber
