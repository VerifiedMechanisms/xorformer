import HeadComplexity.Polynomial.LowRankCrossRecovery

set_option linter.style.header false

/-!
# Entrywise quantitative recovery from an invertible six-by-six cross block

All estimates use ordinary entries and explicit finite sums. In particular,
they do not assume bounded numerator parameters in a competing representation.
-/

namespace HeadComplexity.QuantitativeCrossRecovery
noncomputable section
open scoped BigOperators Matrix

theorem inverse_difference (A B : Matrix (Fin 6) (Fin 6) ℝ)
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB), Matrix.mul_one,
    Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), Matrix.one_mul]

theorem inverse_entry_difference (A B : Matrix (Fin 6) (Fin 6) ℝ)
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) (K e : ℝ) (hK : 0 ≤ K) (he : 0 ≤ e)
    (hAI : ∀ i j, |A⁻¹ i j| ≤ K) (hBI : ∀ i j, |B⁻¹ i j| ≤ K)
    (hAB : ∀ i j, |A i j - B i j| ≤ e) (i j : Fin 6) :
    |A⁻¹ i j - B⁻¹ i j| ≤ 36 * K ^ 2 * e := by
  change |(A⁻¹ - B⁻¹) i j| ≤ _
  rw [inverse_difference A B hA hB]
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.sub_apply]
  calc
    _ ≤ ∑ p, |∑ q, A⁻¹ i q * (B q p - A q p) * B⁻¹ p j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, ∑ q, |A⁻¹ i q * (B q p - A q p) * B⁻¹ p j| :=
      Finset.sum_le_sum (fun p _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ p : Fin 6, ∑ q : Fin 6, K * e * K := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro q _
      rw [abs_mul, abs_mul]
      gcongr
      · exact hAI _ _
      · simpa only [abs_sub_comm] using hAB q p
      · exact hBI _ _
    _ = _ := by simp; ring

theorem triple_difference (x a y x' a' y' B K r d : ℝ)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (_hx : |x| ≤ B) (hy : |y| ≤ B) (hx' : |x'| ≤ B) (_hy' : |y'| ≤ B)
    (ha : |a| ≤ K) (ha' : |a'| ≤ K)
    (hxx : |x - x'| ≤ r) (hyy : |y - y'| ≤ r) (haa : |a - a'| ≤ d) :
    |x * a * y - x' * a' * y'| ≤ 2 * B * K * r + B ^ 2 * d := by
  have hid : x * a * y - x' * a' * y' =
      (x - x') * a * y + x' * (a - a') * y + x' * a' * (y - y') := by ring
  rw [hid]
  calc
    _ ≤ |(x - x') * a * y + x' * (a - a') * y| + |x' * a' * (y - y')| := abs_add_le _ _
    _ ≤ (|(x - x') * a * y| + |x' * (a - a') * y|) + |x' * a' * (y - y')| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ r * K * B + B * d * B + B * K * r := by
      simp only [abs_mul]
      gcongr
    _ = _ := by ring

theorem double_sum_difference (x y x' y' : Fin 6 → ℝ)
    (A A' : Matrix (Fin 6) (Fin 6) ℝ) (B K r d : ℝ)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (hx : ∀ i, |x i| ≤ B) (hy : ∀ i, |y i| ≤ B)
    (hx' : ∀ i, |x' i| ≤ B) (hy' : ∀ i, |y' i| ≤ B)
    (hA : ∀ i j, |A i j| ≤ K) (hA' : ∀ i j, |A' i j| ≤ K)
    (hxx : ∀ i, |x i - x' i| ≤ r) (hyy : ∀ i, |y i - y' i| ≤ r)
    (hAA : ∀ i j, |A i j - A' i j| ≤ d) :
    |(∑ i, ∑ j, x i * A i j * y j) - (∑ i, ∑ j, x' i * A' i j * y' j)| ≤
      36 * (2 * B * K * r + B ^ 2 * d) := by
  rw [← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |∑ j, (x i * A i j * y j - x' i * A' i j * y' j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |x i * A i j * y j - x' i * A' i j * y' j| :=
      Finset.sum_le_sum (fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin 6, ∑ j : Fin 6, (2 * B * K * r + B ^ 2 * d) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact triple_difference _ _ _ _ _ _ B K r d hB hK hr hd
        (hx i) (hy j) (hx' i) (hy' j) (hA i j) (hA' i j) (hxx i) (hyy j) (hAA i j)
    _ = _ := by simp; ring

/-- Recover one arbitrary entry, allowing different errors for the cross block
and the two border vectors. This is used for both stages of cubic completion. -/
theorem entry_error_bound {ι κ : Type*} [Fintype κ]
    (M N : Matrix ι κ ℝ) (a : Fin 6 → ι) (b : Fin 6 → κ)
    (hM : M.rank ≤ 6) (hN : N.rank ≤ 6)
    (hdetM : (M.submatrix a b).det ≠ 0) (hdetN : (N.submatrix a b).det ≠ 0)
    (i : ι) (j : κ) (B K r e : ℝ)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hr : 0 ≤ r) (he : 0 ≤ e)
    (hMI : ∀ p q, |(M.submatrix a b)⁻¹ p q| ≤ K)
    (hNI : ∀ p q, |(N.submatrix a b)⁻¹ p q| ≤ K)
    (hcross : ∀ p q, |M (a p) (b q) - N (a p) (b q)| ≤ e)
    (hrowM : ∀ p, |M i (b p)| ≤ B) (hrowN : ∀ p, |N i (b p)| ≤ B)
    (hcolM : ∀ q, |M (a q) j| ≤ B) (hcolN : ∀ q, |N (a q) j| ≤ B)
    (hrow : ∀ p, |M i (b p) - N i (b p)| ≤ r)
    (hcol : ∀ q, |M (a q) j - N (a q) j| ≤ r) :
    |M i j - N i j| ≤ 36 * (2 * B * K * r + B ^ 2 * (36 * K ^ 2 * e)) := by
  rw [LowRankCrossRecovery.entry_of_rank_le M a b hM hdetM i j,
    LowRankCrossRecovery.entry_of_rank_le N a b hN hdetN i j]
  apply double_sum_difference _ _ _ _ _ _ B K r (36 * K ^ 2 * e)
    hB hK hr (by positivity) hrowM hcolM hrowN hcolN hMI hNI hrow hcol
  exact inverse_entry_difference _ _ hdetM hdetN K e hK he hMI hNI hcross

def firstErrorFactor (K : ℝ) : ℝ := 2000 * K + 500000 * K ^ 2

theorem first_stage_constant (K e : ℝ) (hK : 0 ≤ K) (he : 0 ≤ e) :
    36 * (2 * 19 * K * e + 19 ^ 2 * (36 * K ^ 2 * e)) ≤ firstErrorFactor K * e := by
  unfold firstErrorFactor
  nlinarith [sq_nonneg K, mul_nonneg (sq_nonneg K) he, mul_nonneg hK he]

theorem second_stage_constant (K L e : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) (he : 0 ≤ e) :
    36 * (2 * 38 * K * (2 * L * e) + 38 ^ 2 * (36 * K ^ 2 * e)) ≤
      (6000 * L * K + 2000000 * K ^ 2) * e := by
  nlinarith [mul_nonneg (mul_nonneg hL hK) he, mul_nonneg (sq_nonneg K) he]

end
end HeadComplexity.QuantitativeCrossRecovery
