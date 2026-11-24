import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option linter.style.header false

/-!
# Elementary bounds for finite interpolation matrices

The estimates use only the Leibniz formula, adjugates, and finite sums. They
support the coefficient-recovery step of Theorem 22 without claiming the
existence of its evaluation minor or the complete Boolean lower bound.
-/

namespace HeadComplexity.FiniteInterpolationBounds

noncomputable section

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem abs_det_le_factorial (A : Matrix ι ι ℝ) (hA : ∀ i j, |A i j| ≤ 1) :
    |A.det| ≤ (Nat.factorial (Fintype.card ι) : ℝ) := by
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, |((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i, A (σ i) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul, ← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one, one_mul,
        Finset.abs_prod]
      simpa using Finset.prod_le_prod (fun i _ ↦ abs_nonneg (A (σ i) i))
        (fun i _ ↦ hA (σ i) i)
    _ = (Nat.factorial (Fintype.card ι) : ℝ) := by simp [Fintype.card_perm]

theorem abs_adjugate_le_factorial (A : Matrix ι ι ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) (i j : ι) :
    |A.adjugate i j| ≤ (Nat.factorial (Fintype.card ι) : ℝ) := by
  rw [Matrix.adjugate_apply]
  apply abs_det_le_factorial
  intro k l
  by_cases hk : k = j
  · subst k
    simp only [Matrix.updateRow_self]
    by_cases hl : l = i <;> simp [hl]
  · simpa [Matrix.updateRow_ne hk] using hA k l

theorem inverse_entry_bound (A : Matrix ι ι ℝ) (hA : ∀ i j, |A i j| ≤ 1)
    (i j : ι) :
    |A⁻¹ i j| ≤ (Nat.factorial (Fintype.card ι) : ℝ) / |A.det| := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  change |A.det⁻¹ * A.adjugate i j| ≤ _
  rw [abs_mul, abs_inv, div_eq_mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_adjugate_le_factorial A hA i j)
    (inv_nonneg.mpr (abs_nonneg _))

theorem inverse_row_bound (A : Matrix ι ι ℝ) (hA : ∀ i j, |A i j| ≤ 1)
    (i : ι) :
    (∑ j, |A⁻¹ i j|) ≤ (Fintype.card ι : ℝ) *
      (Nat.factorial (Fintype.card ι) : ℝ) / |A.det| := by
  calc
    _ ≤ ∑ _j : ι, (Nat.factorial (Fintype.card ι) : ℝ) / |A.det| :=
      Finset.sum_le_sum fun j _ ↦ inverse_entry_bound A hA i j
    _ = _ := by simp [mul_div_assoc]

omit [DecidableEq ι] in
theorem mulVec_abs_bound (A : Matrix ι ι ℝ) (x : ι → ℝ) (K ε : ℝ)
    (hε : 0 ≤ ε) (hA : ∀ i, ∑ j, |A i j| ≤ K)
    (hx : ∀ i, |x i| ≤ ε) (i : ι) : |(A *ᵥ x) i| ≤ K * ε := by
  calc
    _ ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |A i j| * ε := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
    _ = (∑ j, |A i j|) * ε := (Finset.sum_mul _ _ _).symm
    _ ≤ K * ε := mul_le_mul_of_nonneg_right (hA i) hε

theorem coefficient_recovery (A B : Matrix ι ι ℝ) (hBA : B * A = 1)
    (x : ι → ℝ) (K ε : ℝ) (hε : 0 ≤ ε)
    (hB : ∀ i, ∑ j, |B i j| ≤ K)
    (hx : ∀ i, |(A *ᵥ x) i| ≤ ε) (i : ι) : |x i| ≤ K * ε := by
  have h := mulVec_abs_bound B (A *ᵥ x) K ε hε hB hx i
  simpa only [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec] using h

/-- Clearing positive row denominators gives an integer determinant. -/
theorem integer_row_det (A : Matrix ι ι ℝ) (K : Matrix ι ι ℤ) (q : ι → ℝ)
    (hrow : ∀ i j, q i * A i j = (K i j : ℝ)) :
    (∏ i, q i) * A.det = (K.det : ℝ) := by
  have heq : Matrix.diagonal q * A = K.map (fun k ↦ (k : ℝ)) := by
    ext i j
    simpa only [Matrix.diagonal_mul, Matrix.map_apply] using hrow i j
  have hdet := congrArg Matrix.det heq
  simpa only [Matrix.det_mul, Matrix.det_diagonal, ← Int.cast_det] using hdet

theorem det_lower_of_integer_rows (A : Matrix ι ι ℝ) (K : Matrix ι ι ℤ)
    (q : ι → ℝ) (hq : ∀ i, 0 < q i) (hdet : A.det ≠ 0)
    (hrow : ∀ i j, q i * A i j = (K i j : ℝ)) :
    1 / (∏ i, q i) ≤ |A.det| := by
  have hqprod : 0 < ∏ i, q i := Finset.prod_pos (fun i _ ↦ hq i)
  have h := integer_row_det A K q hrow
  have hk : K.det ≠ 0 := by
    intro hk
    rw [hk, Int.cast_zero] at h
    exact (mul_ne_zero (ne_of_gt hqprod) hdet) h
  have hkabs : (1 : ℝ) ≤ |(K.det : ℝ)| := by
    exact_mod_cast Int.one_le_abs hk
  rw [← h, abs_mul, abs_of_pos hqprod] at hkabs
  exact (div_le_iff₀ hqprod).mpr (by simpa [mul_comm] using hkabs)

theorem inverse_row_bound_of_integer_rows (A : Matrix ι ι ℝ) (K : Matrix ι ι ℤ)
    (q : ι → ℝ) (hA : ∀ i j, |A i j| ≤ 1) (hq : ∀ i, 0 < q i)
    (hdet : A.det ≠ 0) (hrow : ∀ i j, q i * A i j = (K i j : ℝ)) (i : ι) :
    (∑ j, |A⁻¹ i j|) ≤ (Fintype.card ι : ℝ) *
      (Nat.factorial (Fintype.card ι) : ℝ) * (∏ i, q i) := by
  have hp : 0 < ∏ i, q i := Finset.prod_pos (fun i _ ↦ hq i)
  have hd := det_lower_of_integer_rows A K q hq hdet hrow
  have hdinv : 1 / |A.det| ≤ ∏ i, q i := by
    have hmul : 1 ≤ |A.det| * (∏ i, q i) := (div_le_iff₀ hp).mp hd
    exact (div_le_iff₀ (abs_pos.mpr hdet)).mpr (by simpa [mul_comm] using hmul)
  calc
    _ ≤ (Fintype.card ι : ℝ) * (Nat.factorial (Fintype.card ι) : ℝ) / |A.det| :=
      inverse_row_bound A hA i
    _ ≤ _ := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hdinv (mul_nonneg (Nat.cast_nonneg _)
        (Nat.cast_nonneg _))

theorem factorial_cast_le_pow (n : ℕ) : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
  exact_mod_cast Nat.factorial_le_pow n

/-- The loose power-of-two bound used in the finite zero-chart argument.
The factor 679 beyond the sharper cofactor estimate is harmless. -/
theorem inverse_row_bound_679 (A : Matrix (Fin 679) (Fin 679) ℝ)
    (K : Matrix (Fin 679) (Fin 679) ℤ) (q : Fin 679 → ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) (hq : ∀ i, 0 < q i)
    (hqbound : ∀ i, q i ≤ (2 : ℝ) ^ 414) (hdet : A.det ≠ 0)
    (hrow : ∀ i j, q i * A i j = (K i j : ℝ)) (i : Fin 679) :
    (∑ j, |A⁻¹ i j|) < (2 : ℝ) ^ 300000 := by
  have hfact : (Nat.factorial 679 : ℝ) ≤ (2 : ℝ) ^ (10 * 679) := by
    calc
      _ ≤ (679 : ℝ) ^ 679 := factorial_cast_le_pow 679
      _ ≤ ((2 : ℝ) ^ 10) ^ 679 := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = _ := (pow_mul _ _ _).symm
  have hprod : (∏ i, q i) ≤ (2 : ℝ) ^ (414 * 679) := by
    calc
      _ ≤ ∏ _i : Fin 679, (2 : ℝ) ^ 414 :=
        Finset.prod_le_prod (fun i _ ↦ (hq i).le) (fun i _ ↦ hqbound i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
  have hcard : (679 : ℝ) ≤ (2 : ℝ) ^ 10 := by norm_num
  have hbound := inverse_row_bound_of_integer_rows A K q hA hq hdet hrow i
  simp only [Fintype.card_fin] at hbound
  calc
    _ ≤ (679 : ℝ) * (Nat.factorial 679 : ℝ) * (∏ i, q i) := hbound
    _ ≤ (2 : ℝ) ^ 10 * (2 : ℝ) ^ (10 * 679) * (2 : ℝ) ^ (414 * 679) := by
      apply mul_le_mul
      · exact mul_le_mul hcard hfact (Nat.cast_nonneg _) (by positivity)
      · exact hprod
      · exact Finset.prod_nonneg (fun i _ ↦ (hq i).le)
      · positivity
    _ = (2 : ℝ) ^ 287906 := by rw [← pow_add, ← pow_add]
    _ < (2 : ℝ) ^ 300000 := pow_lt_pow_right₀ (by norm_num) (by decide)

end
end HeadComplexity.FiniteInterpolationBounds
