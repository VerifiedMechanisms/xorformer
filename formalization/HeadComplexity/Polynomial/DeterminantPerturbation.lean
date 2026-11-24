import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Tactic

set_option linter.style.header false

/-! # Elementary entrywise perturbation bounds for six-by-six determinants -/

namespace HeadComplexity.DeterminantPerturbation
noncomputable section
open scoped BigOperators

/-- A telescoping product estimate with an extra factor avoiding subtraction
in the exponent. It also applies to the empty product and a zero bound. -/
theorem prod_sub_prod_mul_bound {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (M e : ℝ) (hM : 0 ≤ M) (he : 0 ≤ e)
    (hf : ∀ i ∈ s, |f i| ≤ M) (hg : ∀ i ∈ s, |g i| ≤ M)
    (hfg : ∀ i ∈ s, |f i - g i| ≤ e) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| * M ≤ s.card * M ^ s.card * e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have ih' := ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ hg j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ hfg j (Finset.mem_insert_of_mem hj))
    have hp : |∏ j ∈ s, g j| ≤ M ^ s.card := by
      rw [Finset.abs_prod]
      simpa using Finset.prod_le_prod (fun j _ ↦ abs_nonneg (g j))
        (fun j hj ↦ hg j (Finset.mem_insert_of_mem hj))
    have ht : |f i * (∏ j ∈ s, f j) - g i * ∏ j ∈ s, g j| ≤
        M * |(∏ j ∈ s, f j) - ∏ j ∈ s, g j| + e * M ^ s.card := by
      have hid : f i * (∏ j ∈ s, f j) - g i * ∏ j ∈ s, g j =
          f i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j) +
            (f i - g i) * ∏ j ∈ s, g j := by ring
      rw [hid]
      calc
        _ ≤ |f i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j)| +
            |(f i - g i) * ∏ j ∈ s, g j| := abs_add_le _ _
        _ ≤ M * |(∏ j ∈ s, f j) - ∏ j ∈ s, g j| + e * M ^ s.card := by
          rw [abs_mul, abs_mul]
          gcongr
          · exact hf i (Finset.mem_insert_self _ _)
          · exact hfg i (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    calc
      _ ≤ (M * |(∏ j ∈ s, f j) - ∏ j ∈ s, g j| + e * M ^ s.card) * M :=
        mul_le_mul_of_nonneg_right ht hM
      _ = M * (|(∏ j ∈ s, f j) - ∏ j ∈ s, g j| * M) + e * M ^ (s.card + 1) := by
        rw [pow_succ]
        ring
      _ ≤ M * (s.card * M ^ s.card * e) + e * M ^ (s.card + 1) := by gcongr
      _ = (s.card + 1 : ℕ) * M ^ (s.card + 1) * e := by
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        ring

/-- The constant is six factorial times six, from Leibniz and telescoping.
All bounds concern ordinary matrix entries, not an operator norm. -/
theorem det_sub_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 6) (A B : Matrix ι ι ℝ)
    (M e : ℝ) (hM : 0 < M) (he : 0 ≤ e)
    (hA : ∀ i j, |A i j| ≤ M) (hB : ∀ i j, |B i j| ≤ M)
    (hAB : ∀ i j, |A i j - B i j| ≤ e) :
    |A.det - B.det| ≤ 4320 * M ^ 5 * e := by
  have ht (σ : Equiv.Perm ι) :
      |σ.sign • (∏ i, A (σ i) i) - σ.sign • (∏ i, B (σ i) i)| * M ≤
        6 * M ^ 6 * e := by
    rw [← smul_sub]
    have hs := (AbsoluteValue.abs : AbsoluteValue ℝ ℝ).map_units_int_smul
      σ.sign ((∏ i, A (σ i) i) - ∏ i, B (σ i) i)
    change |σ.sign • ((∏ i, A (σ i) i) - ∏ i, B (σ i) i)| =
      |(∏ i, A (σ i) i) - ∏ i, B (σ i) i| at hs
    rw [hs]
    simpa [hcard] using prod_sub_prod_mul_bound Finset.univ
      (fun i ↦ A (σ i) i) (fun i ↦ B (σ i) i) M e hM.le he
      (fun i _ ↦ hA _ _) (fun i _ ↦ hB _ _) (fun i _ ↦ hAB _ _)
  apply (mul_le_mul_iff_left₀ hM).mp
  calc
    |A.det - B.det| * M =
        |∑ σ : Equiv.Perm ι,
          (σ.sign • (∏ i, A (σ i) i) - σ.sign • (∏ i, B (σ i) i))| * M := by
      rw [Matrix.det_apply, Matrix.det_apply, Finset.sum_sub_distrib]
    _ ≤ (∑ σ : Equiv.Perm ι,
        |σ.sign • (∏ i, A (σ i) i) - σ.sign • (∏ i, B (σ i) i)|) * M :=
      mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hM.le
    _ = ∑ σ : Equiv.Perm ι,
        |σ.sign • (∏ i, A (σ i) i) - σ.sign • (∏ i, B (σ i) i)| * M :=
      by rw [Finset.sum_mul]
    _ ≤ ∑ _σ : Equiv.Perm ι, 6 * M ^ 6 * e :=
      Finset.sum_le_sum (fun σ _ ↦ ht σ)
    _ = (4320 * M ^ 5 * e) * M := by
      simp [Fintype.card_perm, hcard, pow_succ]
      ring

end
end HeadComplexity.DeterminantPerturbation
