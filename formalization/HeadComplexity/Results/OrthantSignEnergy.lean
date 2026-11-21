import Mathlib

set_option linter.style.header false

/-!
Exact second-moment identities for the orthant-dictionary audit.
These are auxiliary counting statements, not a universal head upper bound.
-/

namespace HeadComplexity

open scoped BigOperators

def orthantSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem orthantSign_not (b : Bool) :
    orthantSign (!b) = -orthantSign b := by
  cases b <;> norm_num [orthantSign]

@[simp] theorem orthantSign_mul_self (b : Bool) :
    orthantSign b * orthantSign b = 1 := by
  cases b <;> norm_num [orthantSign]

def flipOrthant {ι : Type*} [DecidableEq ι] (i : ι) (σ : ι → Bool) : ι → Bool :=
  Function.update σ i (!(σ i))

theorem flipOrthant_involutive {ι : Type*} [DecidableEq ι] (i : ι) :
    Function.Involutive (flipOrthant i) := by
  intro σ
  funext j
  by_cases h : j = i
  · subst j; simp [flipOrthant]
  · simp [flipOrthant, h]

theorem sum_orthant_sign_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) :
    (∑ σ : ι → Bool, orthantSign (σ i) * orthantSign (σ j)) =
      if i = j then (2 : ℝ) ^ Fintype.card ι else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp
  · let e := (flipOrthant_involutive i).toPerm (flipOrthant i)
    have h := Equiv.sum_comp e (fun σ : ι → Bool =>
      orthantSign (σ i) * orthantSign (σ j))
    have he : ∀ σ : ι → Bool,
        orthantSign (e σ i) * orthantSign (e σ j) =
          -(orthantSign (σ i) * orthantSign (σ j)) := by
      intro σ
      simp [e, Function.Involutive.toPerm, flipOrthant, Ne.symm hij]
    simp_rw [he] at h
    rw [Finset.sum_neg_distrib] at h
    rw [if_neg hij]
    linarith

theorem sum_orthant_linear_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) :
    (∑ σ : ι → Bool, (∑ i, q i * orthantSign (σ i)) ^ 2) =
      (2 : ℝ) ^ Fintype.card ι * ∑ i, (q i) ^ 2 := by
  classical
  have hexpand (σ : ι → Bool) :
      (∑ i, q i * orthantSign (σ i)) ^ 2 =
      ∑ i, ∑ j, (q i * q j) * (orthantSign (σ i) * orthantSign (σ j)) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i, ∑ j, ∑ σ : ι → Bool,
        (q i * q j) * (orthantSign (σ i) * orthantSign (σ j)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, (q i * q j) *
        (if i = j then (2 : ℝ) ^ Fintype.card ι else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.mul_sum, sum_orthant_sign_product]
    _ = _ := by
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [← Finset.sum_mul]
      simp only [pow_two]
      ring

theorem orthant_exception_second_moment {ι : Type*}
    [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    (((Finset.univ : Finset (ι → Bool)).filter
      (fun σ => r < |∑ i, q i * orthantSign (σ i)|)).card : ℝ) * r ^ 2 ≤
      (2 : ℝ) ^ Fintype.card ι * ∑ i, (q i) ^ 2 := by
  classical
  let bad := (Finset.univ : Finset (ι → Bool)).filter
    (fun σ => r < |∑ i, q i * orthantSign (σ i)|)
  have hpoint (σ : ι → Bool) (hσ : σ ∈ bad) :
      r ^ 2 ≤ (∑ i, q i * orthantSign (σ i)) ^ 2 := by
    have h := (Finset.mem_filter.mp hσ).2
    nlinarith [sq_abs (∑ i, q i * orthantSign (σ i))]
  have hsum := Finset.sum_le_sum hpoint
  have hsub : (∑ σ ∈ bad, (∑ i, q i * orthantSign (σ i)) ^ 2) ≤
      ∑ σ : ι → Bool, (∑ i, q i * orthantSign (σ i)) ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun σ _ _ => sq_nonneg _)
  have h := hsum.trans hsub
  simpa only [Finset.sum_const, nsmul_eq_mul, sum_orthant_linear_square] using h

end HeadComplexity
