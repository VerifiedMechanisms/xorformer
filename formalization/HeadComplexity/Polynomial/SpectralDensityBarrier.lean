import Mathlib.Tactic

set_option linter.style.header false

/-! A sparsity lower bound for strict signs in a bounded orthogonal dictionary.
This lemma does not assert that head scores have sparse polynomial representations. -/

namespace HeadComplexity.SpectralDensityBarrier
open Finset
open scoped BigOperators

theorem abs_eq_signed (y p : ℝ) (hy : y * y = 1) (hp : 0 < y * p) :
    |p| = y * p := by
  have he : y = 1 ∨ y = -1 := by
    have hz : (y - 1) * (y + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with h | h
    · left; linarith
    · right; linarith
  rcases he with rfl | rfl
  · simpa using abs_of_pos (by simpa using hp : 0 < p)
  · simpa using abs_of_neg (by linarith : p < 0)

theorem spectral_sum_bound {X I : Type*} [Fintype X] [Nonempty X]
    [Fintype I] [Nonempty I] [DecidableEq I] (φ : I → X → ℝ) (y : X → ℝ) (a : I → ℝ)
    (hφ : ∀ i x, |φ i x| ≤ 1)
    (horth : ∀ i j, ∑ x, φ i x * φ j x = if i = j then (Fintype.card X : ℝ) else 0)
    (hy : ∀ x, y x * y x = 1)
    (hp : ∀ x, 0 < y x * ∑ i, a i * φ i x) :
    (Fintype.card X : ℝ) ≤ ∑ i, |∑ x, y x * φ i x| := by
  classical
  let p : X → ℝ := fun x ↦ ∑ i, a i * φ i x
  obtain ⟨i₀, _, hm⟩ := exists_max_image (univ : Finset I) (fun i ↦ |a i|) univ_nonempty
  have hm' (i : I) : |a i| ≤ |a i₀| := hm i (mem_univ _)
  have hK : 0 < |a i₀| := by
    by_contra hn
    have hz : |a i₀| = 0 := le_antisymm (le_of_not_gt hn) (abs_nonneg _)
    have ha (i : I) : a i = 0 := abs_eq_zero.mp (le_antisymm (by simpa [hz] using hm' i)
      (abs_nonneg _))
    obtain ⟨x⟩ := ‹Nonempty X›
    simpa [ha] using hp x
  have hex : ∑ x, φ i₀ x * p x = a i₀ * (Fintype.card X : ℝ) := by
    simp only [p, mul_sum]
    rw [sum_comm]
    calc
      _ = ∑ i, a i * ∑ x, φ i₀ x * φ i x := by
        apply sum_congr rfl
        intro i _
        rw [mul_sum]
        apply sum_congr rfl
        intro x _
        ring
      _ = a i₀ * (Fintype.card X : ℝ) := by simp [horth]
  have hlow : |a i₀| * (Fintype.card X : ℝ) ≤ ∑ x, |p x| := by
    calc
      _ = |∑ x, φ i₀ x * p x| := by
        rw [hex, abs_mul]
        simp only [Nat.abs_cast]
      _ ≤ ∑ x, |φ i₀ x * p x| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, |p x| := by
        apply sum_le_sum
        intro x _
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (hφ _ _)
  have heq : ∑ x, |p x| = ∑ i, a i * ∑ x, y x * φ i x := by
    simp_rw [show ∀ x, |p x| = y x * p x from
      fun x ↦ abs_eq_signed _ _ (hy x) (hp x)]
    simp only [p, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro x _
    ring
  have hupp : ∑ x, |p x| ≤ |a i₀| * ∑ i, |∑ x, y x * φ i x| := by
    rw [heq, mul_sum]
    apply sum_le_sum
    intro i _
    calc
      _ ≤ |a i * ∑ x, y x * φ i x| := le_abs_self _
      _ = |a i| * |∑ x, y x * φ i x| := abs_mul _ _
      _ ≤ |a i₀| * |∑ x, y x * φ i x| := mul_le_mul_of_nonneg_right (hm' _) (abs_nonneg _)
  exact (mul_le_mul_iff_right₀ hK).mp (hlow.trans hupp)

theorem spectral_card_bound {X I : Type*} [Fintype X] [Nonempty X]
    [Fintype I] [Nonempty I] [DecidableEq I]
    (φ : I → X → ℝ) (y : X → ℝ) (a : I → ℝ) (B : ℝ)
    (hφ : ∀ i x, |φ i x| ≤ 1)
    (horth : ∀ i j, ∑ x, φ i x * φ j x = if i = j then (Fintype.card X : ℝ) else 0)
    (hy : ∀ x, y x * y x = 1)
    (hp : ∀ x, 0 < y x * ∑ i, a i * φ i x)
    (hB : ∀ i, |∑ x, y x * φ i x| ≤ B) :
    (Fintype.card X : ℝ) ≤ (Fintype.card I : ℝ) * B := by
  refine (spectral_sum_bound φ y a hφ horth hy hp).trans ?_
  calc
    _ ≤ ∑ _i : I, B := sum_le_sum (fun i _ ↦ hB i)
    _ = (Fintype.card I : ℝ) * B := by simp

theorem tensor_correlation {K X : Type*} [Fintype K] [DecidableEq K] [Fintype X]
    (y φ : K → X → ℝ) :
    (∑ x : K → X, (∏ i, y i (x i)) * (∏ i, φ i (x i))) =
      ∏ i, ∑ z, y i z * φ i z := by
  simp_rw [← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i z ↦ y i z * φ i z)).symm

theorem tensor_correlation_bound {K X : Type*}
    [Fintype K] [DecidableEq K] [Fintype X]
    (y φ : K → X → ℝ) (B : K → ℝ)
    (hB : ∀ i, |∑ z, y i z * φ i z| ≤ B i) :
    |∑ x : K → X, (∏ i, y i (x i)) * (∏ i, φ i (x i))| ≤ ∏ i, B i := by
  rw [tensor_correlation, abs_prod]
  exact prod_le_prod₀ (fun i _ ↦ abs_nonneg _) (fun i _ ↦ hB i)

noncomputable def centralRatio : ℕ → ℝ
  | 0 => 1
  | r + 1 => centralRatio r * (2 * r + 1) / (2 * r + 2)

theorem centralRatio_nonneg (r : ℕ) : 0 ≤ centralRatio r := by
  induction r with
  | zero => norm_num [centralRatio]
  | succ r hr => simp only [centralRatio]; positivity

theorem centralRatio_sq_bound (r : ℕ) : centralRatio r ^ 2 * (r + 1) ≤ 1 := by
  induction r with
  | zero => norm_num [centralRatio]
  | succ r hr =>
    have hr₀ : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hd : (0 : ℝ) < 2 * r + 2 := by positivity
    have hstep : ((2 * (r : ℝ) + 1) / (2 * r + 2)) ^ 2 * (r + 2) ≤ r + 1 := by
      rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hd)]
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hstep (sq_nonneg (centralRatio r))
    simp only [centralRatio, Nat.cast_add, Nat.cast_one]
    calc
      _ = centralRatio r ^ 2 * (((2 * (r : ℝ) + 1) / (2 * r + 2)) ^ 2 * (r + 2)) := by ring
      _ ≤ centralRatio r ^ 2 * (r + 1) := by simpa [mul_assoc] using hh
      _ ≤ 1 := hr

end HeadComplexity.SpectralDensityBarrier
