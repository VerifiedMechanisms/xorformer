import Mathlib.Tactic

set_option linter.style.header false

/-! Finite algebraic ingredients for symmetric row balancing.
The generic-rank argument and convex minimization proof are in the companion note. -/
namespace HeadComplexity.SymmetricRowBalancing
open Finset

theorem translation_sum {G : Type*} [AddGroup G] [Fintype G]
    (f : G → ℝ) (x : G) : (∑ g, f (x + g)) = ∑ g, f g := by
  exact Equiv.sum_comp (Equiv.addLeft x) f

theorem constant_average {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (c r : ℝ) (ha : ∀ i, a i = c) (hs : ∑ i, a i = r) :
    c = r / Fintype.card ι := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (Fintype.card ι : ℝ) * c = r := by simpa [ha] using hs
  apply (eq_div_iff hn).mpr
  nlinarith [he]

theorem positive_scaling_sign (s y v : ℝ) (hs : 0 < s) :
    0 < y * (s * v) ↔ 0 < y * v := by
  rw [show y * (s * v) = s * (y * v) by ring]
  exact mul_pos_iff_of_pos_left hs

theorem squared_mass_bound {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (B : ℝ) (hb : ∀ i, |v i| ≤ B) :
    ∑ i, (v i) ^ 2 ≤ B * ∑ i, |v i| := by
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_right (hb i) (abs_nonneg (v i))
  nlinarith [sq_abs (v i)]

theorem supported_trace_bound {ι : Type*} [Fintype ι]
    (T : Finset ι) (q : ι → ℝ) (c k : ℝ)
    (hout : ∀ i ∉ T, q i = 0) (hdiag : ∀ i ∈ T, q i ≤ c)
    (htrace : ∑ i, q i = k) : k ≤ T.card * c := by
  classical
  have hsum : (∑ i, q i) = ∑ i ∈ T, q i := by
    symm
    apply sum_subset (subset_univ T)
    intro i _ hi
    exact hout i hi
  rw [hsum] at htrace
  rw [← htrace]
  calc
    ∑ i ∈ T, q i ≤ ∑ _i ∈ T, c := sum_le_sum hdiag
    _ = (T.card : ℝ) * c := by simp

theorem balanced_line_diagonal {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (hy : ∀ i, (y i) ^ 2 = 1) (i : ι) :
    y i * y i / (Fintype.card ι : ℝ) = 1 / (Fintype.card ι : ℝ) := by
  rw [← pow_two, hy]

theorem balanced_line_idempotent {ι : Type*} [Fintype ι] [Nonempty ι]
    (y : ι → ℝ) (hy : ∀ i, (y i) ^ 2 = 1) (i j : ι) :
    (∑ k, (y i * y k / (Fintype.card ι : ℝ)) *
      (y k * y j / (Fintype.card ι : ℝ))) =
      y i * y j / (Fintype.card ι : ℝ) := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : ∀ k, (y i * y k / (Fintype.card ι : ℝ)) *
      (y k * y j / (Fintype.card ι : ℝ)) =
      y i * y j / (Fintype.card ι : ℝ) ^ 2 := by
    intro k
    field_simp
    simp [hy k]
  simp_rw [hs]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  field_simp

theorem balanced_line_fixed {ι : Type*} [Fintype ι] [Nonempty ι]
    (y : ι → ℝ) (hy : ∀ i, (y i) ^ 2 = 1) (i : ι) :
    (∑ j, (y i * y j / (Fintype.card ι : ℝ)) * y j) = y i := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : ∀ j, (y i * y j / (Fintype.card ι : ℝ)) * y j =
      y i / (Fintype.card ι : ℝ) := by
    intro j
    field_simp
    simp [hy j]
  simp_rw [hs]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  field_simp

end HeadComplexity.SymmetricRowBalancing
