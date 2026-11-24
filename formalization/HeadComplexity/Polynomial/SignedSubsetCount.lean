import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option linter.style.header false

/-!
# Counting signed subsets of bounded cardinality

The exponential estimate follows directly from the powerset generating
function. It is the combinatorial factor in the polynomial sign-pattern bound.
-/

namespace HeadComplexity.PolynomialRootCount

open Finset

/-- A subset of at most `n` indices. -/
abbrev SmallSubset (I : Type*) (n : ℕ) := {s : Finset I // s.card ≤ n}

/-- A subset of at most `n` indices, with a Boolean sign on each selected index. -/
abbrev SignedSubset (I : Type*) (n : ℕ) := Σ s : SmallSubset I n, (s.val → Bool)

noncomputable instance signedSubsetFintype (I : Type*) [Fintype I] (n : ℕ) :
    Fintype (SignedSubset I n) := by
  classical
  unfold SignedSubset
  infer_instance

/-- The usual binomial-tail estimate, obtained without factorial estimates. -/
theorem smallSubset_card_bound (I : Type*) [Fintype I] {n : ℕ}
    (hn : 0 < n) (hnI : n ≤ Fintype.card I) :
    (Fintype.card (SmallSubset I n) : ℝ) ≤
      (Real.exp 1 * Fintype.card I / n) ^ n := by
  classical
  let m := Fintype.card I
  have hm : 0 < m := lt_of_lt_of_le hn hnI
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let t : ℝ := n / m
  have ht : 0 < t := div_pos hnR hmR
  have ht1 : t ≤ 1 := (div_le_one hmR).mpr (by exact_mod_cast hnI)
  have hmt : (m : ℝ) * t = n := by dsimp [t]; field_simp
  let A : Finset (Finset I) := Finset.univ.filter fun s ↦ s.card ≤ n
  have hcard : Fintype.card (SmallSubset I n) = A.card := Fintype.card_subtype _
  have hsum : (A.card : ℝ) * t ^ n ≤ ∑ s : Finset I, t ^ s.card := by
    calc
      (A.card : ℝ) * t ^ n = ∑ _s ∈ A, t ^ n := by simp
      _ ≤ ∑ s ∈ A, t ^ s.card := Finset.sum_le_sum fun s hs ↦
        pow_le_pow_of_le_one ht.le ht1 (Finset.mem_filter.mp hs).2
      _ ≤ ∑ s : Finset I, t ^ s.card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun _ _ _ ↦ by positivity)
  have hid : (∑ s : Finset I, t ^ s.card) = (1 + t) ^ m := by
    simpa [m] using (Finset.prod_one_add (f := fun _ : I ↦ t) Finset.univ).symm
  have hexp : (1 + t) ^ m ≤ Real.exp 1 ^ n := by
    have hh := Real.prod_one_add_le_exp_sum (Finset.univ : Finset I) (fun _ ↦ ht.le)
    simp only [Finset.prod_const, Finset.card_univ, Finset.sum_const, nsmul_eq_mul] at hh
    change (1 + t) ^ m ≤ Real.exp ((m : ℝ) * t) at hh
    rw [hmt] at hh
    simpa only [← Real.exp_nat_mul, mul_one] using hh
  have hbound : (A.card : ℝ) ≤ (Real.exp 1 / t) ^ n := by
    rw [div_pow]
    exact (le_div_iff₀ (pow_pos ht n)).mpr ((hsum.trans_eq hid).trans hexp)
  rw [hcard]
  convert hbound using 1
  congr 1
  dsimp [t, m]
  field_simp

/-- Assigning a sign to every selected index contributes at most `2^n`. -/
theorem signedSubset_card_le (I : Type*) [Fintype I] (n : ℕ) :
    Fintype.card (SignedSubset I n) ≤ 2 ^ n * Fintype.card (SmallSubset I n) := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ s : SmallSubset I n, Fintype.card (s.val → Bool)) ≤
        ∑ _s : SmallSubset I n, 2 ^ n := by
      apply Finset.sum_le_sum
      intro s _
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) s.2
    _ = _ := by simp [mul_comm]

/-- Quantitative bound for subsets with assigned signs. -/
theorem signedSubset_card_bound (I : Type*) [Fintype I] {n : ℕ}
    (hn : 0 < n) (hnI : n ≤ Fintype.card I) :
    (Fintype.card (SignedSubset I n) : ℝ) ≤
      (2 * Real.exp 1 * Fintype.card I / n) ^ n := by
  have hnat := signedSubset_card_le I n
  have hreal : (Fintype.card (SignedSubset I n) : ℝ) ≤
      (2 : ℝ) ^ n * Fintype.card (SmallSubset I n) := by exact_mod_cast hnat
  calc
    _ ≤ (2 : ℝ) ^ n * (Real.exp 1 * Fintype.card I / n) ^ n :=
      hreal.trans (mul_le_mul_of_nonneg_left (smallSubset_card_bound I hn hnI) (by positivity))
    _ = _ := by rw [← mul_pow]; congr 1; ring

end HeadComplexity.PolynomialRootCount
