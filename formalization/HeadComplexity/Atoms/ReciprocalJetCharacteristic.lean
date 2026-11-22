import Mathlib.Algebra.CharP.Lemmas
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic

set_option linter.style.header false

/-! The reciprocal-cube interpolation experiment has systematic dependencies
in characteristics two and three. These identities are auxiliary and make no
claim about the characteristic-zero head-complexity problem. -/
namespace HeadComplexity.ReciprocalJetCharacteristic

open scoped BigOperators

variable {ι K : Type*} [Field K]

def bit (x : ι → Bool) (i : ι) : K := if x i then 1 else 0

theorem bit_sq (x : ι → Bool) (i : ι) : (bit x i : K)^2 = bit x i := by
  simp [bit]

theorem bit_cube (x : ι → Bool) (i : ι) : (bit x i : K)^3 = bit x i := by
  simp [bit]

variable [Fintype ι]

def affine (r : K) (β : ι → K) (x : ι → Bool) : K :=
  r + ∑ i, β i * bit x i

theorem cube_char_three [CharP K 3] (r : K) (β : ι → K) (x : ι → Bool) :
    affine r β x ^ 3 = r^3 + ∑ i, β i^3 * bit x i := by
  rw [affine, add_pow_char, sum_pow_char]
  simp only [mul_pow, bit_cube]

theorem square_char_two [CharP K 2] (β : ι → K) (x : ι → Bool) :
    (∑ i, β i * bit x i)^2 = ∑ i, β i^2 * bit x i := by
  rw [sum_pow_char]
  simp only [mul_pow, bit_sq]

theorem cube_char_two [CharP K 2] (r : K) (β : ι → K) (x : ι → Bool) :
    affine r β x ^ 3 =
      r^3 + ∑ i, (r^2 * β i + r * β i^2) * bit x i +
        ∑ i, ∑ j, β i * β j^2 * (bit x i * bit x j) := by
  have hs : affine r β x ^ 2 = r^2 + ∑ i, β i^2 * bit x i := by
    rw [affine, add_pow_char, square_char_two]
  calc
    affine r β x ^ 3 = affine r β x * affine r β x ^ 2 := by ring
    _ = (r + ∑ i, β i * bit x i) * (r^2 + ∑ i, β i^2 * bit x i) := by
      rw [hs, affine]
    _ = _ := by
      simp only [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      ring_nf
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem constant_identity_char_three [CharP K 3]
    (r : K) (β : ι → K) (x : ι → Bool) (h : affine r β x ≠ 0) :
    r^3 / affine r β x ^ 3 +
      ∑ i, β i^3 * (bit x i / affine r β x ^ 3) = 1 := by
  simp only [← mul_div_assoc]
  rw [← Finset.sum_div, ← add_div, ← cube_char_three]
  exact div_self (pow_ne_zero _ h)

theorem constant_identity_char_two [CharP K 2]
    (r : K) (β : ι → K) (x : ι → Bool) (h : affine r β x ≠ 0) :
    r^3 / affine r β x ^ 3 +
      ∑ i, (r^2 * β i + r * β i^2) * (bit x i / affine r β x ^ 3) +
      ∑ i, ∑ j, (β i * β j^2) * ((bit x i * bit x j) / affine r β x ^ 3) = 1 := by
  simp only [← mul_div_assoc, ← Finset.sum_div, ← add_div]
  rw [← cube_char_two]
  exact div_self (pow_ne_zero _ h)

end HeadComplexity.ReciprocalJetCharacteristic
