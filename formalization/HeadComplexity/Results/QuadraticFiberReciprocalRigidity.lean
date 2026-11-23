import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

open Polynomial

/-- Paired points of a shifted-square fiber separate the exchange equation. -/
theorem paired_level_exchange_zero (n z rate shift F G : ℝ)
    (hn : n ≠ 0) (hrate : rate ≠ 0) (hz : z ≠ -shift)
    (h₁ : (n - 2 * z) * F + rate * z * G = 0)
    (h₂ : (n + 4 * shift + 2 * z) * F - rate * (z + 2 * shift) * G = 0) :
    F = 0 ∧ G = 0 := by
  have he : (2 * n * (z + shift)) * F = 0 := by
    linear_combination (z + 2 * shift) * h₁ + z * h₂
  have hzs : z + shift ≠ 0 := by intro h; apply hz; linarith
  have hnz : 2 * n * (z + shift) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hn) hzs
  have hF : F = 0 := (mul_eq_zero.mp he).resolve_left hnz
  have heG : (2 * rate * n * (z + shift)) * G = 0 := by
    linear_combination (n + 4 * shift + 2 * z) * h₁ - (n - 2 * z) * h₂
  have hnzG : 2 * rate * n * (z + shift) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hrate) hn) hzs
  exact ⟨hF, (mul_eq_zero.mp heG).resolve_left hnzG⟩

private theorem four_reciprocal_clear (n z rate c₁ c₂ c₃ c₄ d₁ d₂ d₃ d₄ : ℝ)
    (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) (h₃ : d₃ ≠ 0) (h₄ : d₄ ≠ 0) :
    ((n - 2 * z) * (c₁ / d₁ - c₂ / d₂) + rate * z * (c₃ / d₃ - c₄ / d₄) = 0) ↔
    ((n - 2 * z) * (c₁ * d₂ * d₃ * d₄ - c₂ * d₁ * d₃ * d₄) +
      rate * z * (c₃ * d₁ * d₂ * d₄ - c₄ * d₁ * d₂ * d₃) = 0) := by
  field_simp
  ring_nf

/-- Eight distinct nonpole samples force the four-reciprocal identity.
The quadratic fiber symmetry then annihilates both differences. The Boolean
layer reduction is manual; no universal head upper bound is asserted. -/
theorem four_reciprocal_quadratic_fiber_rigidity
    (n b rate shift : ℝ) (a c : Fin 4 → ℝ) (hn : n ≠ 0) (hrate : rate ≠ 0)
    (t : Fin 8 → ℝ) (ht : Function.Injective t)
    (hp : ∀ i j, b ^ 2 * (t i + shift) ^ 2 - a j ≠ 0)
    (h : ∀ i, (n - 2 * t i) *
        (c 0 / (b ^ 2 * (t i + shift) ^ 2 - a 0) -
         c 1 / (b ^ 2 * (t i + shift) ^ 2 - a 1)) +
        rate * t i * (c 2 / (b ^ 2 * (t i + shift) ^ 2 - a 2) -
         c 3 / (b ^ 2 * (t i + shift) ^ 2 - a 3)) = 0)
    (z : ℝ) (hz : z ≠ -shift)
    (hzp : ∀ j, b ^ 2 * (z + shift) ^ 2 - a j ≠ 0) :
    c 0 / (b ^ 2 * (z + shift) ^ 2 - a 0) =
      c 1 / (b ^ 2 * (z + shift) ^ 2 - a 1) ∧
    c 2 / (b ^ 2 * (z + shift) ^ 2 - a 2) =
      c 3 / (b ^ 2 * (z + shift) ^ 2 - a 3) := by
  let q (j : Fin 4) (u : ℝ) := b ^ 2 * (u + shift) ^ 2 - a j
  let D (j : Fin 4) : Polynomial ℝ := C (b ^ 2) * (X + C shift) ^ 2 - C (a j)
  let P : Polynomial ℝ :=
    (C n - 2 * X) * (C (c 0) * D 1 * D 2 * D 3 - C (c 1) * D 0 * D 2 * D 3) +
    C rate * X * (C (c 2) * D 0 * D 1 * D 3 - C (c 3) * D 0 * D 1 * D 2)
  have hdeg : P.natDegree ≤ 7 := by
    dsimp [P, D]
    compute_degree!
  have heval (u : ℝ) : P.eval u =
      (n - 2 * u) * (c 0 * q 1 u * q 2 u * q 3 u - c 1 * q 0 u * q 2 u * q 3 u) +
      rate * u * (c 2 * q 0 u * q 1 u * q 3 u - c 3 * q 0 u * q 1 u * q 2 u) := by
    simp [P, D, q]
  have hzero : P = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P ht
    · intro i
      rw [heval]
      exact (four_reciprocal_clear _ _ _ _ _ _ _ _ _ _ _
        (hp i 0) (hp i 1) (hp i 2) (hp i 3)).mp (h i)
    · simpa using Nat.lt_succ_of_le hdeg
  have hall (u : ℝ) (hu : ∀ j, q j u ≠ 0) :
      (n - 2 * u) * (c 0 / q 0 u - c 1 / q 1 u) +
      rate * u * (c 2 / q 2 u - c 3 / q 3 u) = 0 := by
    apply (four_reciprocal_clear _ _ _ _ _ _ _ _ _ _ _ (hu 0) (hu 1) (hu 2) (hu 3)).mpr
    rw [← heval, hzero]
    simp
  have hsquare : ∀ j, q j (-2 * shift - z) = q j z := by intro j; dsimp [q]; ring
  have hpair := hall (-2 * shift - z) (by intro j; rw [hsquare]; exact hzp j)
  simp only [hsquare] at hpair
  have hpair' : (n + 4 * shift + 2 * z) * (c 0 / q 0 z - c 1 / q 1 z) -
      rate * (z + 2 * shift) * (c 2 / q 2 z - c 3 / q 3 z) = 0 := by
    linear_combination hpair
  have hzv := paired_level_exchange_zero n z rate shift _ _ hn hrate hz (hall z hzp) hpair'
  exact ⟨sub_eq_zero.mp hzv.1, sub_eq_zero.mp hzv.2⟩

end HeadComplexity
