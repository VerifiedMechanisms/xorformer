import HeadComplexity.Research.GlobalParityMargin
import HeadComplexity.Research.BooleanPolynomialSupport
import HeadComplexity.Results.AffineFreeSparsity

set_option linter.style.header false

/-! Exact nonnegative localization to one parity class, hence to one Hamming
layer, requires at least n genuine heads. This does not concern approximate
gates or signed corrections supported on both parity classes. -/

noncomputable section
namespace HeadComplexity.ExactLayerGateLowerBound

open Finset MvPolynomial GlobalParityMargin
open scoped BigOperators

theorem squarefree_full_product {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    squarefreeMonomial S x = ∏ i, if i ∈ S then boolToReal (x i) else 1 := by
  classical
  simp [squarefreeMonomial, Finset.prod_ite_mem]

theorem squarefree_parity_moment_zero {n : ℕ} (S : Finset (Fin n))
    (hS : S.card < n) :
    (∑ x : Cube n, parity x * squarefreeMonomial S x) = 0 := by
  classical
  have hcard : S.card < (Finset.univ : Finset (Fin n)).card := by simpa using hS
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp_rw [squarefree_full_product, parity, ← Finset.prod_mul_distrib]
  rw [sum_product (fun i b ↦ bitSign b * (if i ∈ S then boolToReal b else 1))]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi, bitSign]

theorem polynomial_parity_moment_zero {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree < n) :
    (∑ x : Cube n, parity x * eval (cubePoint x) P) = 0 := by
  classical
  let Q := SquarefreePolynomial.ofMvPolynomial P
  have hQ : Q.DegreeLE P.totalDegree :=
    SquarefreePolynomial.ofMvPolynomial_degreeLE P le_rfl
  have heval (x : Cube n) : eval (cubePoint x) P = Q.eval x :=
    (SquarefreePolynomial.ofMvPolynomial_eval P x).symm
  simp_rw [heval, ← SquarefreePolynomial.fullSum_eq_eval, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro S _
  by_cases hz : Q.coeff S = 0
  · simp [hz]
  · have hS : S.card < n := (hQ S hz).trans_lt hP
    calc
      (∑ x : Cube n, parity x * (Q.coeff S * squarefreeMonomial S x)) =
          Q.coeff S * ∑ x : Cube n, parity x * squarefreeMonomial S x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [squarefree_parity_moment_zero S hS, mul_zero]

theorem polynomial_degree_ge_of_weak_parity {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (s : ℝ)
    (hpos : ∀ x, 0 ≤ s * parity x * eval (cubePoint x) P)
    (hne : ∃ x, 0 < s * parity x * eval (cubePoint x) P) :
    n ≤ P.totalDegree := by
  by_contra hn
  have hzero := polynomial_parity_moment_zero P (Nat.lt_of_not_ge hn)
  have hp : 0 < ∑ x : Cube n, s * parity x * eval (cubePoint x) P := by
    apply Finset.sum_pos' (fun x _ ↦ hpos x)
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, Finset.mem_univ x, hx⟩
  have heq : (∑ x : Cube n, s * parity x * eval (cubePoint x) P) = 0 := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hzero, mul_zero]
  linarith

/-- An exact original score weakly supported with the sign of one parity
orientation, and nonzero somewhere, needs at least n heads. -/
theorem original_weak_parity_heads_ge {n H : ℕ}
    (phi : Fin H → FracAtom n) (c s : ℝ)
    (hpos : ∀ x, 0 ≤ s * parity x * (c + ∑ h, (phi h).eval x))
    (hne : ∃ x, 0 < s * parity x * (c + ∑ h, (phi h).eval x)) : n ≤ H := by
  have hclear (x : Cube n) :
      s * parity x * eval (cubePoint x) (clearedAtomPoly phi c) =
        eval (cubePoint x) (atomDenProduct phi) *
          (s * parity x * (c + ∑ h, (phi h).eval x)) := by
    rw [clearedAtomPoly_eval]
    ring
  have hp : ∀ x, 0 ≤ s * parity x * eval (cubePoint x) (clearedAtomPoly phi c) := by
    intro x
    rw [hclear]
    exact mul_nonneg (atomDenProduct_eval_pos phi x).le (hpos x)
  have hne' : ∃ x, 0 < s * parity x * eval (cubePoint x) (clearedAtomPoly phi c) := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨x, ?_⟩
    rw [hclear]
    exact mul_pos (atomDenProduct_eval_pos phi x) hx
  exact (polynomial_degree_ge_of_weak_parity _ s hp hne').trans
    (clearedAtomPoly_totalDegree_le phi c)

/-- A nonnegative score with all nonzero entries in one parity class is an
exact positive gate and requires at least n heads. -/
theorem original_nonnegative_parity_support_heads_ge {n H : ℕ}
    (phi : Fin H → FracAtom n) (c : ℝ) (x₀ : Cube n)
    (hpos : ∀ x, 0 ≤ c + ∑ h, (phi h).eval x)
    (h₀ : 0 < c + ∑ h, (phi h).eval x₀)
    (hsupp : ∀ x, c + ∑ h, (phi h).eval x ≠ 0 → parity x = parity x₀) :
    n ≤ H := by
  apply original_weak_parity_heads_ge phi c (parity x₀)
  · intro x
    by_cases hz : c + ∑ h, (phi h).eval x = 0
    · simp [hz]
    · rw [hsupp x hz, ← pow_two, parity_sq, one_mul]
      exact hpos x
  · refine ⟨x₀, ?_⟩
    rw [← pow_two, parity_sq, one_mul]
    exact h₀

theorem parity_eq_hamming_pow {n : ℕ} (x : Cube n) :
    parity x = (-1 : ℝ) ^ hammingWeight x := by
  rw [← prod_one_sub_two]
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> norm_num [bitSign, boolToReal]

/-- In particular an exact nonnegative single-Hamming-layer gate cannot be
implemented using fewer than n original heads. -/
theorem original_nonnegative_layer_gate_heads_ge {n H k : ℕ}
    (phi : Fin H → FracAtom n) (c : ℝ) (x₀ : Cube n)
    (hpos : ∀ x, 0 ≤ c + ∑ h, (phi h).eval x)
    (h₀ : 0 < c + ∑ h, (phi h).eval x₀)
    (hsupp : ∀ x, c + ∑ h, (phi h).eval x ≠ 0 → hammingWeight x = k) :
    n ≤ H := by
  apply original_nonnegative_parity_support_heads_ge phi c x₀ hpos h₀
  intro x hx
  rw [parity_eq_hamming_pow, parity_eq_hamming_pow,
    hsupp x hx, hsupp x₀ (ne_of_gt h₀)]

end HeadComplexity.ExactLayerGateLowerBound
