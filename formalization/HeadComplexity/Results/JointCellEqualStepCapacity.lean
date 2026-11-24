import HeadComplexity.Results.JointCellFilteredKernels
import HeadComplexity.Results.JointFamilyScalarCapacity
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

set_option linter.style.header false

/-!
Equal steps collapse a mixed reciprocal filter to only `card + 1` poles.
The number of formal subsets in the filter is therefore not a valid count
of independent scalar oscillations in this symmetric specialization.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

/-- With constant steps, all subsets of a given size have the same pole.
This identity is algebraic, so it also holds away from the positive region. -/
theorem jointCell_filtered_kernel_equal_steps
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (w d : ℝ) :
    jointCellFilteredKernel s (fun _ ↦ w) d =
      ∑ j ∈ Finset.range (s.card + 1),
        ((-1 : ℝ) ^ s.card * (s.card.choose j : ℝ) * (-1 : ℝ) ^ j) /
          (d - (j : ℝ) * w) := by
  unfold jointCellFilteredKernel faceAlternation
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_powerset]
  have h (j : ℕ) :
      (∑ t ∈ s.powersetCard j,
        (-1 : ℝ) ^ t.card * (1 / (d - (t.card : ℝ) * w))) =
      (s.card.choose j : ℝ) *
        ((-1 : ℝ) ^ j * (1 / (d - (j : ℝ) * w))) := by
    simpa only [nsmul_eq_mul] using Finset.sum_powersetCard j s
      (fun r ↦ (-1 : ℝ) ^ r * (1 / (d - (r : ℝ) * w)))
  simp_rw [h]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The scalar word budget also holds when each bit uses different poles.
Repeated poles are allowed and only make this upper bound weaker. -/
theorem jointCell_bitwise_cauchy_word_budget
    {I : Type*} [Fintype I] [DecidableEq I] {a m : ℕ}
    (pole η : Fin a → I → ℝ) (bias : Fin a → ℝ)
    (token : Fin (m + 1) → ℝ) (htoken : StrictMono token)
    (hden : ∀ i b z, 0 < pole b z - token i)
    (hnonzero : ∀ i b, bias b + (∑ z : I, η b z / (pole b z - token i)) ≠ 0)
    (hwords : Function.Injective (fun i : Fin (m + 1) ↦
      fun b : Fin a ↦ (0 < bias b + ∑ z : I, η b z / (pole b z - token i)))) :
    m ≤ a * Fintype.card I := by
  classical
  let P (b : Fin a) : Polynomial ℝ :=
    jointFamilyCauchyPolynomial Finset.univ (pole b) (η b) (bias b)
  have heval (b : Fin a) (i : Fin (m + 1)) :
      (P b).eval (token i) = (∏ z : I, (pole b z - token i)) *
        (bias b + ∑ z : I, η b z / (pole b z - token i)) := by
    exact jointFamilyCauchyPolynomial_eval Finset.univ (pole b) (η b)
      (bias b) (token i) (fun z _ ↦ (hden i b z).ne')
  have hpos (b : Fin a) (i : Fin (m + 1)) :
      0 < ∏ z : I, (pole b z - token i) :=
    Finset.prod_pos fun z _ ↦ hden i b z
  have hpnonzero (i : Fin (m + 1)) (b : Fin a) : (P b).eval (token i) ≠ 0 := by
    rw [heval]
    exact mul_ne_zero (hpos b i).ne' (hnonzero i b)
  have hpwords : Function.Injective (fun i : Fin (m + 1) ↦
      fun b : Fin a ↦ (0 < (P b).eval (token i))) := by
    intro i j hij
    apply hwords
    funext b
    have hb := congrFun hij b
    simpa only [heval, mul_pos_iff_of_pos_left (hpos b i),
      mul_pos_iff_of_pos_left (hpos b j)] using hb
  have hroot := jointFamily_distinct_words_total_degree_bound
    P token htoken hpnonzero hpwords
  calc
    m ≤ ∑ b : Fin a, (P b).natDegree := hroot
    _ ≤ ∑ _b : Fin a, Fintype.card I := by
      apply Finset.sum_le_sum
      intro b hb
      exact jointFamilyCauchyPolynomial_degree Finset.univ (pole b) (η b) (bias b)
    _ = a * Fintype.card I := by simp

/-- A family of `q` equal-step filters per output bit has only
`q * (c + 1)` scalar poles per bit. Thus `m + 1` distinct words require
`m ≤ a * q * (c + 1)`, even with different shifts and steps for every bit. -/
theorem jointCell_equal_step_filter_word_budget
    {a m q c : ℕ} (D w A : Fin a → Fin q → ℝ) (bias : Fin a → ℝ)
    (token : Fin (m + 1) → ℝ) (htoken : StrictMono token)
    (hden : ∀ i b h (j : Fin (c + 1)), 0 < D b h - (j : ℝ) * w b h - token i)
    (hnonzero : ∀ i b, bias b + (∑ h : Fin q, A b h *
      jointCellFilteredKernel (Finset.univ : Finset (Fin c))
        (fun _ ↦ w b h) (D b h - token i)) ≠ 0)
    (hwords : Function.Injective (fun i : Fin (m + 1) ↦ fun b : Fin a ↦
      (0 < bias b + ∑ h : Fin q, A b h *
        jointCellFilteredKernel (Finset.univ : Finset (Fin c))
          (fun _ ↦ w b h) (D b h - token i)))) :
    m ≤ a * q * (c + 1) := by
  classical
  let pole (b : Fin a) (z : Fin q × Fin (c + 1)) : ℝ :=
    D b z.1 - (z.2 : ℝ) * w b z.1
  let η (b : Fin a) (z : Fin q × Fin (c + 1)) : ℝ :=
    A b z.1 * ((-1 : ℝ) ^ c * (c.choose z.2 : ℝ) * (-1 : ℝ) ^ (z.2 : ℕ))
  have heq (b : Fin a) (t : ℝ) :
      (∑ h : Fin q, A b h *
        jointCellFilteredKernel (Finset.univ : Finset (Fin c))
          (fun _ ↦ w b h) (D b h - t)) =
      ∑ z : Fin q × Fin (c + 1), η b z / (pole b z - t) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro h hh
    rw [jointCell_filtered_kernel_equal_steps]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [pole, η]
    rw [show D b h - t - (j : ℝ) * w b h =
      D b h - (j : ℝ) * w b h - t by ring]
    ring
  have hn' (i : Fin (m + 1)) (b : Fin a) :
      bias b + ∑ z, η b z / (pole b z - token i) ≠ 0 := by
    rw [← heq]
    exact hnonzero i b
  have hw' : Function.Injective (fun i : Fin (m + 1) ↦ fun b : Fin a ↦
      (0 < bias b + ∑ z, η b z / (pole b z - token i))) := by
    simpa only [← heq] using hwords
  have hbound := jointCell_bitwise_cauchy_word_budget pole η bias token htoken
    (fun i b z ↦ hden i b z.1 z.2) hn' hw'
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_assoc] using hbound

end HeadComplexity.AxisZeroGluing
