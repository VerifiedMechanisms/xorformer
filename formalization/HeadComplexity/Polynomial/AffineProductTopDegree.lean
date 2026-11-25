import HeadComplexity.Polynomial.RoPEGroupSymmetrization

set_option linter.style.header false

/-! # Constants in affine factors do not change top-degree coefficients -/

namespace HeadComplexity.AffineProductTopDegree

open MvPolynomial
open scoped BigOperators

variable {σ ι : Type*}

theorem prod_degree_le_card (s : Finset ι) (p : ι → MvPolynomial σ ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ 1) :
    (∏ i ∈ s, p i).totalDegree ≤ s.card := by
  apply (totalDegree_finsetProd _ _).trans
  calc
    (∑ i ∈ s, (p i).totalDegree) ≤ ∑ _i ∈ s, 1 := Finset.sum_le_sum (fun i _ ↦ hp i)
    _ = s.card := by simp

/-- Removing constants from affine factors changes only smaller degrees. -/
theorem prod_shift_sub_degree (s : Finset ι) (c : ι → ℝ)
    (p : ι → MvPolynomial σ ℝ) (hp : ∀ i, (p i).totalDegree ≤ 1) :
    ((∏ i ∈ s, (C (c i) + p i)) - ∏ i ∈ s, p i).totalDegree ≤ s.card - 1 := by
  classical
  have hshift (i : ι) : (C (c i) + p i).totalDegree ≤ 1 :=
    (totalDegree_add _ _).trans (max_le (by simp) (hp i))
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    by_cases hs : s = ∅
    · subst s
      simp
    · have hcard : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
      have he : (C (c i) + p i) * (∏ j ∈ s, (C (c j) + p j)) -
          p i * ∏ j ∈ s, p j =
          C (c i) * (∏ j ∈ s, (C (c j) + p j)) +
            p i * ((∏ j ∈ s, (C (c j) + p j)) - ∏ j ∈ s, p j) := by ring
      rw [he]
      apply (totalDegree_add _ _).trans
      apply max_le
      · exact (totalDegree_mul _ _).trans (by
          simpa using prod_degree_le_card s (fun j ↦ C (c j) + p j) hshift)
      · have hb := (totalDegree_mul (p i) _).trans (Nat.add_le_add (hp i) ih)
        omega

/-- A sum with one numerator and H-1 affine denominators has the same top
coefficients after removing all denominator constants. -/
theorem numerator_products_shift_sub_degree {H : ℕ} (hH : 2 ≤ H)
    (c : Fin H → ℝ) (N D : Fin H → MvPolynomial σ ℝ)
    (hN : ∀ i, (N i).totalDegree ≤ 1) (hD : ∀ i, (D i).totalDegree ≤ 1) :
    ((∑ i, N i * ∏ j ∈ Finset.univ.erase i, (C (c j) + D j)) -
      ∑ i, N i * ∏ j ∈ Finset.univ.erase i, D j).totalDegree ≤ H - 1 := by
  classical
  rw [← Finset.sum_sub_distrib]
  apply totalDegree_finsetSum_le
  intro i _
  rw [← mul_sub]
  have hb := (totalDegree_mul (N i) _).trans
    (Nat.add_le_add (hN i) (prod_shift_sub_degree (Finset.univ.erase i) c D hD))
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin] at hb
  omega

end HeadComplexity.AffineProductTopDegree
