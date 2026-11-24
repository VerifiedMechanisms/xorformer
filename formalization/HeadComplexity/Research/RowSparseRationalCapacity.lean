import HeadComplexity.Results.WarrenBound
import Mathlib.Data.Set.Card.Arithmetic

set_option linter.style.header false
set_option linter.unusedDecidableInType false

/-!
Finite margin-free capacity when a prescribed routing uses few rational heads
on each query row. No unrestricted routing or localization theorem is assumed.
-/
noncomputable section
namespace HeadComplexity.RowSparseRationalCapacity
open Finset MvPolynomial
open scoped BigOperators

variable {I J K : Type} [DecidableEq J]

def score (R : I → Finset J) (A B : J → I → MvPolynomial K ℝ)
    (C : I → MvPolynomial K ℝ) (θ : K → ℝ) (x : I) : ℝ :=
  eval θ (C x) + ∑ h ∈ R x, eval θ (A h x) / eval θ (B h x)

def cleared (R : I → Finset J) (A B : J → I → MvPolynomial K ℝ)
    (C : I → MvPolynomial K ℝ) (x : I) : MvPolynomial K ℝ :=
  C x * ∏ h ∈ R x, B h x +
    ∑ h ∈ R x, A h x * ∏ g ∈ (R x).erase h, B g x

omit [DecidableEq J] in
private theorem prod_degree (s : Finset J) (P : J → MvPolynomial K ℝ)
    (hP : ∀ h ∈ s, (P h).totalDegree ≤ 1) :
    (∏ h ∈ s, P h).totalDegree ≤ s.card := by
  refine (totalDegree_finsetProd _ _).trans ?_
  simpa using sum_le_card_nsmul s (fun h => (P h).totalDegree) 1 hP

theorem cleared_degree (R : I → Finset J) (A B : J → I → MvPolynomial K ℝ)
    (C : I → MvPolynomial K ℝ)
    (hA : ∀ h x, (A h x).totalDegree ≤ 1)
    (hB : ∀ h x, (B h x).totalDegree ≤ 1)
    (hC : ∀ x, (C x).totalDegree ≤ 1) (x : I) :
    (cleared R A B C x).totalDegree ≤ (R x).card + 1 := by
  unfold cleared
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    have hp := prod_degree (R x) (fun h => B h x) (fun h _ => hB h x)
    have hc := hC x
    omega
  · apply totalDegree_finsetSum_le
    intro h hh
    refine (totalDegree_mul _ _).trans ?_
    have hp := prod_degree ((R x).erase h) (fun g => B g x) (fun g _ => hB g x)
    have hc := card_le_card (erase_subset h (R x))
    have ha := hA h x
    omega

theorem eval_cleared (R : I → Finset J) (A B : J → I → MvPolynomial K ℝ)
    (C : I → MvPolynomial K ℝ) (θ : K → ℝ) (x : I)
    (hB : ∀ h ∈ R x, eval θ (B h x) ≠ 0) :
    eval θ (cleared R A B C x) =
      (∏ h ∈ R x, eval θ (B h x)) * score R A B C θ x := by
  simp only [cleared, score, map_add, map_mul, map_prod, map_sum]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply sum_congr rfl
    intro h hh
    rw [← mul_prod_erase (R x) (fun g => eval θ (B g x)) hh]
    field_simp [hB h hh]

def represented (R : I → Finset J) (A B : J → I → MvPolynomial K ℝ)
    (C : I → MvPolynomial K ℝ) : Set (I → Bool) :=
  {f | ∃ θ : K → ℝ, (∀ x h, h ∈ R x → 0 < eval θ (B h x)) ∧
    ∀ x, if f x then 0 < score R A B C θ x else score R A B C θ x < 0}

theorem represented_subset_patterns (R : I → Finset J)
    (A B : J → I → MvPolynomial K ℝ) (C : I → MvPolynomial K ℝ) :
    represented R A B C ⊆ strictPolynomialSignPatterns (cleared R A B C) := by
  rintro f ⟨θ,hB,hf⟩
  refine ⟨θ,fun x => ?_⟩
  rw [eval_cleared R A B C θ x (fun h hh => (hB x h hh).ne')]
  have hp : 0 < ∏ h ∈ R x, eval θ (B h x) := prod_pos (fun h hh => hB x h hh)
  have hx := hf x
  cases hf' : f x <;> simp only [hf', Bool.false_eq_true, ↓reduceIte] at hx ⊢
  · exact mul_neg_of_pos_of_neg hp hx
  · exact mul_pos hp hx

variable [Fintype I] [Fintype K]

/-- A fixed routing with at most `k` contributors on each row pays degree `k+1`,
regardless of how many total heads exist. All real coefficients and signed
cancellation among the routed heads remain unrestricted. -/
theorem card_represented_le (R : I → Finset J)
    (A B : J → I → MvPolynomial K ℝ) (C : I → MvPolynomial K ℝ) {k : ℕ}
    (hR : ∀ x, (R x).card ≤ k)
    (hA : ∀ h x, (A h x).totalDegree ≤ 1)
    (hB : ∀ h x, (B h x).totalDegree ≤ 1)
    (hC : ∀ x, (C x).totalDegree ≤ 1)
    (hK : 0 < Fintype.card K) (hm : Fintype.card K ≤ Fintype.card I) :
    ((represented R A B C).ncard : ℝ) ≤
      (4 * Real.exp 1 * (k+1 : ℕ) * Fintype.card I / Fintype.card K) ^ Fintype.card K := by
  have hs : ((represented R A B C).ncard : ℝ) ≤
      ((strictPolynomialSignPatterns (cleared R A B C)).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard (represented_subset_patterns R A B C) (Set.toFinite _)
  refine hs.trans ?_
  exact warrenStrictSignPatternBound (Fintype.card I) (k+1) (Fintype.card K)
    (Nat.succ_pos _) hK hm I K (cleared R A B C) rfl rfl
    (fun x => (cleared_degree R A B C hA hB hC x).trans (Nat.add_le_add_right (hR x) 1))

/-- A finite codebook of routings contributes its actual cardinality as an
additional multiplicative factor. The codebook must be justified separately. -/
theorem card_routing_union_le {T : Type} [Fintype T]
    (R : T → I → Finset J) (A B : J → I → MvPolynomial K ℝ)
    (C : I → MvPolynomial K ℝ) {k : ℕ}
    (hR : ∀ t x, (R t x).card ≤ k)
    (hA : ∀ h x, (A h x).totalDegree ≤ 1)
    (hB : ∀ h x, (B h x).totalDegree ≤ 1)
    (hC : ∀ x, (C x).totalDegree ≤ 1)
    (hK : 0 < Fintype.card K) (hm : Fintype.card K ≤ Fintype.card I) :
    (((⋃ t, represented (R t) A B C).ncard : ℕ) : ℝ) ≤
      Fintype.card T *
      (4 * Real.exp 1 * (k+1 : ℕ) * Fintype.card I / Fintype.card K) ^ Fintype.card K := by
  have hs : (((⋃ t, represented (R t) A B C).ncard : ℕ) : ℝ) ≤
      ∑ t, ((represented (R t) A B C).ncard : ℝ) := by
    exact_mod_cast Set.ncard_iUnion_le_of_fintype (fun t => represented (R t) A B C)
  refine hs.trans ((sum_le_sum (fun t _ =>
    card_represented_le (R t) A B C (hR t) hA hB hC hK hm)).trans_eq ?_)
  simp

end HeadComplexity.RowSparseRationalCapacity
