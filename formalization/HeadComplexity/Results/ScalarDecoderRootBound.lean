import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

set_option linter.style.header false

/-!
# A root-count obstruction for scalar lookup decoders

These results concern a one-dimensional code parameter, not the full Boolean
head model. Clearing positive affine denominators gives one polynomial per
output bit. Distinct successive strict sign words require a root in every
gap between their code parameters.
-/

namespace HeadComplexity

open scoped BigOperators

theorem polynomial_root_between_opposite_signs
    (p : Polynomial ℝ) (a b : ℝ) (hab : a < b)
    (h : p.eval a * p.eval b < 0) :
    ∃ z : ℝ, a < z ∧ z < b ∧ p.eval z = 0 := by
  rcases mul_neg_iff.mp h with h | h
  · obtain ⟨z, hz, he⟩ :=
      intermediate_value_Ioo' hab.le p.continuousOn ⟨h.2, h.1⟩
    exact ⟨z, hz.1, hz.2, he⟩
  · obtain ⟨z, hz, he⟩ :=
      intermediate_value_Ioo hab.le p.continuousOn ⟨h.1, h.2⟩
    exact ⟨z, hz.1, hz.2, he⟩

theorem polynomial_sign_sequence_degree_bound
    {r m : ℕ} (p : Fin r → Polynomial ℝ)
    (hp : ∀ j, p j ≠ 0) (t : Fin (m+1) → ℝ) (ht : StrictMono t)
    (hchange : ∀ i : Fin m, ∃ j : Fin r,
      (p j).eval (t i.castSucc) * (p j).eval (t i.succ) < 0) :
    m ≤ ∑ j, (p j).natDegree := by
  classical
  let P : Polynomial ℝ := ∏ j, p j
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hp j)
  have hroot (i : Fin m) : ∃ z : ℝ,
      t i.castSucc < z ∧ z < t i.succ ∧ P.eval z = 0 := by
    obtain ⟨j, hj⟩ := hchange i
    have hi : i.castSucc < i.succ := by simp
    obtain ⟨z, h₁, h₂, h₃⟩ :=
      polynomial_root_between_opposite_signs (p j) _ _ (ht hi) hj
    refine ⟨z, h₁, h₂, ?_⟩
    simp only [P, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) h₃
  choose z hz₁ hz₂ hz₀ using hroot
  have hz : StrictMono z := by
    intro i j hij
    have hs : i.succ ≤ j.castSucc := by
      exact Fin.le_iff_val_le_val.mpr (by simpa using hij)
    exact (hz₂ i).trans_le ((ht.monotone hs).trans (hz₁ j).le)
  have hm : m ≤ P.natDegree := by
    by_contra h
    have he := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      P hz.injective hz₀ (by simpa using Nat.lt_of_not_ge h)
    exact hP he
  exact hm.trans (Polynomial.natDegree_prod_le Finset.univ p)

theorem scalar_decoder_degree_budget
    {r m H : ℕ} (p : Fin r → Polynomial ℝ)
    (hp : ∀ j, p j ≠ 0) (hdegree : ∀ j, (p j).natDegree ≤ H)
    (t : Fin (m+1) → ℝ) (ht : StrictMono t)
    (hchange : ∀ i : Fin m, ∃ j : Fin r,
      (p j).eval (t i.castSucc) * (p j).eval (t i.succ) < 0) :
    m ≤ r*H := by
  calc
    m ≤ ∑ j, (p j).natDegree :=
      polynomial_sign_sequence_degree_bound p hp t ht hchange
    _ ≤ ∑ _j : Fin r, H := Finset.sum_le_sum (fun j _ => hdegree j)
    _ = r*H := by simp

theorem scalar_decoder_distinct_sign_words_bound
    {r m H : ℕ} (p : Fin r → Polynomial ℝ)
    (hdegree : ∀ j, (p j).natDegree ≤ H)
    (t : Fin (m+1) → ℝ) (ht : StrictMono t)
    (hnonzero : ∀ i j, (p j).eval (t i) ≠ 0)
    (hwords : Function.Injective (fun i : Fin (m+1) =>
      fun j : Fin r => (0 < (p j).eval (t i)))) :
    m ≤ r*H := by
  classical
  have hp (j : Fin r) : p j ≠ 0 := by
    intro he
    simpa [he] using hnonzero 0 j
  apply scalar_decoder_degree_budget p hp hdegree t ht
  intro i
  by_contra hc
  push Not at hc
  have he : (fun j : Fin r => 0 < (p j).eval (t i.castSucc)) =
      (fun j : Fin r => 0 < (p j).eval (t i.succ)) := by
    funext j
    apply propext
    have hprod := hc j
    have ha := hnonzero i.castSucc j
    have hb := hnonzero i.succ j
    constructor
    · intro h
      by_contra h'
      have hn : (p j).eval (t i.succ) < 0 := lt_of_le_of_ne (le_of_not_gt h') hb
      exact (not_lt_of_ge hprod) (mul_neg_of_pos_of_neg h hn)
    · intro h
      by_contra h'
      have hn : (p j).eval (t i.castSucc) < 0 := lt_of_le_of_ne (le_of_not_gt h') ha
      exact (not_lt_of_ge hprod) (mul_neg_of_neg_of_pos hn h)
  have hi := hwords he
  have : i.castSucc < i.succ := by simp
  exact (ne_of_lt this) hi

theorem scalar_decoder_all_words_lower_bound
    {r m H : ℕ} (p : Fin r → Polynomial ℝ)
    (hdegree : ∀ j, (p j).natDegree ≤ H)
    (t : Fin (m+1) → ℝ) (ht : StrictMono t)
    (hnonzero : ∀ i j, (p j).eval (t i) ≠ 0)
    (hwords : Function.Injective (fun i : Fin (m+1) =>
      fun j : Fin r => (0 < (p j).eval (t i))))
    (hcard : m+1 = 2^r) :
    2^r ≤ r*H+1 := by
  have := scalar_decoder_distinct_sign_words_bound p hdegree t ht hnonzero hwords
  omega

end HeadComplexity
