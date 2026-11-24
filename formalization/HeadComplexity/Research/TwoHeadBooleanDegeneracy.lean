import HeadComplexity.Research.AffineBooleanZeroDivisors
import Mathlib.LinearAlgebra.Matrix.Rank

set_option linter.style.header false

/-!
A structural restriction on exact two-head Boolean cancellations.  The
dimension-four boundary and asymptotic head-count question are not asserted.
-/

noncomputable section

namespace HeadComplexity.TwoHeadBooleanDegeneracy

open Finset
open scoped BigOperators
open AffineBooleanZeroDivisors

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem cross_coefficient_relations (a₀ b₀ c₀ d₀ : ℝ) (a b c d : ι → ℝ)
    (h : ∀ s : Finset ι,
      value a₀ a s * value c₀ c s + value d₀ d s * value b₀ b s = 0) :
    a₀*c₀+d₀*b₀ = 0 ∧
    (∀ i, a₀*c i + c₀*a i + d₀*b i + b₀*d i + a i*c i+d i*b i = 0) ∧
    (∀ i j, i ≠ j → a i*c j+a j*c i+d i*b j+d j*b i = 0) := by
  have he := h ∅
  simp only [value, sum_empty, add_zero] at he
  have hs (i : ι) := h {i}
  simp only [value, sum_singleton] at hs
  refine ⟨he, ?_, ?_⟩
  · intro i
    nlinarith [hs i]
  · intro i j hij
    have hp := h {i,j}
    simp only [value, sum_insert (show i ∉ ({j} : Finset ι) by simp [hij]),
      sum_singleton] at hp
    nlinarith [hs i, hs j]

theorem diagonal_support_card_le_four (a b c d : ι → ℝ)
    (h : ∀ i j, i ≠ j → a i*c j+a j*c i+d i*b j+d j*b i = 0) :
    (univ.filter (fun i => a i*c i+d i*b i ≠ 0)).card ≤ 4 := by
  classical
  let M : Matrix ι (Fin 4) ℝ := fun i => ![a i, c i, d i, b i]
  let T : Matrix (Fin 4) ι ℝ := ![fun j => c j/2, fun j => a j/2,
    fun j => b j/2, fun j => d j/2]
  have heq : M*T = Matrix.diagonal (fun i => a i*c i+d i*b i) := by
    ext i j
    change (∑ k : Fin 4, M i k * T k j) = _
    simp only [Fin.sum_univ_succ, M, T, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Finset.univ_eq_empty,
      Finset.sum_empty, add_zero]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      ring
    · rw [Matrix.diagonal_apply_ne _ hij]
      nlinarith [h i j hij]
  have hr : (Matrix.diagonal (fun i => a i*c i+d i*b i)).rank ≤ 4 := by
    rw [← heq]
    exact (Matrix.rank_mul_le_left M T).trans (by simpa using Matrix.rank_le_card_width M)
  rw [Matrix.rank_diagonal] at hr
  simpa only [Fintype.card_subtype, Finset.mem_filter, Finset.mem_univ, true_and] using hr

theorem exists_zero_diagonal (a₀ b₀ c₀ d₀ : ℝ) (a b c d : ι → ℝ)
    (hn : 5 ≤ Fintype.card ι)
    (h : ∀ s : Finset ι,
      value a₀ a s * value c₀ c s + value d₀ d s * value b₀ b s = 0) :
    ∃ j, a j*c j+d j*b j = 0 := by
  obtain ⟨_, _, hp⟩ := cross_coefficient_relations a₀ b₀ c₀ d₀ a b c d h
  have hc := diagonal_support_card_le_four a b c d hp
  by_contra he
  push Not at he
  have hf : univ.filter (fun i => a i*c i+d i*b i ≠ 0) = (univ : Finset ι) := by
    ext i
    simp [he i]
  rw [hf, card_univ] at hc
  omega

theorem factor_at_zero_diagonal (a₀ b₀ c₀ d₀ : ℝ) (a b c d : ι → ℝ)
    (h : ∀ s : Finset ι,
      value a₀ a s * value c₀ c s + value d₀ d s * value b₀ b s = 0)
    (j : ι) (hbj : b j ≠ 0) (hj : a j*c j+d j*b j = 0) :
    let κ := a j/b j
    let ell := c j/b j
    d₀ + κ*c₀ = -ell*(a₀-κ*b₀) ∧
    (∀ i, d i+κ*c i = -ell*(a i-κ*b i)) ∧
    (∀ s : Finset ι,
      value (a₀-κ*b₀) (fun i => a i-κ*b i) s *
      value (c₀-ell*b₀) (fun i => c i-ell*b i) s = 0) := by
  dsimp only
  obtain ⟨he, hs, hp⟩ := cross_coefficient_relations a₀ b₀ c₀ d₀ a b c d h
  have hdj : d j = -(a j/b j)*c j := by
    field_simp
    nlinarith
  have hconst : d₀+(a j/b j)*c₀ = -(c j/b j)*(a₀-(a j/b j)*b₀) := by
    have ht := hs j
    rw [hdj] at ht
    field_simp
    field_simp at ht
    nlinarith
  have hcoeff (i : ι) : d i+(a j/b j)*c i = -(c j/b j)*(a i-(a j/b j)*b i) := by
    by_cases hij : i = j
    · subst i
      rw [hdj]
      field_simp
      ring
    · have ht := hp i j hij
      rw [hdj] at ht
      field_simp
      field_simp at ht
      nlinarith
  refine ⟨hconst, hcoeff, ?_⟩
  intro s
  have hu : value (a₀-(a j/b j)*b₀) (fun i => a i-(a j/b j)*b i) s =
      value a₀ a s-(a j/b j)*value b₀ b s := by
    simp only [value, sum_sub_distrib, ← mul_sum]
    ring
  have hg : value (c₀-(c j/b j)*b₀) (fun i => c i-(c j/b j)*b i) s =
      value c₀ c s-(c j/b j)*value b₀ b s := by
    simp only [value, sum_sub_distrib, ← mul_sum]
    ring
  have hv : value d₀ d s+(a j/b j)*value c₀ c s =
      -(c j/b j)*(value a₀ a s-(a j/b j)*value b₀ b s) := by
    have he0 := hconst
    have hes : (∑ i ∈ s, (d i+(a j/b j)*c i)) =
        ∑ i ∈ s, -(c j/b j)*(a i-(a j/b j)*b i) := by
      exact sum_congr rfl (fun i _ => hcoeff i)
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum] at hes
    dsimp only [value]
    nlinarith
  rw [hu, hg]
  linear_combination h s - value b₀ b s * hv

/-- A nonconstant common two-head table forces the denominators to agree,
up to a positive scalar, outside at most two input coordinates.  This is
an exact cancellation theorem, not a sign-capacity theorem. -/
theorem denominator_difference_support_le_two
    (a₀ b₀ c₀ d₀ : ℝ) (a b c d : ι → ℝ)
    (hn : 5 ≤ Fintype.card ι)
    (h : ∀ s : Finset ι,
      value a₀ a s * value c₀ c s + value d₀ d s * value b₀ b s = 0)
    (hb : ∀ s : Finset ι, 0 < value b₀ b s)
    (hc : ∀ s : Finset ι, 0 < value c₀ c s)
    (hbs : ∀ i, b i ≠ 0)
    (ha : ∀ κ : ℝ, a₀ ≠ κ*b₀ ∨ ∃ i, a i ≠ κ*b i) :
    ∃ ell : ℝ, 0 < ell ∧
      (univ.filter (fun i => c i - ell*b i ≠ 0)).card ≤ 2 := by
  obtain ⟨j, hj⟩ := exists_zero_diagonal a₀ b₀ c₀ d₀ a b c d hn h
  let κ := a j/b j
  let ell := c j/b j
  obtain ⟨_, _, hprod⟩ := factor_at_zero_diagonal a₀ b₀ c₀ d₀ a b c d
    h j (hbs j) hj
  change ∀ s : Finset ι,
    value (a₀-κ*b₀) (fun i => a i-κ*b i) s *
    value (c₀-ell*b₀) (fun i => c i-ell*b i) s = 0 at hprod
  have hF : a₀-κ*b₀ ≠ 0 ∨ ∃ i, a i-κ*b i ≠ 0 := by
    simpa only [sub_ne_zero] using ha κ
  have hs : ∃ s : Finset ι, value (a₀-κ*b₀) (fun i => a i-κ*b i) s ≠ 0 := by
    by_cases h₀ : a₀-κ*b₀ = 0
    · obtain ⟨i, hi⟩ := hF.resolve_left (not_not.mpr h₀)
      exact ⟨{i}, by simpa [value, h₀] using hi⟩
    · exact ⟨∅, by simpa [value] using h₀⟩
  obtain ⟨s, hs⟩ := hs
  have hG := (mul_eq_zero.mp (hprod s)).resolve_left hs
  have heq : value c₀ c s = ell * value b₀ b s := by
    simp only [value, sum_sub_distrib, ← mul_sum] at hG ⊢
    linarith
  have hell : 0 < ell := by
    have ht := hc s
    rw [heq] at ht
    exact (mul_pos_iff.mp ht).resolve_right (by intro hneg; linarith [hb s]) |>.1
  refine ⟨ell, hell, ?_⟩
  apply support_card_le_two (c₀-ell*b₀) (a₀-κ*b₀)
    (fun i => c i-ell*b i) (fun i => a i-κ*b i) _ hF
  intro t
  simpa only [mul_comm] using hprod t

#print axioms diagonal_support_card_le_four
#print axioms exists_zero_diagonal
#print axioms factor_at_zero_diagonal
#print axioms denominator_difference_support_le_two

end HeadComplexity.TwoHeadBooleanDegeneracy
