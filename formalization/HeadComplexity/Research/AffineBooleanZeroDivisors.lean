import Mathlib.Tactic

set_option linter.style.header false

/-!
Affine zero divisors in the Boolean table algebra.  These are auxiliary
structural lemmas for the two-head cancellation classification.  They do not
bound the number of heads in an arbitrary sign representation.
-/

noncomputable section

namespace HeadComplexity.AffineBooleanZeroDivisors

open Finset
open scoped BigOperators

variable {ι : Type*}

def value (a₀ : ℝ) (a : ι → ℝ) (s : Finset ι) : ℝ := a₀ + ∑ i ∈ s, a i

theorem coefficient_relations (a₀ b₀ : ℝ) (a b : ι → ℝ)
    (h : ∀ s : Finset ι, value a₀ a s * value b₀ b s = 0) :
    a₀*b₀ = 0 ∧
    (∀ i, a₀*b i + b₀*a i + a i*b i = 0) ∧
    (∀ i j, i ≠ j → a i*b j + a j*b i = 0) := by
  classical
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

theorem three_nonzero_slopes_force_zero (a₀ b₀ : ℝ) (a b : ι → ℝ)
    (h : ∀ s : Finset ι, value a₀ a s * value b₀ b s = 0)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hai : a i ≠ 0) (haj : a j ≠ 0) (hak : a k ≠ 0) :
    b₀ = 0 ∧ ∀ l, b l = 0 := by
  obtain ⟨he, hs, hp⟩ := coefficient_relations a₀ b₀ a b h
  have hij' := hp i j hij
  have hik' := hp i k hik
  have hjk' := hp j k hjk
  have hbi : b i = 0 := by
    have hz : 2 * a j * a k * b i = 0 := by
      linear_combination a k * hij' + a j * hik' - a i * hjk'
    rcases mul_eq_zero.mp hz with hleft | hright
    · exact False.elim ((mul_ne_zero (mul_ne_zero (by norm_num) haj) hak) hleft)
    · exact hright
  have hb (l : ι) : b l = 0 := by
    by_cases hli : l = i
    · simpa [hli] using hbi
    · have hl := hp i l (Ne.symm hli)
      rw [hbi, mul_zero, add_zero] at hl
      exact (mul_eq_zero.mp hl).resolve_left hai
  have hb₀ : b₀ = 0 := by
    have ht := hs i
    simp only [hbi, mul_zero, add_zero, zero_add] at ht
    exact (mul_eq_zero.mp ht).resolve_right hai
  exact ⟨hb₀, hb⟩

theorem support_card_le_two [Fintype ι] (a₀ b₀ : ℝ) (a b : ι → ℝ)
    (h : ∀ s : Finset ι, value a₀ a s * value b₀ b s = 0)
    (hb : b₀ ≠ 0 ∨ ∃ i, b i ≠ 0) :
    (univ.filter (fun i => a i ≠ 0)).card ≤ 2 := by
  by_contra hc
  have hc' : 2 < (univ.filter (fun i => a i ≠ 0)).card := Nat.lt_of_not_ge hc
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.mp hc'
  have hz := three_nonzero_slopes_force_zero a₀ b₀ a b h i j k hij hik hjk
    (mem_filter.mp hi).2 (mem_filter.mp hj).2 (mem_filter.mp hk).2
  rcases hb with hb₀ | ⟨l, hl⟩
  · exact hb₀ hz.1
  · exact hl (hz.2 l)

theorem exists_nonzero_slope (a₀ b₀ : ℝ) (a b : ι → ℝ)
    (h : ∀ s : Finset ι, value a₀ a s * value b₀ b s = 0)
    (ha : a₀ ≠ 0 ∨ ∃ i, a i ≠ 0) (hb : b₀ ≠ 0 ∨ ∃ i, b i ≠ 0) :
    ∃ i, a i ≠ 0 := by
  by_contra hn
  push Not at hn
  have ha₀ : a₀ ≠ 0 := ha.resolve_right (by simpa using hn)
  obtain ⟨he, hs, _⟩ := coefficient_relations a₀ b₀ a b h
  have hb₀ : b₀ = 0 := (mul_eq_zero.mp he).resolve_left ha₀
  have hz (i : ι) : b i = 0 := by
    have ht := hs i
    simp only [hn i, mul_zero, zero_mul, add_zero] at ht
    exact (mul_eq_zero.mp ht).resolve_left ha₀
  rcases hb with h₀ | ⟨i, hi⟩
  · exact h₀ hb₀
  · exact hi (hz i)

theorem two_slope_classification (a₀ b₀ : ℝ) (a b : ι → ℝ)
    (h : ∀ s : Finset ι, value a₀ a s * value b₀ b s = 0)
    (hb : b₀ ≠ 0 ∨ ∃ i, b i ≠ 0)
    (i j : ι) (hij : i ≠ j) (hai : a i ≠ 0) (haj : a j ≠ 0) :
    (∀ l, l ≠ i → l ≠ j → a l = 0 ∧ b l = 0) ∧
    ((a₀ = 0 ∧ a i + a j = 0 ∧ b₀ ≠ 0 ∧ b i = -b₀ ∧ b j = -b₀) ∨
     (b₀ = 0 ∧ b i + b j = 0 ∧ a₀ ≠ 0 ∧ a i = -a₀ ∧ a j = -a₀)) := by
  obtain ⟨he, hs, hp⟩ := coefficient_relations a₀ b₀ a b h
  have hout (l : ι) (hli : l ≠ i) (hlj : l ≠ j) : a l = 0 ∧ b l = 0 := by
    have hal : a l = 0 := by
      by_contra hal
      have hz := three_nonzero_slopes_force_zero a₀ b₀ a b h i j l hij
        (Ne.symm hli) (Ne.symm hlj) hai haj hal
      rcases hb with h₀ | ⟨k, hk⟩
      · exact h₀ hz.1
      · exact hk (hz.2 k)
    have ht := hp i l (Ne.symm hli)
    rw [hal, zero_mul, add_zero] at ht
    exact ⟨hal, (mul_eq_zero.mp ht).resolve_left hai⟩
  refine ⟨hout, ?_⟩
  have hnonzero : b₀ ≠ 0 ∨ b i ≠ 0 ∨ b j ≠ 0 := by
    rcases hb with h₀ | ⟨l, hl⟩
    · exact Or.inl h₀
    · by_cases hli : l = i
      · exact Or.inr (Or.inl (hli ▸ hl))
      · by_cases hlj : l = j
        · exact Or.inr (Or.inr (hlj ▸ hl))
        · exact False.elim (hl (hout l hli hlj).2)
  by_cases ha₀ : a₀ = 0
  · simp only [ha₀, zero_mul, zero_add] at hs
    have hbi : b i = -b₀ := by
      have ht : a i * (b₀+b i) = 0 := by nlinarith [hs i]
      have hz := (mul_eq_zero.mp ht).resolve_left hai
      linarith
    have hbj : b j = -b₀ := by
      have ht : a j * (b₀+b j) = 0 := by nlinarith [hs j]
      have hz := (mul_eq_zero.mp ht).resolve_left haj
      linarith
    have hb₀ : b₀ ≠ 0 := by
      intro hz
      simp [hz, hbi, hbj] at hnonzero
    have hpij := hp i j hij
    rw [hbi, hbj] at hpij
    have ht : (a i+a j)*b₀ = 0 := by nlinarith
    exact Or.inl ⟨ha₀, (mul_eq_zero.mp ht).resolve_right hb₀, hb₀, hbi, hbj⟩
  · have hb₀ : b₀ = 0 := (mul_eq_zero.mp he).resolve_left ha₀
    simp only [hb₀, zero_mul, add_zero] at hs
    have hbi : b i ≠ 0 := by
      intro hz
      have ht := hp i j hij
      rw [hz, mul_zero, add_zero] at ht
      have hbj := (mul_eq_zero.mp ht).resolve_left hai
      simp [hb₀, hz, hbj] at hnonzero
    have hbj : b j ≠ 0 := by
      intro hz
      have ht := hp i j hij
      rw [hz, mul_zero, zero_add] at ht
      exact (mul_ne_zero haj hbi) ht
    have hai' : a i = -a₀ := by
      have ht : (a₀+a i)*b i = 0 := by nlinarith [hs i]
      have hz := (mul_eq_zero.mp ht).resolve_right hbi
      linarith
    have haj' : a j = -a₀ := by
      have ht : (a₀+a j)*b j = 0 := by nlinarith [hs j]
      have hz := (mul_eq_zero.mp ht).resolve_right hbj
      linarith
    have hpij := hp i j hij
    rw [hai', haj'] at hpij
    have ht : a₀*(b i+b j) = 0 := by nlinarith
    exact Or.inr ⟨hb₀, (mul_eq_zero.mp ht).resolve_left ha₀, ha₀, hai', haj'⟩

theorem one_slope_classification (a₀ b₀ : ℝ) (a b : ι → ℝ)
    (h : ∀ s : Finset ι, value a₀ a s * value b₀ b s = 0)
    (hb : b₀ ≠ 0 ∨ ∃ i, b i ≠ 0)
    (i : ι) (hai : a i ≠ 0) (haout : ∀ l, l ≠ i → a l = 0) :
    (∀ l, l ≠ i → b l = 0) ∧
    ((a₀ = 0 ∧ b₀ ≠ 0 ∧ b i = -b₀) ∨
     (b₀ = 0 ∧ a₀ ≠ 0 ∧ a i = -a₀ ∧ b i ≠ 0)) := by
  obtain ⟨he, hs, hp⟩ := coefficient_relations a₀ b₀ a b h
  have hbout (l : ι) (hli : l ≠ i) : b l = 0 := by
    have ht := hp i l (Ne.symm hli)
    rw [haout l hli, zero_mul, add_zero] at ht
    exact (mul_eq_zero.mp ht).resolve_left hai
  have hnonzero : b₀ ≠ 0 ∨ b i ≠ 0 := by
    rcases hb with h₀ | ⟨l, hl⟩
    · exact Or.inl h₀
    · by_cases hli : l = i
      · exact Or.inr (hli ▸ hl)
      · exact False.elim (hl (hbout l hli))
  refine ⟨hbout, ?_⟩
  by_cases ha₀ : a₀ = 0
  · simp only [ha₀, zero_mul, zero_add] at hs
    have ht : a i*(b₀+b i) = 0 := by nlinarith [hs i]
    have hbi : b i = -b₀ := by
      have hz := (mul_eq_zero.mp ht).resolve_left hai
      linarith
    have hb₀ : b₀ ≠ 0 := by
      intro hz
      simp [hz, hbi] at hnonzero
    exact Or.inl ⟨ha₀, hb₀, hbi⟩
  · have hb₀ : b₀ = 0 := (mul_eq_zero.mp he).resolve_left ha₀
    simp only [hb₀, zero_mul, add_zero] at hs
    have hbi : b i ≠ 0 := hnonzero.resolve_left (not_not.mpr hb₀)
    have ht : (a₀+a i)*b i = 0 := by nlinarith [hs i]
    have hai' : a i = -a₀ := by
      have hz := (mul_eq_zero.mp ht).resolve_right hbi
      linarith
    exact Or.inr ⟨hb₀, ha₀, hai', hbi⟩

#print axioms coefficient_relations
#print axioms three_nonzero_slopes_force_zero
#print axioms support_card_le_two
#print axioms two_slope_classification
#print axioms one_slope_classification

end HeadComplexity.AffineBooleanZeroDivisors
