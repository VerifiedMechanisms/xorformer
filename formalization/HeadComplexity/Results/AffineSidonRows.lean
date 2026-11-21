import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

open scoped BigOperators

/-- The part of the Sidon property used by an affine coordinate square.
This is an auxiliary restriction on a pole set, not on attention heads. -/
def HasUniquePairSums (s : Set ℝ) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
    a + d = b + c → a = b ∨ a = c

/-- An affine row taking values in a Sidon set cannot have two active
Boolean coordinates. The finite subsets parameterize the Boolean cube. -/
theorem affine_sidon_row_pair_zero {n : ℕ} {s : Set ℝ}
    (hs : HasUniquePairSums s) (a : ℝ) (b : Fin n → ℝ)
    (hm : ∀ t : Finset (Fin n), a + ∑ i ∈ t, b i ∈ s)
    (i j : Fin n) (hij : i ≠ j) : b i = 0 ∨ b j = 0 := by
  classical
  have h0 : a ∈ s := by simpa using hm ∅
  have hi : a + b i ∈ s := by simpa using hm {i}
  have hj : a + b j ∈ s := by simpa using hm {j}
  have htwo : a + b i + b j ∈ s := by
    simpa [hij, add_assoc] using hm {i, j}
  have heq : a + (a + b i + b j) = (a + b i) + (a + b j) := by ring
  rcases hs a h0 (a + b i) hi (a + b j) hj (a + b i + b j) htwo heq with h | h
  · left
    linarith
  · right
    linarith

/-- A row of an affine permutation cube with Sidon poles is either
constant or depends on just one Boolean coordinate. -/
theorem affine_sidon_row_one_coordinate {n : ℕ} {s : Set ℝ}
    (hs : HasUniquePairSums s) (a : ℝ) (b : Fin n → ℝ)
    (hm : ∀ t : Finset (Fin n), a + ∑ i ∈ t, b i ∈ s) :
    (∀ i, b i = 0) ∨
      ∃ i, b i ≠ 0 ∧ ∀ j, j ≠ i → b j = 0 := by
  classical
  by_cases h : ∃ i, b i ≠ 0
  · obtain ⟨i, hi⟩ := h
    right
    refine ⟨i, hi, ?_⟩
    intro j hji
    rcases affine_sidon_row_pair_zero hs a b hm i j hji.symm with hz | hz
    · exact (hi hz).elim
    · exact hz
  · left
    intro i
    by_contra hi
    exact h ⟨i, hi⟩

end HeadComplexity
