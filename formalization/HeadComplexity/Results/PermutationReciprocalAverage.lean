import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

open Finset
open scoped BigOperators

private theorem swap_preserves_finset {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (i j : ι) (hi : i ∈ A) (hj : j ∈ A) :
    ∀ a, a ∈ A ↔ Equiv.swap i j a ∈ A := by
  intro a
  by_cases hai : a = i
  · subst a
    simp [hi, hj]
  by_cases haj : a = j
  · subst a
    simp [hi, hj]
  simp [Equiv.swap_apply_of_ne_of_ne hai haj]

/-- Averaging a coordinate-to-subset ratio over all permutations gives the
same sum for each coordinate of the subset. -/
theorem permutation_reciprocal_ratio_sums_eq {ι : Type*} [Fintype ι]
    [DecidableEq ι] (v : ι → ℝ) (A : Finset ι) (i j : ι)
    (hi : i ∈ A) (hj : j ∈ A) :
    (∑ σ : Equiv.Perm ι, v (σ i) / ∑ a ∈ A, v (σ a)) =
      ∑ σ : Equiv.Perm ι, v (σ j) / ∑ a ∈ A, v (σ a) := by
  have hden (σ : Equiv.Perm ι) :
      (∑ a ∈ A, v ((σ * Equiv.swap i j) a)) = ∑ a ∈ A, v (σ a) := by
    apply Finset.sum_equiv (Equiv.swap i j) (swap_preserves_finset A i j hi hj)
    intro a ha
    simp only [Equiv.Perm.mul_apply]
  calc
    (∑ σ : Equiv.Perm ι, v (σ i) / ∑ a ∈ A, v (σ a)) =
        ∑ σ : Equiv.Perm ι, v ((σ * Equiv.swap i j) i) /
          ∑ a ∈ A, v ((σ * Equiv.swap i j) a) := by
      exact (Equiv.sum_comp (Equiv.mulRight (Equiv.swap i j))
        (fun σ : Equiv.Perm ι ↦ v (σ i) / ∑ a ∈ A, v (σ a))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [hden]
      simp

/-- The exact permutation-average identity underlying a finite-population
reciprocal identity. Positivity ensures the subset denominators are nonzero.
This theorem does not assert a sparse permutation family or a head bound. -/
theorem permutation_reciprocal_ratio_sum {ι : Type*} [Fintype ι]
    [DecidableEq ι] (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (A : Finset ι) (i : ι) (hi : i ∈ A) :
    (A.card : ℝ) * (∑ σ : Equiv.Perm ι, v (σ i) / ∑ a ∈ A, v (σ a)) =
      Fintype.card (Equiv.Perm ι) := by
  have hpos (σ : Equiv.Perm ι) : 0 < ∑ a ∈ A, v (σ a) :=
    Finset.sum_pos (fun a ha ↦ hv (σ a)) ⟨i, hi⟩
  calc
    (A.card : ℝ) * (∑ σ : Equiv.Perm ι, v (σ i) / ∑ a ∈ A, v (σ a)) =
        ∑ j ∈ A, ∑ σ : Equiv.Perm ι, v (σ j) / ∑ a ∈ A, v (σ a) := by
      calc
        _ = ∑ j ∈ A, ∑ σ : Equiv.Perm ι, v (σ i) / ∑ a ∈ A, v (σ a) := by simp
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          exact permutation_reciprocal_ratio_sums_eq v A i j hi hj
    _ = ∑ σ : Equiv.Perm ι, ∑ j ∈ A, v (σ j) / ∑ a ∈ A, v (σ a) := by
      rw [Finset.sum_comm]
    _ = ∑ σ : Equiv.Perm ι, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [← Finset.sum_div, div_self (hpos σ).ne']
    _ = _ := by simp

end HeadComplexity
