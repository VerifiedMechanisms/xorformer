import HeadComplexity.Atoms.ReciprocalOscillation
import Mathlib.SetTheory.Cardinal.Finite

set_option linter.style.header false

/-!
# Many positive zeros of a linear functional on reciprocal evaluations

A nonnegative rational function with prescribed double zeros gives a Cartesian
grid of isolated zeros after summing over independent denominator coordinates.
These are zeros of a linear functional of score evaluations, not sign patterns
of the scores themselves. No head-complexity lower bound is asserted.
-/

namespace HeadComplexity.PositiveFunctionalGrid

open Finset Polynomial
open scoped BigOperators

theorem exists_nonnegative_reciprocal_with_zeros {q : ℕ}
    (a : Fin (q + q + 1) → ℝ) (ha : Function.Injective a)
    (ha_nonneg : ∀ j, 0 ≤ a j) (r : Fin q → ℝ) :
    ∃ b : Fin (q + q + 1) → ℝ, ∀ t : ℝ, 0 < t →
      0 ≤ ∑ j, b j / (t + a j) ∧
      ((∑ j, b j / (t + a j)) = 0 ↔ ∃ i, t = r i) := by
  classical
  obtain ⟨b, hb⟩ := exists_reciprocal_prescribed_roots_identity
    a ha ha_nonneg (Fin.append r r)
  refine ⟨b, fun t ht ↦ ?_⟩
  have hprod : (∏ i : Fin (q + q), (t - Fin.append r r i)) =
      (∏ i : Fin q, (t - r i)) ^ 2 := by
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right, pow_two]
  have hden : 0 < ∏ j, (t + a j) := by
    apply Finset.prod_pos
    intro j _
    exact add_pos_of_pos_of_nonneg ht (ha_nonneg j)
  rw [hb t ht, hprod]
  constructor
  · exact div_nonneg (sq_nonneg _) hden.le
  · simp [div_eq_zero_iff, hden.ne', Finset.prod_eq_zero_iff, sub_eq_zero]

theorem sum_reciprocal_zero_iff {q : ℕ} {ι : Type*} [Fintype ι]
    (a b : Fin (q + q + 1) → ℝ) (r : Fin q → ℝ)
    (hb : ∀ t : ℝ, 0 < t →
      0 ≤ ∑ j, b j / (t + a j) ∧
      ((∑ j, b j / (t + a j)) = 0 ↔ ∃ i, t = r i))
    (t : ι → ℝ) (ht : ∀ i, 0 < t i) :
    (∑ i, ∑ j, b j / (t i + a j)) = 0 ↔ ∀ i, ∃ j, t i = r j := by
  classical
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ (hb (t i) (ht i)).1)]
  simp only [Finset.mem_univ, forall_true_left]
  exact forall_congr' fun i ↦ (hb (t i) (ht i)).2

/-- The positive zero set is exactly a finite Cartesian grid. -/
theorem exists_positive_zero_grid_equiv {q : ℕ} {ι : Type*} [Fintype ι]
    (a : Fin (q + q + 1) → ℝ) (ha : Function.Injective a)
    (ha_nonneg : ∀ j, 0 ≤ a j) (r : Fin q → ℝ)
    (hr : Function.Injective r) (hr_pos : ∀ j, 0 < r j) :
    ∃ b : Fin (q + q + 1) → ℝ,
      Nonempty ((ι → Fin q) ≃
        {t : ι → ℝ // (∀ i, 0 < t i) ∧
          (∑ i, ∑ j, b j / (t i + a j)) = 0}) := by
  classical
  obtain ⟨b, hb⟩ := exists_nonnegative_reciprocal_with_zeros a ha ha_nonneg r
  let F : (ι → Fin q) →
      {t : ι → ℝ // (∀ i, 0 < t i) ∧
        (∑ i, ∑ j, b j / (t i + a j)) = 0} := fun s ↦
    ⟨fun i ↦ r (s i), fun i ↦ hr_pos (s i),
      (sum_reciprocal_zero_iff a b r hb _ (fun i ↦ hr_pos (s i))).mpr
        (fun i ↦ ⟨s i, rfl⟩)⟩
  have hF : Function.Bijective F := by
    constructor
    · intro s t h
      funext i
      apply hr
      exact congrFun (congrArg Subtype.val h) i
    · intro t
      have hex := (sum_reciprocal_zero_iff a b r hb t.val t.property.1).mp t.property.2
      choose s hs using hex
      refine ⟨s, ?_⟩
      apply Subtype.ext
      funext i
      exact (hs i).symm
  exact ⟨b, ⟨Equiv.ofBijective F hF⟩⟩

/-- In `H*k` free positive coordinates there are exactly `q^(H*k)` zeros.
The equation is a linear functional of the reciprocal evaluation vector. -/
theorem exists_positive_zero_grid_card (q H k : ℕ) :
    ∃ b : Fin (q + q + 1) → ℝ,
      Nat.card {t : Fin H × Fin k → ℝ // (∀ i, 0 < t i) ∧
        (∑ i, ∑ j, b j / (t i + ((j : ℕ) : ℝ) + 1)) = 0} = q ^ (H * k) := by
  let a : Fin (q + q + 1) → ℝ := fun j ↦ ((j : ℕ) : ℝ) + 1
  let r : Fin q → ℝ := fun j ↦ ((j : ℕ) : ℝ) + 1
  have ha : Function.Injective a := by
    intro i j h
    apply Fin.ext
    dsimp [a] at h
    exact_mod_cast add_right_cancel h
  have hr : Function.Injective r := by
    intro i j h
    apply Fin.ext
    dsimp [r] at h
    exact_mod_cast add_right_cancel h
  obtain ⟨b, ⟨e⟩⟩ := exists_positive_zero_grid_equiv (ι := Fin H × Fin k)
    a ha (fun j ↦ by dsimp [a]; positivity) r hr
      (fun j ↦ by dsimp [r]; positivity)
  refine ⟨b, ?_⟩
  have hc := Nat.card_congr e
  simpa [a, Nat.card_eq_fintype_card, Fintype.card_fun, add_assoc] using hc.symm

end HeadComplexity.PositiveFunctionalGrid
