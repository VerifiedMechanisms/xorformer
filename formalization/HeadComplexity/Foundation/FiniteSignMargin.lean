import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Strict margins on a finite domain

The classifier convention uses a strict positive threshold and permits zero
scores on negative inputs. A small negative constant shift makes every score
nonzero. These lemmas record the finite quantitative margins used by rotary
head perturbations, without any limiting classifier.
-/

namespace HeadComplexity

/-- A positive real function on a finite domain has a strictly positive strict
lower bound, including when the domain is empty. -/
theorem finite_positive_lower_bound {α : Type*} [Finite α]
    (g : α → ℝ) (hg : ∀ x, 0 < g x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, δ < g x := by
  classical
  letI := Fintype.ofFinite α
  have hfin (s : Finset α) : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ s, δ < g x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨δ, hδ, hbound⟩ := ih
      refine ⟨min δ (g a / 2), lt_min hδ (div_pos (hg a) (by norm_num)), ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (min_le_right _ _).trans_lt (by linarith [hg x])
      · exact (min_le_left _ _).trans_lt (hbound x hx)
  obtain ⟨δ, hδ, hbound⟩ := hfin Finset.univ
  exact ⟨δ, hδ, fun x ↦ hbound x (Finset.mem_univ x)⟩

/-- Decreasing all scores by one sufficiently small positive number preserves
their positive labels and makes every negative label strictly negative. -/
theorem exists_strict_shift {α : Type*} [Finite α] (S : α → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x,
      (0 < S x - δ ↔ 0 < S x) ∧ S x - δ ≠ 0 := by
  classical
  obtain ⟨δ, hδ, hbound⟩ := finite_positive_lower_bound
    (fun x ↦ if 0 < S x then S x else 1)
    (fun x ↦ by split <;> positivity)
  refine ⟨δ, hδ, fun x ↦ ?_⟩
  by_cases hx : 0 < S x
  · have hb : δ < S x := by simpa only [if_pos hx] using hbound x
    exact ⟨⟨fun _ ↦ hx, fun _ ↦ sub_pos.mpr hb⟩, (sub_pos.mpr hb).ne'⟩
  · have hn : S x - δ < 0 := by linarith [le_of_not_gt hx]
    exact ⟨⟨fun h ↦ False.elim ((not_lt_of_gt hn) h), fun h ↦ False.elim (hx h)⟩,
      hn.ne⟩

/-- Strict signs on a finite domain survive a uniform small perturbation. -/
theorem exists_sign_stability_margin {α : Type*} [Finite α]
    (S : α → ℝ) (hS : ∀ x, S x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ T : α → ℝ,
      (∀ x, |T x - S x| < δ) → ∀ x,
        (0 < T x ↔ 0 < S x) ∧ T x ≠ 0 := by
  obtain ⟨δ, hδ, hbound⟩ := finite_positive_lower_bound
    (fun x ↦ |S x|) (fun x ↦ abs_pos.mpr (hS x))
  refine ⟨δ, hδ, fun T hT x ↦ ?_⟩
  have hclose := (hT x).trans (hbound x)
  rcases lt_or_gt_of_ne (hS x) with hx | hx
  · rw [abs_of_neg hx] at hclose
    have hneg : T x < 0 := by have := (abs_lt.mp hclose).2; linarith
    exact ⟨⟨fun h ↦ False.elim ((not_lt_of_gt hneg) h),
      fun h ↦ False.elim ((not_lt_of_gt hx) h)⟩, hneg.ne⟩
  · rw [abs_of_pos hx] at hclose
    have hpos : 0 < T x := by have := (abs_lt.mp hclose).1; linarith
    exact ⟨⟨fun _ ↦ hx, fun _ ↦ hpos⟩, hpos.ne'⟩

end HeadComplexity
