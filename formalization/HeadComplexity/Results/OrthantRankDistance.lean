import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Integer rank distances in an orthant dictionary

The counting inequality used in the deterministic orthant-matching audit.
This is an auxiliary obstruction, not a universal attention upper bound.
-/

namespace HeadComplexity

open scoped BigOperators

theorem int_rank_distance_card_bound (s : Finset ℤ) (c : ℤ) :
    (s.card : ℝ) * ((s.card : ℝ) - 1) ≤
      4 * ∑ a ∈ s, ((a - c).natAbs : ℝ) := by
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases hs : s = ∅
  · simp [hs]
  obtain ⟨a, ha, hmax⟩ :=
    s.exists_max_image (fun v : ℤ => (v - c).natAbs)
      (Finset.nonempty_iff_ne_empty.mpr hs)
  let q : ℕ := (a - c).natAbs
  have hsub : s ⊆ Finset.Icc (c - (q : ℤ)) (c + (q : ℤ)) := by
    intro v hv
    have hm : ((v - c).natAbs : ℤ) ≤ (q : ℤ) := by
      exact_mod_cast hmax v hv
    have hp := Int.le_natAbs (a := v - c)
    have hn : -(v - c) ≤ ((v - c).natAbs : ℤ) := by
      simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -(v - c)))
    simp only [Finset.mem_Icc]
    constructor <;> omega
  have hcard : s.card ≤ 2 * q + 1 := by
    have hc := Finset.card_le_card hsub
    have he := Int.card_Icc_of_le
      (a := c - (q : ℤ)) (b := c + (q : ℤ)) (by omega)
    omega
  have herase := Finset.card_erase_add_one ha
  have hq : ((s.erase a).card : ℝ) ≤ 2 * (q : ℝ) := by
    exact_mod_cast (show (s.erase a).card ≤ 2 * q by omega)
  have hc : (s.card : ℝ) = ((s.erase a).card : ℝ) + 1 := by
    exact_mod_cast herase.symm
  have hi := ih (s.erase a) (Finset.erase_ssubset ha)
  have hsum := s.sum_erase_add (fun v : ℤ => ((v - c).natAbs : ℝ)) ha
  change (∑ v ∈ s.erase a, ((v - c).natAbs : ℝ)) + (q : ℝ) =
    ∑ v ∈ s, ((v - c).natAbs : ℝ) at hsum
  rw [hc]
  nlinarith

theorem injective_rank_distance_card_bound {α : Type*} [DecidableEq α]
    (s : Finset α) (R : α → ℤ) (hR : Function.Injective R) (c : ℤ) :
    (s.card : ℝ) * ((s.card : ℝ) - 1) ≤
      4 * ∑ a ∈ s, ((R a - c).natAbs : ℝ) := by
  have h := int_rank_distance_card_bound (s.image R) c
  rw [Finset.card_image_of_injective s hR] at h
  rw [Finset.sum_image (fun a _ b _ hab => hR hab)] at h
  exact h

theorem multidimensional_rank_distance_card_bound {α ι : Type*}
    [DecidableEq α] [Fintype ι] (s : Finset α)
    (R : ι → α → ℤ) (hR : ∀ i, Function.Injective (R i)) (c : ι → ℤ) :
    (Fintype.card ι : ℝ) * (s.card : ℝ) * ((s.card : ℝ) - 1) ≤
      4 * ∑ a ∈ s, ∑ i, ((R i a - c i).natAbs : ℝ) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun i _ => injective_rank_distance_card_bound s (R i) (hR i) (c i))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum] at h
  rw [Finset.sum_comm] at h
  simpa only [mul_assoc] using h

theorem rank_ball_card_bound {α ι : Type*} [DecidableEq α] [Fintype ι]
    (s : Finset α) (hs : s.Nonempty) (R : ι → α → ℤ)
    (hR : ∀ i, Function.Injective (R i)) (c : ι → ℤ) (r : ℝ)
    (hr : ∀ a ∈ s, (∑ i, ((R i a - c i).natAbs : ℝ)) ≤ r) :
    (Fintype.card ι : ℝ) * ((s.card : ℝ) - 1) ≤ 4 * r := by
  have hd : 0 < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have h := multidimensional_rank_distance_card_bound s R hR c
  have hsum : (∑ a ∈ s, ∑ i, ((R i a - c i).natAbs : ℝ)) ≤
      (s.card : ℝ) * r := by
    simpa using Finset.sum_le_sum hr
  have hm : (s.card : ℝ) *
      ((Fintype.card ι : ℝ) * ((s.card : ℝ) - 1)) ≤
      (s.card : ℝ) * (4 * r) := by
    nlinarith
  exact le_of_mul_le_mul_left hm hd

end HeadComplexity
