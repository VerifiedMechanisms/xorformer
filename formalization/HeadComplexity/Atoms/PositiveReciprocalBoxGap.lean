import Mathlib.Tactic

set_option linter.style.header false

/-! A quantitative compiler from separated box incidences to positive
reciprocal scores. The geometric incidence construction is not formalized
in this file, and the inputs here are real vectors, not Boolean vectors. -/

namespace HeadComplexity.PositiveReciprocalBoxGap

open Finset

theorem reciprocal_inside {t : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1 / 4) :
    4 / 5 ≤ 1 / (1 + t) := by
  have hd : 0 < 1 + t := by linarith
  apply (le_div_iff₀ hd).mpr
  linarith

theorem reciprocal_outside {t h : ℝ} (hh : 0 < h) (ht : 16 * h ≤ t) :
    0 < 1 / (1 + t) ∧ 1 / (1 + t) < 1 / (16 * h) := by
  have hd : 0 < 16 * h := by positivity
  have hdt : 0 < 1 + t := by linarith
  constructor
  · positivity
  · exact (one_div_lt_one_div hdt hd).mpr (by linarith)

theorem separated_box_sum {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] (inside : I → J → Prop) [DecidableRel inside]
    (t : I → J → ℝ) (ht : ∀ i j, 0 ≤ t i j)
    (hin : ∀ i j, inside i j → t i j ≤ 1 / 4)
    (hout : ∀ i j, ¬inside i j → 16 * (Fintype.card I : ℝ) ≤ t i j)
    (j : J) :
    ((∃ i, inside i j) →
      1 / 4 < (∑ i, 1 / (1 + t i j)) - 1 / 2) ∧
    ((¬∃ i, inside i j) →
      (∑ i, 1 / (1 + t i j)) - 1 / 2 < -(1 / 4)) := by
  classical
  have hcard : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  constructor
  · rintro ⟨i, hi⟩
    have hv := reciprocal_inside (ht i j) (hin i j hi)
    have hs : 1 / (1 + t i j) ≤ ∑ k, 1 / (1 + t k j) := by
      apply single_le_sum (fun k _ ↦ ?_) (mem_univ i)
      have hk := ht k j
      positivity
    linarith
  · intro hnone
    have hs : (∑ i, 1 / (1 + t i j)) <
        ∑ _i : I, 1 / (16 * (Fintype.card I : ℝ)) := by
      apply sum_lt_sum_of_nonempty (s := univ) univ_nonempty
      intro i _
      exact (reciprocal_outside hcard (hout i j (fun hi ↦ hnone ⟨i, hi⟩))).2
    have he : (∑ _i : I, 1 / (16 * (Fintype.card I : ℝ))) = 1 / 16 := by
      simp only [sum_const, card_univ, nsmul_eq_mul]
      field_simp
    rw [he] at hs
    linarith

#print axioms reciprocal_inside
#print axioms reciprocal_outside
#print axioms separated_box_sum

end HeadComplexity.PositiveReciprocalBoxGap
