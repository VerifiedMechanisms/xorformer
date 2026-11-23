import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

/-- Three pair relations with positive coefficients force all three values
to vanish. This is an auxiliary rigidity statement, not a head bound. -/
theorem three_positive_pair_relations_eq_zero
    (a b c d e f u v w : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (huv : a * u + b * v = 0)
    (huw : c * u + d * w = 0)
    (hvw : e * v + f * w = 0) : u = 0 ∧ v = 0 ∧ w = 0 := by
  have hu : u = 0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with hneg | hpos
    · have hv : 0 < v := by
        have hau : a * u < 0 := mul_neg_of_pos_of_neg ha hneg
        have hbv : 0 < b * v := by linarith
        exact (mul_pos_iff_of_pos_left hb).mp hbv
      have hw : 0 < w := by
        have hcu : c * u < 0 := mul_neg_of_pos_of_neg hc hneg
        have hdw : 0 < d * w := by linarith
        exact (mul_pos_iff_of_pos_left hd).mp hdw
      have hev : 0 < e * v := mul_pos he hv
      have hfw : 0 < f * w := mul_pos hf hw
      linarith
    · have hv : v < 0 := by
        have hau : 0 < a * u := mul_pos ha hpos
        have hbv : b * v < 0 := by linarith
        by_contra hv
        have hbv0 : 0 ≤ b * v := mul_nonneg (le_of_lt hb) (le_of_not_gt hv)
        linarith
      have hw : w < 0 := by
        have hcu : 0 < c * u := mul_pos hc hpos
        have hdw : d * w < 0 := by linarith
        by_contra hw
        have hdw0 : 0 ≤ d * w := mul_nonneg (le_of_lt hd) (le_of_not_gt hw)
        linarith
      have hev : e * v < 0 := mul_neg_of_pos_of_neg he hv
      have hfw : f * w < 0 := mul_neg_of_pos_of_neg hf hw
      linarith
  have hv : v = 0 := by
    rw [hu, mul_zero, zero_add] at huv
    exact (mul_eq_zero.mp huv).resolve_left (ne_of_gt hb)
  have hw : w = 0 := by
    rw [hu, mul_zero, zero_add] at huw
    exact (mul_eq_zero.mp huw).resolve_left (ne_of_gt hd)
  exact ⟨hu, hv, hw⟩

/-- A complete graph of positive pair relations on at least three specified
indices has only the zero solution. No finiteness assumption is needed. -/
theorem positive_pair_relations_vanish_of_three {ι : Type*}
    (u : ι → ℝ) (a : ι → ι → ℝ) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (ha : ∀ r s, r ≠ s → 0 < a r s)
    (hpair : ∀ r s, r ≠ s → a r s * u r + a s r * u s = 0) :
    ∀ r, u r = 0 := by
  have hi := (three_positive_pair_relations_eq_zero
    (a i j) (a j i) (a i k) (a k i) (a j k) (a k j)
    (u i) (u j) (u k)
    (ha i j hij) (ha j i hij.symm) (ha i k hik)
    (ha k i hik.symm) (ha j k hjk) (ha k j hjk.symm)
    (hpair i j hij) (hpair i k hik) (hpair j k hjk)).1
  intro r
  by_cases hri : r = i
  · simpa [hri] using hi
  · have hp := hpair r i hri
    rw [hi, mul_zero, add_zero] at hp
    exact (mul_eq_zero.mp hp).resolve_left (ne_of_gt (ha r i hri))

end HeadComplexity
