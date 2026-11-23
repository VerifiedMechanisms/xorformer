import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false

/-! A boundary escape for arbitrary nonzero linear functionals on cube tables.
This is an obstruction to a numerator-norm Lagrangian certificate, not a
lower bound on worst-case head complexity. -/

namespace HeadComplexity.NegativePoleEscape

open scoped BigOperators
open Finset

variable {n : ℕ}

noncomputable def weight (s : Finset (Fin n)) (t : ℝ) (i : Fin n) : ℝ :=
  if i ∈ s then 1 else t

noncomputable def denom (s : Finset (Fin n)) (t : ℝ)
    (x : Finset (Fin n)) : ℝ := t + ∑ i ∈ xᶜ, weight s t i

noncomputable def constant (s : Finset (Fin n)) (t : ℝ) : ℝ :=
  t + ∑ i : Fin n, weight s t i

theorem weight_pos (s : Finset (Fin n)) {t : ℝ} (ht : 0 < t) (i : Fin n) :
    0 < weight s t i := by
  unfold weight
  split_ifs <;> positivity

theorem denom_pos (s : Finset (Fin n)) {t : ℝ} (ht : 0 < t)
    (x : Finset (Fin n)) : 0 < denom s t x := by
  exact add_pos_of_pos_of_nonneg ht
    (Finset.sum_nonneg fun i _ ↦ (weight_pos s ht i).le)

theorem constant_pos (s : Finset (Fin n)) {t : ℝ} (ht : 0 < t) :
    0 < constant s t := by
  exact add_pos_of_pos_of_nonneg ht
    (Finset.sum_nonneg fun i _ ↦ (weight_pos s ht i).le)

theorem denom_selected (s : Finset (Fin n)) (t : ℝ) :
    denom s t s = t * (1 + (sᶜ.card : ℝ)) := by
  unfold denom
  have hh : ∀ i ∈ sᶜ, weight s t i = t := by
    intro i hi
    simp only [Finset.mem_compl] at hi
    simp [weight, hi]
  simp_rw [Finset.sum_congr rfl hh]
  simp
  ring

theorem denom_selected_le (s : Finset (Fin n)) {t : ℝ} (ht : 0 ≤ t) :
    denom s t s ≤ t * ((n : ℝ) + 1) := by
  rw [denom_selected]
  have hc : sᶜ.card ≤ n := by simpa using Finset.card_le_univ sᶜ
  have hcr : (sᶜ.card : ℝ) ≤ n := by exact_mod_cast hc
  apply mul_le_mul_of_nonneg_left _ ht
  linarith

theorem denom_ge_one_of_not_subset (s x : Finset (Fin n)) {t : ℝ}
    (ht : 0 < t) (hx : ¬s ⊆ x) : 1 ≤ denom s t x := by
  obtain ⟨i, his, hix⟩ := Finset.not_subset.mp hx
  have hi : i ∈ xᶜ := by simpa using hix
  have hh := Finset.single_le_sum
    (fun j (_ : j ∈ xᶜ) ↦ (weight_pos s ht j).le) hi
  have hw : weight s t i = 1 := by simp [weight, his]
  rw [hw] at hh
  unfold denom
  linarith

theorem constant_ge_one (s : Finset (Fin n)) {t : ℝ} (ht : 0 < t)
    (hs : s.Nonempty) : 1 ≤ constant s t := by
  obtain ⟨i, hi⟩ := hs
  have hh := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) ↦ (weight_pos s ht j).le)
    (Finset.mem_univ i)
  have hw : weight s t i = 1 := by simp [weight, hi]
  rw [hw] at hh
  unfold constant
  linarith

theorem denom_eq_constant_sub (s x : Finset (Fin n)) (t : ℝ) :
    denom s t x = constant s t - ∑ i ∈ x, weight s t i := by
  have hh := Finset.sum_add_sum_compl x (weight s t)
  unfold denom constant
  linarith

theorem exists_maximal_support (a : Finset (Fin n) → ℝ)
    (ha : ∃ s, s.Nonempty ∧ a s ≠ 0) :
    ∃ s, s.Nonempty ∧ a s ≠ 0 ∧
      ∀ x, s ⊂ x → a x = 0 := by
  classical
  let support := Finset.univ.filter (fun s : Finset (Fin n) ↦ s.Nonempty ∧ a s ≠ 0)
  have hne : support.Nonempty := by
    obtain ⟨s, hs, has⟩ := ha
    exact ⟨s, by simp [support, hs, has]⟩
  obtain ⟨s, hs, hmax⟩ := support.exists_max_image Finset.card hne
  have hs' : s.Nonempty ∧ a s ≠ 0 := by simpa [support] using hs
  refine ⟨s, hs'.1, hs'.2, ?_⟩
  intro x hx
  by_contra hax
  have hxne : x.Nonempty := hs'.1.mono hx.subset
  have hmem : x ∈ support := by simp [support, hxne, hax]
  exact (not_lt_of_ge (hmax x hmem)) (Finset.card_lt_card hx)

noncomputable def score (s : Finset (Fin n)) (t : ℝ) (i : Fin n)
    (d : ℝ) (x : Finset (Fin n)) : ℝ :=
  (if i ∈ x then d else 0) / denom s t x

theorem nonselected_term_bound (a : Finset (Fin n) → ℝ)
    (s : Finset (Fin n)) (t : ℝ) (i : Fin n) (d : ℝ)
    (ht : 0 < t) (hd : |d| ≤ 1)
    (hmax : ∀ x, s ⊂ x → a x = 0) (x : Finset (Fin n)) (hx : x ≠ s) :
    |a x * score s t i d x| ≤ |a x| := by
  by_cases hax : a x = 0
  · simp [hax]
  have hns : ¬s ⊆ x := by
    intro hsx
    exact hax (hmax x (Finset.ssubset_iff_subset_ne.mpr ⟨hsx, Ne.symm hx⟩))
  have hden := denom_ge_one_of_not_subset s x ht hns
  have hp := denom_pos s ht x
  have hn : |if i ∈ x then d else 0| ≤ 1 := by split_ifs <;> simpa using hd
  have hr : |score s t i d x| ≤ 1 := by
    rw [score, abs_div, abs_of_pos hp]
    exact (div_le_one hp).mpr (hn.trans hden)
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_left hr (abs_nonneg (a x))

theorem weighted_score_lower (a : Finset (Fin n) → ℝ)
    (s : Finset (Fin n)) (t : ℝ) (i : Fin n) (d : ℝ)
    (ht : 0 < t) (hi : i ∈ s) (hd : |d| ≤ 1)
    (hmax : ∀ x, s ⊂ x → a x = 0) :
    a s * d / denom s t s - (∑ x, |a x|) ≤ ∑ x, a x * score s t i d x := by
  classical
  let rest : Finset (Finset (Fin n)) := Finset.univ.erase s
  have htail : -(∑ x, |a x|) ≤ ∑ x ∈ rest, a x * score s t i d x := by
    calc
      _ ≤ -(∑ x ∈ rest, |a x|) := by
        apply neg_le_neg
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun x _ _ ↦ abs_nonneg (a x))
      _ = ∑ x ∈ rest, -|a x| := by rw [Finset.sum_neg_distrib]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        have hxs : x ≠ s := (Finset.mem_erase.mp hx).1
        exact (abs_le.mp (nonselected_term_bound a s t i d ht hd hmax x hxs)).1
  have hsum := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin n))))
    (fun x ↦ a x * score s t i d x) (Finset.mem_univ s)
  have hsel : a s * score s t i d s = a s * d / denom s t s := by
    simp [score, hi, mul_div_assoc]
  change (∑ x ∈ rest, a x * score s t i d x) + a s * score s t i d s = _ at hsum
  rw [hsel] at hsum
  linarith

theorem exists_large_weighted_score (a : Finset (Fin n) → ℝ)
    (ha : ∃ s, s.Nonempty ∧ a s ≠ 0) (R : ℝ) (hR : 0 ≤ R) :
    ∃ s t i d, s.Nonempty ∧ 0 < t ∧ |d| = 1 ∧ i ∈ s ∧
      R < ∑ x, a x * score s t i d x := by
  classical
  obtain ⟨s, hs, has, hmax⟩ := exists_maximal_support a ha
  obtain ⟨i, hi⟩ := hs
  let L : ℝ := ∑ x, |a x|
  have hL : 0 ≤ L := Finset.sum_nonneg fun x _ ↦ abs_nonneg (a x)
  let d : ℝ := if 0 < a s then 1 else -1
  have hd : |d| = 1 := by unfold d; split_ifs <;> norm_num
  have had : a s * d = |a s| := by
    unfold d
    split_ifs with hh
    · simp [abs_of_pos hh]
    · rw [abs_of_neg (lt_of_le_of_ne (le_of_not_gt hh) has)]
      ring
  have haabs : 0 < |a s| := abs_pos.mpr has
  have hbudget : 0 < R + L + 1 := by linarith
  have hn : 0 < (n : ℝ) + 1 := by positivity
  let t := |a s| / (((n : ℝ) + 1) * (R + L + 1))
  have ht : 0 < t := div_pos haabs (mul_pos hn hbudget)
  have htbudget : t * ((n : ℝ) + 1) * (R + L + 1) = |a s| := by
    unfold t
    field_simp
  have hdens : 0 < denom s t s := denom_pos s ht s
  have hmain : R + L + 1 ≤ |a s| / denom s t s := by
    apply (le_div_iff₀ hdens).mpr
    have hh := mul_le_mul_of_nonneg_right (denom_selected_le s ht.le) hbudget.le
    rw [htbudget] at hh
    nlinarith
  have hlower := weighted_score_lower a s t i d ht hi hd.le hmax
  rw [had] at hlower
  refine ⟨s, t, i, d, ⟨i, hi⟩, ht, hd, hi, ?_⟩
  change |a s| / denom s t s - L ≤ _ at hlower
  linarith

def bits (x : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ x)

theorem affineValue_bits (c : ℝ) (a : Fin n → ℝ) (x : Finset (Fin n)) :
    affineValue c a (bits x) = c + ∑ i ∈ x, a i := by
  classical
  unfold affineValue
  congr 1
  calc
    _ = ∑ i : Fin n, if i ∈ x then a i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ x <;> simp [bits, boolToReal, hi]
    _ = _ := by simp

noncomputable def slope (s : Finset (Fin n)) (t : ℝ) (i : Fin n) : ℝ :=
  -weight s t i / constant s t

noncomputable def numerator (s : Finset (Fin n)) (t : ℝ) (i : Fin n)
    (d : ℝ) (j : Fin n) : ℝ := if j = i then d / constant s t else 0

theorem slope_negative (s : Finset (Fin n)) {t : ℝ} (ht : 0 < t) (i : Fin n) :
    slope s t i < 0 :=
  div_neg_of_neg_of_pos (neg_neg_of_pos (weight_pos s ht i)) (constant_pos s ht)

theorem slope_margin (s : Finset (Fin n)) {t : ℝ} (ht : 0 < t) :
    ∑ i : Fin n, -slope s t i < 1 := by
  simp only [slope, neg_div, neg_neg, ← Finset.sum_div]
  apply (div_lt_one (constant_pos s ht)).mpr
  unfold constant
  linarith

theorem numerator_norm (s : Finset (Fin n)) (hs : s.Nonempty) {t : ℝ}
    (ht : 0 < t) (i : Fin n) (d : ℝ) (hd : |d| ≤ 1) :
    ∑ j : Fin n, (numerator s t i d j) ^ 2 ≤ 1 := by
  have hp := constant_pos s ht
  have hc := constant_ge_one s ht hs
  have hh : |d / constant s t| ≤ 1 := by
    rw [abs_div, abs_of_pos hp]
    exact (div_le_one hp).mpr (hd.trans hc)
  have hsquare : (d / constant s t) ^ 2 ≤ 1 := by
    have hb := abs_le.mp hh
    have hm := mul_nonneg (sub_nonneg.mpr hb.2)
      (show 0 ≤ d / constant s t + 1 by linarith)
    nlinarith
  simpa [numerator, ite_pow] using hsquare

theorem normalized_denominator (s x : Finset (Fin n)) {t : ℝ} (ht : 0 < t) :
    affineValue 1 (slope s t) (bits x) = denom s t x / constant s t := by
  rw [affineValue_bits, denom_eq_constant_sub]
  simp only [slope, neg_div, Finset.sum_neg_distrib, ← Finset.sum_div]
  field_simp [(constant_pos s ht).ne']
  ring

theorem normalized_numerator (s x : Finset (Fin n)) (t : ℝ) (i : Fin n) (d : ℝ) :
    affineValue 0 (numerator s t i d) (bits x) =
      (if i ∈ x then d else 0) / constant s t := by
  rw [affineValue_bits]
  by_cases hi : i ∈ x <;> simp [numerator, hi]

theorem normalized_score (s x : Finset (Fin n)) {t : ℝ} (ht : 0 < t)
    (i : Fin n) (d : ℝ) :
    affineValue 0 (numerator s t i d) (bits x) /
        affineValue 1 (slope s t) (bits x) = score s t i d x := by
  rw [normalized_denominator s x ht, normalized_numerator]
  unfold score
  field_simp [(constant_pos s ht).ne']

noncomputable def atom (s : Finset (Fin n)) (t : ℝ) (ht : 0 < t)
    (i : Fin n) (d : ℝ) : FracAtom n :=
  FracAtom.ofNegativeAffineRatio 0 (numerator s t i d) 1 (slope s t)
    (by norm_num) (slope_negative s ht) (slope_margin s ht)

theorem atom_eval (s x : Finset (Fin n)) {t : ℝ} (ht : 0 < t)
    (i : Fin n) (d : ℝ) : (atom s t ht i d).eval (bits x) = score s t i d x := by
  rw [atom, FracAtom.ofNegativeAffineRatio_eval, normalized_score s x ht]

theorem unbounded_normalized_functional (a : Finset (Fin n) → ℝ)
    (ha : ∃ s, s.Nonempty ∧ a s ≠ 0) (R : ℝ) :
    ∃ (u b : Fin n → ℝ),
      (∀ i, b i < 0) ∧ (∑ i, -b i < 1) ∧ (∑ i, (u i)^2 ≤ 1) ∧
      R < ∑ x, a x * (affineValue 0 u (bits x) / affineValue 1 b (bits x)) := by
  obtain ⟨s, t, i, d, hs, ht, hd, _, hlarge⟩ :=
    exists_large_weighted_score a ha (max R 0) (le_max_right R 0)
  refine ⟨numerator s t i d, slope s t, slope_negative s ht,
    slope_margin s ht, numerator_norm s hs ht i d hd.le, ?_⟩
  simp_rw [normalized_score s _ ht]
  exact (le_max_left R 0).trans_lt hlarge

theorem unbounded_atom_functional (a : Finset (Fin n) → ℝ)
    (ha : ∃ s, s.Nonempty ∧ a s ≠ 0) (R : ℝ) :
    ∃ φ : FracAtom n, R < ∑ x, a x * φ.eval (bits x) := by
  obtain ⟨s, t, i, d, _, ht, _, _, hlarge⟩ :=
    exists_large_weighted_score a ha (max R 0) (le_max_right R 0)
  refine ⟨atom s t ht i d, ?_⟩
  simp_rw [atom_eval]
  exact (le_max_left R 0).trans_lt hlarge

noncomputable def lagrangian (a : Finset (Fin n) → ℝ) (C : ℝ)
    (u b : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, (u i)^2) + C -
    ∑ x, a x * (affineValue 0 u (bits x) / affineValue 1 b (bits x))

theorem lagrangian_unbounded_below (a : Finset (Fin n) → ℝ)
    (ha : ∃ s, s.Nonempty ∧ a s ≠ 0) (C R : ℝ) :
    ∃ (u b : Fin n → ℝ),
      (∀ i, b i < 0) ∧ (∑ i, -b i < 1) ∧ (∑ i, (u i)^2 ≤ 1) ∧
      lagrangian a C u b < R := by
  obtain ⟨u, b, hb, hm, hu, hl⟩ := unbounded_normalized_functional a ha (C + 1 - R)
  refine ⟨u, b, hb, hm, hu, ?_⟩
  unfold lagrangian
  linarith

#print axioms unbounded_normalized_functional
#print axioms unbounded_atom_functional
#print axioms lagrangian_unbounded_below

end HeadComplexity.NegativePoleEscape
