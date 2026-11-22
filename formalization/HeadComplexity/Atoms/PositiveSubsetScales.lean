import Mathlib.Tactic

set_option linter.style.header false

/-! Widely separated positive subset sums, and ratios of such sums, have
injective dominant-summand labels. This is an affine-table compatibility
obstruction, not a worst-case head-complexity lower bound. -/

namespace HeadComplexity.PositiveSubsetScales

open Finset

theorem dominant_summand {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (s : Finset I) (hs : s.Nonempty) :
    ∃ i ∈ s, w i ≤ ∑ j ∈ s, w j ∧
      (∑ j ∈ s, w j) ≤ (Fintype.card I : ℝ) * w i := by
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image w hs
  refine ⟨i, hi, ?_, ?_⟩
  · exact single_le_sum (fun j _ ↦ hw j) hi
  · calc
      (∑ j ∈ s, w j) ≤ ∑ _j ∈ s, w i := sum_le_sum fun j hj ↦ hmax j hj
      _ = (s.card : ℝ) * w i := by simp
      _ ≤ (Fintype.card I : ℝ) * w i := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast s.card_le_univ) (hw i)

theorem separated_subset_sums {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (s : J → Finset I) (hs : ∀ j, (s j).Nonempty)
    (hsep : ∀ j k, j ≠ k →
      (Fintype.card I : ℝ) * (∑ i ∈ s k, w i) < ∑ i ∈ s j, w i ∨
      (Fintype.card I : ℝ) * (∑ i ∈ s j, w i) < ∑ i ∈ s k, w i) :
    Fintype.card J ≤ Fintype.card I := by
  classical
  choose top hmem hlo hhi using fun j ↦ dominant_summand w hw (s j) (hs j)
  apply Fintype.card_le_of_injective top
  intro j k he
  by_contra hne
  have hd : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have hjk : (∑ i ∈ s j, w i) ≤
      (Fintype.card I : ℝ) * (∑ i ∈ s k, w i) := by
    calc
      _ ≤ (Fintype.card I : ℝ) * w (top j) := hhi j
      _ = (Fintype.card I : ℝ) * w (top k) := by rw [he]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlo k) hd
  have hkj : (∑ i ∈ s k, w i) ≤
      (Fintype.card I : ℝ) * (∑ i ∈ s j, w i) := by
    calc
      _ ≤ (Fintype.card I : ℝ) * w (top k) := hhi k
      _ = (Fintype.card I : ℝ) * w (top j) := by rw [he]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlo j) hd
  rcases hsep j k hne with h | h <;> linarith

theorem ratio_comparison {a b A₁ A₂ B₁ B₂ d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hA₁ : a ≤ A₁ ∧ A₁ ≤ d * a) (hA₂ : a ≤ A₂ ∧ A₂ ≤ d * a)
    (hB₁ : b ≤ B₁ ∧ B₁ ≤ e * b) (hB₂ : b ≤ B₂ ∧ B₂ ≤ e * b)
    (hB₁pos : 0 < B₁) (hB₂pos : 0 < B₂) :
    A₁ / B₁ ≤ (d * e) * (A₂ / B₂) := by
  have hA₂nonneg : 0 ≤ A₂ := ha.trans hA₂.1
  have hprod : A₁ * B₂ ≤ (d * e) * A₂ * B₁ := by
    calc
      A₁ * B₂ ≤ (d * a) * (e * b) :=
        mul_le_mul hA₁.2 hB₂.2 (le_of_lt hB₂pos) (mul_nonneg hd ha)
      _ = (d * e) * (a * b) := by ring
      _ ≤ (d * e) * (A₂ * B₁) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hA₂.1 hB₁.1 hb hA₂nonneg)
          (mul_nonneg hd he)
      _ = _ := by ring
  rw [← mul_div_assoc]
  exact (div_le_div_iff₀ hB₁pos hB₂pos).mpr hprod

theorem separated_ratios {I K J : Type*} [Fintype I] [Fintype K] [Fintype J]
    (w : I → ℝ) (v : K → ℝ) (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 < v i)
    (s : J → Finset I) (t : J → Finset K)
    (hs : ∀ j, (s j).Nonempty) (ht : ∀ j, (t j).Nonempty)
    (hsep : ∀ j k, j ≠ k →
      ((Fintype.card I : ℝ) * Fintype.card K) *
        ((∑ i ∈ s k, w i) / ∑ i ∈ t k, v i) <
          (∑ i ∈ s j, w i) / ∑ i ∈ t j, v i ∨
      ((Fintype.card I : ℝ) * Fintype.card K) *
        ((∑ i ∈ s j, w i) / ∑ i ∈ t j, v i) <
          (∑ i ∈ s k, w i) / ∑ i ∈ t k, v i) :
    Fintype.card J ≤ Fintype.card I * Fintype.card K := by
  classical
  choose topW hmemW hloW hhiW using fun j ↦ dominant_summand w hw (s j) (hs j)
  choose topV hmemV hloV hhiV using fun j ↦
    dominant_summand v (fun i ↦ (hv i).le) (t j) (ht j)
  have hden (j : J) : 0 < ∑ i ∈ t j, v i :=
    Finset.sum_pos (fun i _ ↦ hv i) (ht j)
  have hinj : Function.Injective (fun j ↦ (topW j, topV j)) := by
    intro j k heq
    have heW := congrArg Prod.fst heq
    have heV := congrArg Prod.snd heq
    dsimp at heW heV
    by_contra hne
    have hWk : w (topW j) ≤ ∑ i ∈ s k, w i := by rw [heW]; exact hloW k
    have hVk : v (topV j) ≤ ∑ i ∈ t k, v i := by rw [heV]; exact hloV k
    have hWk' : (∑ i ∈ s k, w i) ≤ (Fintype.card I : ℝ) * w (topW j) := by
      rw [heW]; exact hhiW k
    have hVk' : (∑ i ∈ t k, v i) ≤ (Fintype.card K : ℝ) * v (topV j) := by
      rw [heV]; exact hhiV k
    have hjk := ratio_comparison (hw (topW j)) (hv (topV j)).le
      (Nat.cast_nonneg (Fintype.card I)) (Nat.cast_nonneg (Fintype.card K))
      ⟨hloW j, hhiW j⟩ ⟨hWk, hWk'⟩ ⟨hloV j, hhiV j⟩ ⟨hVk, hVk'⟩
      (hden j) (hden k)
    have hkj := ratio_comparison (hw (topW j)) (hv (topV j)).le
      (Nat.cast_nonneg (Fintype.card I)) (Nat.cast_nonneg (Fintype.card K))
      ⟨hWk, hWk'⟩ ⟨hloW j, hhiW j⟩ ⟨hVk, hVk'⟩ ⟨hloV j, hhiV j⟩
      (hden k) (hden j)
    rcases hsep j k hne with h | h <;> linarith
  simpa using Fintype.card_le_of_injective _ hinj

#print axioms separated_subset_sums
#print axioms ratio_comparison
#print axioms separated_ratios

end HeadComplexity.PositiveSubsetScales
