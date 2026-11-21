import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Alternation of one affine fraction

The alternating face sum of an affine fraction with a positive constant
denominator coefficient and nonnegative slopes satisfies a subconvex
recurrence. This is an amplitude obstruction, not a head-count obstruction.
-/

namespace HeadComplexity

open scoped BigOperators

variable {ι : Type*}

/-- Alternation over all subsets of a coordinate face based at zero. -/
noncomputable def faceAlternation (s : Finset ι) (v : Finset ι → ℝ) : ℝ :=
  ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card * v t

theorem faceAlternation_congr (s : Finset ι) {v w : Finset ι → ℝ}
    (h : ∀ t ⊆ s, v t = w t) : faceAlternation s v = faceAlternation s w := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [h t (Finset.mem_powerset.mp ht)]

theorem faceAlternation_add (s : Finset ι) (v w : Finset ι → ℝ) :
    faceAlternation s (fun t ↦ v t + w t) = faceAlternation s v + faceAlternation s w := by
  simp [faceAlternation, mul_add, Finset.sum_add_distrib]

theorem faceAlternation_smul (s : Finset ι) (c : ℝ) (v : Finset ι → ℝ) :
    faceAlternation s (fun t ↦ c * v t) = c * faceAlternation s v := by
  simp [faceAlternation, Finset.mul_sum, mul_left_comm]

theorem faceAlternation_sum {κ : Type*} (s : Finset ι) (u : Finset κ)
    (v : κ → Finset ι → ℝ) :
    faceAlternation s (fun t ↦ ∑ i ∈ u, v i t) = ∑ i ∈ u, faceAlternation s (v i) := by
  simp only [faceAlternation, Finset.mul_sum]
  exact Finset.sum_comm

theorem faceAlternation_constant (s : Finset ι) (hs : s.Nonempty) (c : ℝ) :
    faceAlternation s (fun _ ↦ c) = 0 := by
  rw [faceAlternation, ← Finset.sum_mul]
  have h : (∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card) = 0 := by
    exact_mod_cast Finset.sum_powerset_neg_one_pow_card_of_nonempty hs
  rw [h, zero_mul]

variable [DecidableEq ι]

/-- Multiplication by a coordinate removes the face on which that coordinate
is zero from the complete alternating sum. -/
theorem faceAlternation_coordinate (s : Finset ι) (i : ι) (v : Finset ι → ℝ) :
    faceAlternation s (fun t ↦ if i ∈ t then v t else 0) =
      faceAlternation s v - faceAlternation (s.erase i) v := by
  have he : (s.erase i).powerset = s.powerset.filter (fun t ↦ i ∉ t) := by
    ext t
    simp only [Finset.mem_powerset, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.trans (Finset.erase_subset _ _), fun hi ↦ (Finset.mem_erase.mp (h hi)).1 rfl⟩
    · rintro ⟨h, hn⟩ j hj
      exact Finset.mem_erase.mpr ⟨fun hji ↦ hn (hji ▸ hj), h hj⟩
  unfold faceAlternation
  rw [he, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hi : i ∈ t <;> simp [hi]

/-- The exact discrete product rule for an affine denominator. -/
theorem faceAlternation_affine_mul (s : Finset ι) (b₀ : ℝ) (b : ι → ℝ)
    (v : Finset ι → ℝ) :
    faceAlternation s (fun t ↦ (b₀ + ∑ i ∈ t, b i) * v t) =
      (b₀ + ∑ i ∈ s, b i) * faceAlternation s v -
        ∑ i ∈ s, b i * faceAlternation (s.erase i) v := by
  have hpoint (t : Finset ι) (ht : t ⊆ s) :
      (b₀ + ∑ i ∈ t, b i) * v t =
        b₀ * v t + ∑ i ∈ s, b i * (if i ∈ t then v t else 0) := by
    rw [add_mul, Finset.sum_mul]
    congr 1
    symm
    calc
      _ = ∑ i ∈ t, b i * (if i ∈ t then v t else 0) := by
        symm
        apply Finset.sum_subset ht
        intro i _ hi
        simp [hi]
      _ = ∑ i ∈ t, b i * v t := Finset.sum_congr rfl (fun i hi ↦ by simp [hi])
  rw [faceAlternation_congr s hpoint, faceAlternation_add, faceAlternation_smul,
    faceAlternation_sum]
  simp_rw [faceAlternation_smul, faceAlternation_coordinate, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

omit [DecidableEq ι] in
theorem faceAlternation_affine_eq_zero (s : Finset ι) (hs : 2 ≤ s.card)
    (a₀ : ℝ) (a : ι → ℝ) :
    faceAlternation s (fun t ↦ a₀ + ∑ i ∈ t, a i) = 0 := by
  classical
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  have he (i : ι) (hi : i ∈ s) : (s.erase i).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hi]
    omega
  have h := faceAlternation_affine_mul s a₀ a (fun _ ↦ 1)
  simp only [mul_one] at h
  rw [h, faceAlternation_constant s hne, mul_zero]
  have hz : (∑ i ∈ s, a i * faceAlternation (s.erase i) (fun _ ↦ 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [faceAlternation_constant _ (he i hi), mul_zero]
  rw [hz, sub_self]

omit [DecidableEq ι] in
/-- Maximum principle for the subconvex recurrence of alternating face sums. -/
theorem faceAlternation_range_of_affine_product
    (b₀ : ℝ) (b : ι → ℝ) (hb₀ : 0 < b₀) (hb : ∀ i, 0 ≤ b i)
    (v : Finset ι → ℝ) (lo hi : ℝ)
    (hv : ∀ t, lo ≤ v t ∧ v t ≤ hi)
    (hzero : ∀ s : Finset ι, 2 ≤ s.card →
      faceAlternation s (fun t ↦ (b₀ + ∑ i ∈ t, b i) * v t) = 0)
    (s : Finset ι) (hs : s.Nonempty) : |faceAlternation s v| ≤ hi - lo := by
  classical
  have hM : 0 ≤ hi - lo := sub_nonneg.mpr ((hv ∅).1.trans (hv ∅).2)
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hcard : s.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
      have halt : faceAlternation {i} v = v ∅ - v {i} := by
        change (∑ t ∈ (insert i (∅ : Finset ι)).powerset, (-1 : ℝ) ^ t.card * v t) = _
        rw [Finset.sum_powerset_insert (Finset.notMem_empty i)]
        simp [sub_eq_add_neg]
      rw [halt]
      apply abs_le.mpr
      constructor <;> linarith [(hv ∅).1, (hv ∅).2, (hv {i}).1, (hv {i}).2]
    · have htwo : 2 ≤ s.card := by
        have := Finset.card_pos.mpr hs
        omega
      have herase (i : ι) (hi : i ∈ s) : (s.erase i).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem hi]
        omega
      have hsmall (i : ι) (himem : i ∈ s) :
          |faceAlternation (s.erase i) v| ≤ hi - lo := by
        exact ih (s.erase i) (Finset.erase_ssubset himem) (herase i himem)
      have hsum : 0 ≤ ∑ i ∈ s, b i := Finset.sum_nonneg (fun i _ ↦ hb i)
      have hD : 0 < b₀ + ∑ i ∈ s, b i := add_pos_of_pos_of_nonneg hb₀ hsum
      have hrec : (b₀ + ∑ i ∈ s, b i) * faceAlternation s v =
          ∑ i ∈ s, b i * faceAlternation (s.erase i) v := by
        have hz := hzero s htwo
        rw [faceAlternation_affine_mul] at hz
        exact sub_eq_zero.mp hz
      have hbound : |∑ i ∈ s, b i * faceAlternation (s.erase i) v| ≤
          (∑ i ∈ s, b i) * (hi - lo) := by
        calc
          _ ≤ ∑ i ∈ s, |b i * faceAlternation (s.erase i) v| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i ∈ s, b i * |faceAlternation (s.erase i) v| := by
            apply Finset.sum_congr rfl
            intro i _
            rw [abs_mul, abs_of_nonneg (hb i)]
          _ ≤ ∑ i ∈ s, b i * (hi - lo) :=
            Finset.sum_le_sum (fun i hi ↦ mul_le_mul_of_nonneg_left (hsmall i hi) (hb i))
          _ = _ := (Finset.sum_mul _ _ _).symm
      rw [← hrec, abs_mul, abs_of_pos hD] at hbound
      apply (mul_le_mul_iff_right₀ hD).mp
      nlinarith [mul_nonneg hb₀.le hM]

omit [DecidableEq ι] in
/-- The alternating sum of a positive-denominator affine fraction is at most
its output range. This says nothing about the number of unrestricted heads. -/
theorem abs_faceAlternation_affineFraction_le_range
    (a₀ b₀ : ℝ) (a b : ι → ℝ) (hb₀ : 0 < b₀) (hb : ∀ i, 0 ≤ b i)
    (lo hi : ℝ)
    (hv : ∀ t : Finset ι,
      lo ≤ (a₀ + ∑ i ∈ t, a i) / (b₀ + ∑ i ∈ t, b i) ∧
      (a₀ + ∑ i ∈ t, a i) / (b₀ + ∑ i ∈ t, b i) ≤ hi)
    (s : Finset ι) (hs : s.Nonempty) :
    |faceAlternation s (fun t ↦ (a₀ + ∑ i ∈ t, a i) / (b₀ + ∑ i ∈ t, b i))|
      ≤ hi - lo := by
  classical
  apply faceAlternation_range_of_affine_product b₀ b hb₀ hb _ lo hi hv ?_ s hs
  intro u hu
  have heq : faceAlternation u
      (fun t ↦ (b₀ + ∑ i ∈ t, b i) * ((a₀ + ∑ i ∈ t, a i) / (b₀ + ∑ i ∈ t, b i))) =
      faceAlternation u (fun t ↦ a₀ + ∑ i ∈ t, a i) := by
    apply faceAlternation_congr
    intro t _
    have hpos : 0 < b₀ + ∑ i ∈ t, b i :=
      add_pos_of_pos_of_nonneg hb₀ (Finset.sum_nonneg (fun i _ ↦ hb i))
    field_simp
  rw [heq]
  exact faceAlternation_affine_eq_zero u hu a₀ a

end HeadComplexity
