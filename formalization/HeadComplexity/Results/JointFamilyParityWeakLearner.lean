import HeadComplexity.Results.AffineFractionAlternation
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option linter.style.header false

/-!
A single affine fraction with a positive monotone affine denominator has
small normalized correlation with full parity. This is an approximation
obstruction for one atom, not a lower bound for sums with cancellation.
-/

namespace HeadComplexity

open scoped BigOperators

variable {ι : Type*}

/-- The alternating face recurrence is controlled just by the edges from
zero, rather than by the entire range of the function. -/
theorem jointFamily_faceAlternation_abs_le_of_edges
    (b₀ : ℝ) (b : ι → ℝ) (hb₀ : 0 < b₀) (hb : ∀ i, 0 ≤ b i)
    (v : Finset ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hzero : ∀ s : Finset ι, 2 ≤ s.card →
      faceAlternation s (fun t ↦ (b₀ + ∑ i ∈ t, b i) * v t) = 0)
    (s : Finset ι) (hs : s.Nonempty)
    (hedge : ∀ i ∈ s, |v ∅ - v {i}| ≤ M) :
    |faceAlternation s v| ≤ M := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hcard : s.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
      have halt : faceAlternation {i} v = v ∅ - v {i} := by
        change (∑ t ∈ (insert i (∅ : Finset ι)).powerset, (-1 : ℝ) ^ t.card * v t) = _
        rw [Finset.sum_powerset_insert (Finset.notMem_empty i)]
        simp [sub_eq_add_neg]
      rw [halt]
      exact hedge i (by simp)
    · have htwo : 2 ≤ s.card := by
        have := Finset.card_pos.mpr hs
        omega
      have herase (i : ι) (hi : i ∈ s) : (s.erase i).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem hi]
        omega
      have hsmall (i : ι) (hi : i ∈ s) :
          |faceAlternation (s.erase i) v| ≤ M := by
        apply ih (s.erase i) (Finset.erase_ssubset hi) (herase i hi)
        intro j hj
        exact hedge j (Finset.mem_of_mem_erase hj)
      have hsum : 0 ≤ ∑ i ∈ s, b i := Finset.sum_nonneg (fun i _ ↦ hb i)
      have hD : 0 < b₀ + ∑ i ∈ s, b i := add_pos_of_pos_of_nonneg hb₀ hsum
      have hrec : (b₀ + ∑ i ∈ s, b i) * faceAlternation s v =
          ∑ i ∈ s, b i * faceAlternation (s.erase i) v := by
        have hz := hzero s htwo
        rw [faceAlternation_affine_mul] at hz
        exact sub_eq_zero.mp hz
      have hbound : |∑ i ∈ s, b i * faceAlternation (s.erase i) v| ≤
          (∑ i ∈ s, b i) * M := by
        calc
          _ ≤ ∑ i ∈ s, |b i * faceAlternation (s.erase i) v| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i ∈ s, b i * |faceAlternation (s.erase i) v| := by
            apply Finset.sum_congr rfl
            intro i _
            rw [abs_mul, abs_of_nonneg (hb i)]
          _ ≤ ∑ i ∈ s, b i * M :=
            Finset.sum_le_sum (fun i hi ↦ mul_le_mul_of_nonneg_left (hsmall i hi) (hb i))
          _ = _ := (Finset.sum_mul _ _ _).symm
      rw [← hrec, abs_mul, abs_of_pos hD] at hbound
      apply (mul_le_mul_iff_right₀ hD).mp
      nlinarith [mul_nonneg hb₀.le hM]

/-- Squared unnormalized parity correlation of one affine fraction is at most
twice its squared Euclidean norm on the face. All numerator coefficients
are unrestricted. -/
theorem jointFamily_affineFraction_parity_sq_le_two_energy
    (a₀ b₀ : ℝ) (a b : ι → ℝ) (hb₀ : 0 < b₀) (hb : ∀ i, 0 ≤ b i)
    (s : Finset ι) (hs : s.Nonempty) :
    (faceAlternation s (fun t ↦ (a₀ + ∑ i ∈ t, a i) /
      (b₀ + ∑ i ∈ t, b i))) ^ 2 ≤
      2 * ∑ t ∈ s.powerset, ((a₀ + ∑ i ∈ t, a i) /
        (b₀ + ∑ i ∈ t, b i)) ^ 2 := by
  classical
  let v : Finset ι → ℝ := fun t ↦ (a₀ + ∑ i ∈ t, a i) / (b₀ + ∑ i ∈ t, b i)
  let E : ℝ := ∑ t ∈ s.powerset, (v t) ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hroot : (Real.sqrt (2 * E)) ^ 2 = 2 * E := Real.sq_sqrt (by positivity)
  have hedges (i : ι) (hi : i ∈ s) : |v ∅ - v {i}| ≤ Real.sqrt (2 * E) := by
    have hsub : ({∅, {i}} : Finset (Finset ι)) ⊆ s.powerset := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Finset.mem_powerset.mpr (Finset.empty_subset _)
      · exact Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hi)
    have hpair : (v ∅) ^ 2 + (v {i}) ^ 2 ≤ E := by
      have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun t _ _ ↦ sq_nonneg (v t))
      simpa only [Finset.sum_pair (by simp : (∅ : Finset ι) ≠ {i})] using h
    apply (abs_le).2
    constructor <;> nlinarith [sq_nonneg (v ∅ + v {i}), Real.sqrt_nonneg (2 * E)]
  have halt : |faceAlternation s v| ≤ Real.sqrt (2 * E) := by
    apply jointFamily_faceAlternation_abs_le_of_edges b₀ b hb₀ hb v _
      (Real.sqrt_nonneg _) ?_ s hs hedges
    intro u hu
    have heq : faceAlternation u
        (fun t ↦ (b₀ + ∑ i ∈ t, b i) * v t) =
        faceAlternation u (fun t ↦ a₀ + ∑ i ∈ t, a i) := by
      apply faceAlternation_congr
      intro t _
      have hpos : 0 < b₀ + ∑ i ∈ t, b i :=
        add_pos_of_pos_of_nonneg hb₀ (Finset.sum_nonneg (fun i _ ↦ hb i))
      dsimp [v]
      field_simp
    rw [heq]
    exact faceAlternation_affine_eq_zero u hu a₀ a
  change (faceAlternation s v) ^ 2 ≤ 2 * E
  nlinarith [sq_abs (faceAlternation s v), abs_nonneg (faceAlternation s v)]

/-- The same obstruction holds for an entire family of independently chosen
columns. In particular, sharing denominator slopes cannot improve its
normalized correlation with a parity times column-vector target. -/
theorem jointFamily_affineFraction_columns_parity_sq_le_two_energy
    {κ : Type*} (J : Finset κ) (τ a₀ b₀ : κ → ℝ)
    (a b : κ → ι → ℝ) (hb₀ : ∀ j ∈ J, 0 < b₀ j)
    (hb : ∀ j ∈ J, ∀ i, 0 ≤ b j i)
    (s : Finset ι) (hs : s.Nonempty) :
    (∑ j ∈ J, τ j * faceAlternation s
      (fun t ↦ (a₀ j + ∑ i ∈ t, a j i) / (b₀ j + ∑ i ∈ t, b j i))) ^ 2 ≤
      2 * (∑ j ∈ J, (τ j) ^ 2) *
        ∑ j ∈ J, ∑ t ∈ s.powerset,
          ((a₀ j + ∑ i ∈ t, a j i) / (b₀ j + ∑ i ∈ t, b j i)) ^ 2 := by
  let L : κ → ℝ := fun j ↦ faceAlternation s
    (fun t ↦ (a₀ j + ∑ i ∈ t, a j i) / (b₀ j + ∑ i ∈ t, b j i))
  let E : κ → ℝ := fun j ↦ ∑ t ∈ s.powerset,
    ((a₀ j + ∑ i ∈ t, a j i) / (b₀ j + ∑ i ∈ t, b j i)) ^ 2
  have hsum : (∑ j ∈ J, (L j) ^ 2) ≤ 2 * ∑ j ∈ J, E j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    exact jointFamily_affineFraction_parity_sq_le_two_energy
      (a₀ j) (b₀ j) (a j) (b j) (hb₀ j hj) (hb j hj) s hs
  calc
    _ ≤ (∑ j ∈ J, (τ j) ^ 2) * ∑ j ∈ J, (L j) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq J τ L
    _ ≤ (∑ j ∈ J, (τ j) ^ 2) * (2 * ∑ j ∈ J, E j) :=
      mul_le_mul_of_nonneg_left hsum (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
    _ = _ := by ring

end HeadComplexity
