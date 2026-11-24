import HeadComplexity.Results.JointCellFilteredKernels

set_option linter.style.header false

/-!
The exact feature family obtained by filtering one admissible affine-numerator
reciprocal head. This supplies c+1 scalar features on a c-coordinate face
without compiling c separate heads. It asserts no bit-decoding theorem.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- The full Boolean difference of an affine-numerator reciprocal. -/
noncomputable def jointCellAffineFilteredKernel (s : Finset ι) (w v : ι → ℝ)
    (d a : ℝ) : ℝ :=
  (-1 : ℝ) ^ s.card * faceAlternation s
    (fun t ↦ (a + ∑ i ∈ t, v i) / (d - ∑ i ∈ t, w i))

/-- An affine numerator gives the full reciprocal filter and all immediate
proper-face reciprocal filters. The coefficients are arbitrary. -/
theorem jointCell_affine_filtered_kernel_eq (s : Finset ι) (w v : ι → ℝ)
    (d a : ℝ) :
    jointCellAffineFilteredKernel s w v d a =
      (a + ∑ i ∈ s, v i) * jointCellFilteredKernel s w d +
        ∑ i ∈ s, v i * jointCellFilteredKernel (s.erase i) w d := by
  let f : Finset ι → ℝ := fun t ↦ 1 / (d - ∑ i ∈ t, w i)
  have hprod := faceAlternation_affine_mul s a v f
  have he : faceAlternation s (fun t ↦ (a + ∑ i ∈ t, v i) /
      (d - ∑ i ∈ t, w i)) =
      (a + ∑ i ∈ s, v i) * faceAlternation s f -
        ∑ i ∈ s, v i * faceAlternation (s.erase i) f := by
    simpa only [f, div_eq_mul_inv, one_mul] using hprod
  unfold jointCellAffineFilteredKernel jointCellFilteredKernel
  rw [he, mul_sub, Finset.mul_sum]
  have hterm : ∀ i ∈ s,
      -((-1 : ℝ) ^ s.card * (v i * faceAlternation (s.erase i) f)) =
        v i * ((-1 : ℝ) ^ (s.erase i).card * faceAlternation (s.erase i) f) := by
    intro i hi
    have hc : s.card = (s.erase i).card + 1 := by
      rw [Finset.card_erase_of_mem hi]
      have := Finset.card_pos.mpr (show s.Nonempty from ⟨i, hi⟩)
      omega
    rw [hc, pow_succ]
    ring
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    exact hterm

/-- Nonnegative affine-numerator coefficients cannot supply a bit switch:
all these filtered outputs are strictly positive when the constant is
positive and every denominator has a full-cube margin. -/
theorem jointCell_affine_filtered_kernel_pos (s : Finset ι) (w v : ι → ℝ)
    (d a : ℝ) (ha : 0 < a) (hw : ∀ i ∈ s, 0 < w i)
    (hv : ∀ i ∈ s, 0 ≤ v i) (hd : ∑ i ∈ s, w i < d) :
    0 < jointCellAffineFilteredKernel s w v d a := by
  rw [jointCell_affine_filtered_kernel_eq]
  apply add_pos_of_pos_of_nonneg
  · apply mul_pos
    · exact add_pos_of_pos_of_nonneg ha (Finset.sum_nonneg hv)
    · exact jointCell_filtered_kernel_pos s w d hw hd
  · apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg (hv i hi)
    apply le_of_lt
    apply jointCell_filtered_kernel_pos
    · intro j hj
      exact hw j (Finset.mem_of_mem_erase hj)
    · have hle : (∑ j ∈ s.erase i, w j) ≤ ∑ j ∈ s, w j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i s)
          (fun j hj _ ↦ (hw j hj).le)
      exact hle.trans_lt hd

end HeadComplexity.AxisZeroGluing
