import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

/-- A reciprocal sum detects a cover when each covered point has one
small denominator and every uncovered point has all denominators large.
This does not assert existence of such a cover on the Boolean cube. -/
theorem reciprocal_sum_separates_gapped_cover
    {X ι : Type*} [Fintype ι]
    (B : ι → X → ℝ) (f : X → Bool) (s L τ : ℝ)
    (_hs : 0 < s) (hL : 0 < L)
    (hB : ∀ i x, 0 < B i x)
    (hcover : ∀ x, f x = true → ∃ i, B i x ≤ s)
    (houtside : ∀ x, f x = false → ∀ i, L ≤ B i x)
    (hlower : (Fintype.card ι : ℝ) / L < τ)
    (hupper : τ < 1 / s) :
    ∀ x, (f x = true → 0 < (∑ i, 1 / B i x) - τ) ∧
      (f x = false → (∑ i, 1 / B i x) - τ < 0) := by
  classical
  intro x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := hcover x hx
    have hrec : 1 / s ≤ 1 / B i x := one_div_le_one_div_of_le (hB i x) hi
    have hsum : 1 / B i x ≤ ∑ j, 1 / B j x := by
      exact Finset.single_le_sum (fun j _ => le_of_lt (one_div_pos.mpr (hB j x)))
        (Finset.mem_univ i)
    linarith
  · intro hx
    have hrec (i : ι) : 1 / B i x ≤ 1 / L :=
      one_div_le_one_div_of_le hL (houtside x hx i)
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrec i)
    have hid : (∑ _i : ι, (1 : ℝ) / L) = (Fintype.card ι : ℝ) / L := by
      simp [div_eq_mul_inv]
    rw [hid] at hsum
    linarith

/-- Clearing a common positive denominator preserves a strict halfspace
predicate. Thus a common projective feature map cannot avoid a parity
obstruction for unions of halfspaces. -/
theorem projective_halfspace_sign_iff
    {ι : Type*} [Fintype ι]
    (c D : ℝ) (w a : ι → ℝ) (hD : 0 < D) :
    0 < c + ∑ i, w i * (a i / D) ↔
      0 < c * D + ∑ i, w i * a i := by
  have hid : c + ∑ i, w i * (a i / D) =
      (c * D + ∑ i, w i * a i) / D := by
    simp [add_div, Finset.sum_div, mul_div_assoc, ne_of_gt hD]
  rw [hid]
  exact div_pos_iff_of_pos_right hD

end HeadComplexity
