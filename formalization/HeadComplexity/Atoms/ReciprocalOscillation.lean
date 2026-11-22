import HeadComplexity.Atoms.PositiveStatisticRawBit

set_option linter.style.header false

/-!
# Oscillation of linear functionals of positive reciprocal evaluations

This file records an obstruction to a proposed lower-bound shortcut. A linear
functional of the vector `(1 / (t + a j)) j` can have any prescribed `K` roots
in the positive `t` domain, even when all shifts are nonnegative and distinct.
It is not a lower bound on attention-head complexity.
-/

namespace HeadComplexity

open Finset Polynomial
open scoped BigOperators

/-- Partial fractions with `K + 1` nonnegative distinct shifts realize every
monic polynomial with `K` prescribed roots, divided by the positive common
denominator. The coefficients of the linear functional may have either sign. -/
theorem exists_reciprocal_prescribed_roots_identity {K : ℕ}
    (a : Fin (K + 1) → ℝ) (ha : Function.Injective a)
    (ha_nonneg : ∀ j, 0 ≤ a j) (r : Fin K → ℝ) :
    ∃ b : Fin (K + 1) → ℝ, ∀ t : ℝ, 0 < t →
      (∑ j, b j / (t + a j)) =
        (∏ i, (t - r i)) / (∏ j, (t + a j)) := by
  classical
  let P : ℝ[X] := ∏ i : Fin K, (X - C (r i))
  have hdeg : P.natDegree = K := by
    dsimp [P]
    rw [natDegree_prod _ _ (fun i _ ↦ (monic_X_sub_C (r i)).ne_zero)]
    simp
  have htop : P.coeff (K + 1) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    omega
  obtain ⟨b, hb⟩ := real_partial_fraction_coeff P a ha (by omega)
  refine ⟨b, fun t ht ↦ ?_⟩
  have hpos : ∀ j, 0 < t + a j := fun j ↦ add_pos_of_pos_of_nonneg ht (ha_nonneg j)
  have herase : ∀ h : Fin (K + 1),
      (∏ j ∈ Finset.univ.erase h, (t + a j)) ≠ 0 := by
    intro h
    exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ (hpos j).ne'
  have hfactor : ∀ h : Fin (K + 1),
      (∏ j, (t + a j)) =
        (t + a h) * ∏ j ∈ Finset.univ.erase h, (t + a j) := by
    intro h
    exact (Finset.mul_prod_erase Finset.univ
      (fun j ↦ t + a j) (Finset.mem_univ h)).symm
  have hsum : (∑ j, b j / (t + a j)) =
      (∑ h, b h * ∏ j ∈ Finset.univ.erase h, (t + a j)) /
        (∏ j, (t + a j)) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro h _
    rw [hfactor h, mul_div_mul_right _ _ (herase h)]
  have hpoly : P.eval t =
      ∑ h, b h * ∏ j ∈ Finset.univ.erase h, (t + a j) := by
    simpa [htop] using hb t
  rw [hsum, ← hpoly]
  congr 1
  simp [P, Polynomial.eval_prod]

/-- Exactly the prescribed positive roots occur. In particular, no bound
independent of the number of evaluation coordinates follows from positivity
of the shifts alone. -/
theorem exists_reciprocal_prescribed_positive_zeros {K : ℕ}
    (a : Fin (K + 1) → ℝ) (ha : Function.Injective a)
    (ha_nonneg : ∀ j, 0 ≤ a j) (r : Fin K → ℝ) :
    ∃ b : Fin (K + 1) → ℝ, ∀ t : ℝ, 0 < t →
      ((∑ j, b j / (t + a j)) = 0 ↔ ∃ i, t = r i) := by
  classical
  obtain ⟨b, hb⟩ := exists_reciprocal_prescribed_roots_identity a ha ha_nonneg r
  refine ⟨b, fun t ht ↦ ?_⟩
  have hden : (∏ j, (t + a j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact (add_pos_of_pos_of_nonneg ht (ha_nonneg j)).ne'
  rw [hb t ht, div_eq_zero_iff]
  simp [hden, Finset.prod_eq_zero_iff, sub_eq_zero]

end HeadComplexity
