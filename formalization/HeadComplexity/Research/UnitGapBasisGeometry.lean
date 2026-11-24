import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false

/-!
Elementary full-cube restrictions on a one-head unit-value interpolation basis.
These restrictions do not assert uniqueness of the full truth-table extension.
-/

noncomputable section
namespace HeadComplexity.UnitGapBasisGeometry
open scoped BigOperators

theorem affineValue_update_true {n : ℕ} (c : ℝ) (a : Fin n → ℝ)
    (x : Fin n → Bool) (i : Fin n) (hi : x i = false) :
    affineValue c a (Function.update x i true) = affineValue c a x + a i := by
  have hterm : ∀ j, a j * boolToReal (Function.update x i true j) =
      a j * boolToReal (x j) + if j = i then a i else 0 := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [hi, boolToReal]
    · simp [hji]
  simp only [affineValue, hterm, Finset.sum_add_distrib]
  simp
  ring

/-- A unit contact on the zero endpoint of an edge forces the numerator slope
to have at least the magnitude of the positive denominator slope. -/
theorem abs_slope_ge_of_zero_contact {n : ℕ}
    (a₀ b₀ : ℝ) (a b : Fin n → ℝ) (i : Fin n)
    (hgap : ∀ x, affineValue b₀ b x ≤ |affineValue a₀ a x|)
    (x : Fin n → Bool) (hxi : x i = false)
    (hcontact : |affineValue a₀ a x| = affineValue b₀ b x) :
    b i ≤ |a i| := by
  have hedge := hgap (Function.update x i true)
  rw [affineValue_update_true _ _ _ _ hxi,
      affineValue_update_true _ _ _ _ hxi] at hedge
  have habs := abs_add_le (affineValue a₀ a x) (a i)
  rw [hcontact] at habs
  linarith

/-- An affine spanning sample has a point on the zero face of every coordinate. -/
theorem exists_zero_coordinate_of_affine_spanning {n : ℕ} {ι : Type*}
    (points : ι → Fin n → Bool)
    (hspan : ∀ (c : ℝ) (a : Fin n → ℝ),
      (∀ j, affineValue c a (points j) = 0) → c = 0 ∧ a = 0)
    (i : Fin n) : ∃ j, points j i = false := by
  by_contra h
  push Not at h
  have hone : ∀ j, points j i = true := by
    intro j
    cases hi : points j i
    · exact False.elim (h j hi)
    · rfl
  have hzero : ∀ j, affineValue (-1) (fun k => if k = i then 1 else 0)
      (points j) = 0 := by
    intro j
    have hterm : ∀ k, (if k = i then 1 else 0 : ℝ) * boolToReal (points j k) =
        if k = i then 1 else 0 := by
      intro k
      by_cases hki : k = i
      · subst k
        simp [hone j, boolToReal]
      · simp [hki]
    simp only [affineValue, hterm]
    simp
  have hc := (hspan (-1) (fun k => if k = i then 1 else 0) hzero).1
  norm_num at hc

/-- Full Boolean unit feasibility together with an affine spanning family of
unit contacts controls every numerator slope. -/
theorem abs_slope_ge_of_affine_spanning_contacts {n : ℕ} {ι : Type*}
    (a₀ b₀ : ℝ) (a b : Fin n → ℝ) (points : ι → Fin n → Bool)
    (hgap : ∀ x, affineValue b₀ b x ≤ |affineValue a₀ a x|)
    (hcontact : ∀ j, |affineValue a₀ a (points j)| = affineValue b₀ b (points j))
    (hspan : ∀ (c : ℝ) (v : Fin n → ℝ),
      (∀ j, affineValue c v (points j) = 0) → c = 0 ∧ v = 0)
    (i : Fin n) : b i ≤ |a i| := by
  obtain ⟨j, hj⟩ := exists_zero_coordinate_of_affine_spanning points hspan i
  exact abs_slope_ge_of_zero_contact a₀ b₀ a b i hgap (points j) hj (hcontact j)

end HeadComplexity.UnitGapBasisGeometry
