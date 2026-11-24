import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Arrowhead completion and a diagonal congruence obstruction

The completion identity is the Schur-complement calculation behind reciprocal
scores. The monomial-matrix theorem audits constant congruences that preserve
the diagonal leaf block for independent denominator coefficients. Neither
result asserts a Boolean head-complexity separation.
-/

namespace HeadComplexity.RoPEArrowhead

open scoped BigOperators

variable {H : ℕ}

/-- Completing the squares isolates the reciprocal score in an arrowhead
quadratic form. -/
theorem complete_squares (d a y : Fin H → ℝ) (c t : ℝ)
    (hd : ∀ h, d h ≠ 0) :
    c * t ^ 2 + 2 * t * (∑ h, a h * y h) + ∑ h, d h * y h ^ 2 =
      (c - ∑ h, a h ^ 2 / d h) * t ^ 2 +
        ∑ h, d h * (y h + a h * t / d h) ^ 2 := by
  have he (h : Fin H) :
      d h * (y h + a h * t / d h) ^ 2 =
        d h * y h ^ 2 + 2 * t * (a h * y h) + (a h ^ 2 / d h) * t ^ 2 := by
    field_simp [hd h]
    ring
  simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- For positive leaf diagonals, negativity of the Schur complement is exactly
negativity of the arrowhead quadratic form on some vector with query entry one. -/
theorem exists_negative_iff (d a : Fin H → ℝ) (c : ℝ)
    (hd : ∀ h, 0 < d h) :
    (∃ y : Fin H → ℝ,
      c + 2 * (∑ h, a h * y h) + ∑ h, d h * y h ^ 2 < 0) ↔
        c - ∑ h, a h ^ 2 / d h < 0 := by
  constructor
  · rintro ⟨y, hy⟩
    have he := complete_squares d a y c 1 (fun h ↦ (hd h).ne')
    have hs : 0 ≤ ∑ h, d h * (y h + a h / d h) ^ 2 :=
      Finset.sum_nonneg fun h _ ↦ mul_nonneg (hd h).le (sq_nonneg _)
    simp only [one_pow, mul_one] at he
    linarith
  · intro hc
    refine ⟨fun h ↦ -a h / d h, ?_⟩
    have he := complete_squares d a (fun h ↦ -a h / d h) c 1
      (fun h ↦ (hd h).ne')
    simp only [one_pow, mul_one, neg_div, neg_add_cancel, zero_pow (by omega : 2 ≠ 0),
      mul_zero, Finset.sum_const_zero, add_zero] at he
    simpa only [neg_div] using he.trans_lt hc

/-- An invertible matrix whose distinct columns have coordinatewise disjoint
support is a permutation times a nonzero diagonal matrix. -/
theorem monomial_of_coordinate_separated (B : Matrix (Fin H) (Fin H) ℝ)
    (hdet : B.det ≠ 0)
    (hsep : ∀ i j k, j ≠ k → B i j * B i k = 0) :
    ∃ e : Equiv.Perm (Fin H), ∀ j,
      B (e j) j ≠ 0 ∧ ∀ i, i ≠ e j → B i j = 0 := by
  classical
  have hcol (j : Fin H) : ∃ i, B i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hdet (Matrix.det_eq_zero_of_column_eq_zero j h)
  choose g hg using hcol
  have hinj : Function.Injective g := by
    intro j k heq
    by_contra hne
    have hz := hsep (g j) j k hne
    have hk : B (g j) k ≠ 0 := by simpa only [heq] using hg k
    exact (mul_ne_zero (hg j) hk) hz
  have hbij : Function.Bijective g := ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨Equiv.ofBijective g hbij, fun j ↦ ⟨hg j, ?_⟩⟩
  intro i hij
  obtain ⟨k, rfl⟩ := hbij.2 i
  have hkj : k ≠ j := by
    intro heq
    subst k
    exact hij rfl
  exact (mul_eq_zero.mp (hsep (g k) k j hkj)).resolve_left (hg k)

/-- Under the preceding support condition, congruence cannot mix the original
diagonal coefficient directions: each new diagonal is a positive scalar
multiple of one old coefficient. -/
theorem diagonal_coefficients_permuted (B : Matrix (Fin H) (Fin H) ℝ)
    (hdet : B.det ≠ 0)
    (hsep : ∀ i j k, j ≠ k → B i j * B i k = 0) :
    ∃ e : Equiv.Perm (Fin H), ∀ j,
      0 < (B (e j) j) ^ 2 ∧ ∀ d : Fin H → ℝ,
        (∑ i, (B i j) ^ 2 * d i) = (B (e j) j) ^ 2 * d (e j) := by
  classical
  obtain ⟨e, he⟩ := monomial_of_coordinate_separated B hdet hsep
  refine ⟨e, fun j ↦ ⟨sq_pos_of_ne_zero (he j).1, fun d ↦ ?_⟩⟩
  apply Finset.sum_eq_single (e j)
  · intro i _ hij
    rw [(he j).2 i hij]
    simp
  · simp

end HeadComplexity.RoPEArrowhead
