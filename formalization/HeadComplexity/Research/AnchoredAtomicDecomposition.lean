import HeadComplexity.Atoms.AffineMonomialApproximation
import HeadComplexity.Atoms.FracAtomSymmetry

set_option linter.style.header false

/-!
# Anchored affine blocks and coefficient mass

The complete positive reciprocal expansion is given in the companion written
proof. This module checks two ingredients without assuming a quantitative
margin: genuine one-head approximation of every affine block on a negative
face, and the full-cube mass estimate from the reciprocal expansion's endpoint
identities. It also checks the scalar-feature coefficient mass estimate.
-/

namespace HeadComplexity.AnchoredAtomicDecomposition

open Finset
open scoped BigOperators

variable {n : ℕ}

theorem affineValue_flipBits (a : ℝ) (u : Fin n → ℝ)
    (x : Fin n → Bool) :
    affineValue (a + ∑ i, u i) (fun i ↦ -u i) (flipBits x) =
      affineValue a u x := by
  have hbit : ∀ i, boolToReal (flipBits x i) = 1 - boolToReal (x i) := by
    intro i
    cases hx : x i <;> simp [flipBits, boolToReal, hx]
  unfold affineValue
  simp_rw [hbit, neg_mul, mul_sub, mul_one]
  rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  ring

/-- A negative face indicator times an arbitrary affine numerator remains
uniformly approximable by one genuine original-model head. -/
theorem uniformlyOneAtomApproximable_negativeFace_affine
    (S : Finset (Fin n)) (a : ℝ) (u : Fin n → ℝ) :
    UniformlyOneAtomApproximable
      (fun x ↦ squarefreeMonomial S (flipBits x) * affineValue a u x) := by
  intro ε hε
  obtain ⟨φ, hφ⟩ := exists_fracAtom_approx_monomial_mul_affineValue
    S (a + ∑ i, u i) (fun i ↦ -u i) ε hε
  refine ⟨φ.flip, fun x ↦ ?_⟩
  simpa only [FracAtom.flip_eval, affineValue_flipBits] using hφ (flipBits x)

/-- The coefficient mass of the scalar-feature expansion is controlled using
only the values at the zero input and singleton inputs, with all denominators
positive. The companion proof obtains these hypotheses from the full-cube
norm of the original head. -/
theorem scalar_coefficient_mass_le
    (c M a : ℝ) (w u : Fin n → ℝ)
    (hc : 0 < c) (hM : 0 ≤ M) (hw : ∀ i, 0 ≤ w i)
    (ha : |a| ≤ M * c)
    (hui : ∀ i, |a + u i| ≤ M * (c + w i)) :
    |a| / c + ∑ i, |u i| / (c + w i) ≤ (2 * (n : ℝ) + 1) * M := by
  have hbase : |a| / c ≤ M := (div_le_iff₀ hc).2 ha
  have hterm : ∀ i, |u i| / (c + w i) ≤ 2 * M := by
    intro i
    have hden : 0 < c + w i := add_pos_of_pos_of_nonneg hc (hw i)
    apply (div_le_iff₀ hden).2
    have habs : |u i| ≤ |a + u i| + |a| := by
      calc
        |u i| = |(a + u i) - a| := by congr 1; ring
        _ ≤ |a + u i| + |a| := abs_sub _ _
    nlinarith [hui i, mul_nonneg hM (hw i)]
  calc
    |a| / c + ∑ i, |u i| / (c + w i) ≤ M + ∑ _i : Fin n, 2 * M :=
      add_le_add hbase (Finset.sum_le_sum fun i _ ↦ hterm i)
    _ = (2 * (n : ℝ) + 1) * M := by simp; ring

/-- Endpoint identities for a reciprocal expansion give an exact weighted
mass identity for the whole affine face blocks. This theorem does not assume
that the coefficients are nonnegative; positivity is needed only when using
the identity to bound the norms of those blocks. -/
theorem face_coefficient_mass_eq
    (c : ℝ) (w : Fin n → ℝ) (κ : Finset (Fin n) → ℝ)
    (hc : c ≠ 0)
    (hzero : ∑ S : Finset (Fin n), κ S = 1 / c)
    (hsingleton : ∀ i, ∑ S : Finset (Fin n),
      (if i ∉ S then κ S else 0) = 1 / (c + w i)) :
    (∑ S : Finset (Fin n), κ S *
      (c + ∑ i : Fin n, if i ∉ S then w i else 0)) =
        1 + ∑ i : Fin n, w i / (c + w i) := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hzero]
  have hfirst : (1 / c) * c = 1 := by field_simp
  rw [hfirst]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hterm : ∀ S : Finset (Fin n),
      κ S * (if i ∉ S then w i else 0) =
        w i * (if i ∉ S then κ S else 0) := by
    intro S
    split_ifs <;> ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, hsingleton]
  ring

/-- The weighted face coefficient mass is at most `n+1`, independent of the
denominator's condition number. -/
theorem face_coefficient_mass_le
    (c : ℝ) (w : Fin n → ℝ) (κ : Finset (Fin n) → ℝ)
    (hc : 0 < c) (hw : ∀ i, 0 ≤ w i)
    (hzero : ∑ S : Finset (Fin n), κ S = 1 / c)
    (hsingleton : ∀ i, ∑ S : Finset (Fin n),
      (if i ∉ S then κ S else 0) = 1 / (c + w i)) :
    (∑ S : Finset (Fin n), κ S *
      (c + ∑ i : Fin n, if i ∉ S then w i else 0)) ≤ (n : ℝ) + 1 := by
  rw [face_coefficient_mass_eq c w κ hc.ne' hzero hsingleton]
  have hterm : ∀ i, w i / (c + w i) ≤ 1 := by
    intro i
    apply (div_le_one (add_pos_of_pos_of_nonneg hc (hw i))).2
    linarith
  calc
    1 + ∑ i : Fin n, w i / (c + w i) ≤ 1 + ∑ _i : Fin n, (1 : ℝ) :=
      add_le_add_right (Finset.sum_le_sum fun i _ ↦ hterm i) 1
    _ = (n : ℝ) + 1 := by simp; ring

end HeadComplexity.AnchoredAtomicDecomposition
