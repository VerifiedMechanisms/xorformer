import HeadComplexity.Atoms.PartialFraction
import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Results.SymmetricComplexity
import Mathlib.LinearAlgebra.Lagrange

set_option linter.style.header false

/-!
# Exact scalar interpolation of Hamming-weight profiles

The sign-change construction uses one atom per alternation.  A different,
complementary interpolation result realizes an arbitrary real-valued profile
on Hamming weights `0, ..., n` exactly with `n` atoms.  This is the scalar
version of the Cauchy-basis construction used by Fourier certificate compilers.
-/

namespace HeadComplexity

open Finset Polynomial
open scoped BigOperators

variable {n : ℕ}

/-- Distinct positive shifts for exact Hamming-profile interpolation. -/
noncomputable def exactProfileShift (n : ℕ) (h : Fin n) : ℝ :=
  (n : ℝ) + 1 + (h : ℕ)

theorem exactProfileShift_pos (n : ℕ) (h : Fin n) :
    0 < exactProfileShift n h := by
  unfold exactProfileShift
  positivity

theorem exactProfileShift_injective (n : ℕ) :
    Function.Injective (exactProfileShift n) := by
  intro i j hij
  unfold exactProfileShift at hij
  have hcast : (i : ℝ) = (j : ℝ) := by linarith
  exact Fin.ext (Nat.cast_inj.mp hcast)

/-- Every real-valued Hamming profile has an exact constant-plus-reciprocal
representation with `n` shifts. -/
theorem exists_exact_hamming_reciprocals (target : Fin (n + 1) → ℝ) :
    ∃ (b : Fin n → ℝ) (c : ℝ), ∀ k : Fin (n + 1),
      c + ∑ h, b h / ((k : ℕ) + exactProfileShift n h) = target k := by
  classical
  let shift : Fin n → ℝ := exactProfileShift n
  let nodes : Fin (n + 1) → ℝ := fun k ↦ (k : ℕ)
  let denom : ℝ → ℝ := fun t ↦ ∏ h, (t + shift h)
  let values : Fin (n + 1) → ℝ := fun k ↦ target k * denom (nodes k)
  let P : ℝ[X] := Lagrange.interpolate Finset.univ nodes values
  have hnodes : Function.Injective nodes := by
    intro i j hij
    dsimp [nodes] at hij
    exact Fin.ext (Nat.cast_inj.mp hij)
  have hPdeg : P.natDegree ≤ n := by
    apply Polynomial.natDegree_le_iff_degree_le.mpr
    simpa [P] using
      (Lagrange.degree_interpolate_le
        (s := (Finset.univ : Finset (Fin (n + 1))))
        (r := values) hnodes.injOn)
  have hPeval : ∀ k : Fin (n + 1), P.eval (nodes k) = values k := by
    intro k
    simpa [P] using Lagrange.eval_interpolate_at_node
      (s := (Finset.univ : Finset (Fin (n + 1))))
      (v := nodes) (r := values) hnodes.injOn (Finset.mem_univ k)
  obtain ⟨c, b, hpartial⟩ :=
    real_partial_fraction P shift (exactProfileShift_injective n) hPdeg
  refine ⟨b, c, fun k ↦ ?_⟩
  have hpos : ∀ h : Fin n, 0 < nodes k + shift h := by
    intro h
    dsimp [nodes, shift]
    unfold exactProfileShift
    have hk : 0 ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hh : 0 ≤ ((h : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hprodpos : 0 < denom (nodes k) := by
    dsimp [denom]
    exact Finset.prod_pos fun h _ ↦ hpos h
  have hprodne : denom (nodes k) ≠ 0 := hprodpos.ne'
  have herase : ∀ h : Fin n,
      (∏ j ∈ Finset.univ.erase h, (nodes k + shift j)) ≠ 0 := by
    intro h
    exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ (hpos j).ne'
  have hfactor : ∀ h : Fin n,
      denom (nodes k) =
        (nodes k + shift h) *
          ∏ j ∈ Finset.univ.erase h, (nodes k + shift j) := by
    intro h
    dsimp [denom]
    exact (Finset.mul_prod_erase Finset.univ
      (fun j ↦ nodes k + shift j) (Finset.mem_univ h)).symm
  have hsum :
      (∑ h, b h / (nodes k + shift h)) =
        (∑ h, b h * ∏ j ∈ Finset.univ.erase h,
          (nodes k + shift j)) / denom (nodes k) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro h hh
    rw [hfactor h, mul_div_mul_right _ _ (herase h)]
  have hratio : c + ∑ h, b h / (nodes k + shift h) =
      P.eval (nodes k) / denom (nodes k) := by
    rw [hsum, hpartial (nodes k)]
    field_simp
    ring
  rw [hratio, hPeval]
  dsimp [values]
  field_simp [hprodne]

/-- Fractional atom realizing one reciprocal term in the exact profile. -/
noncomputable def exactHammingAtom (b : ℝ) (h : Fin n) : FracAtom n :=
  FracAtom.ofPositiveAffineRatio b (fun _ ↦ 0)
    (exactProfileShift n h) (fun _ ↦ 1)
    (exactProfileShift_pos n h) (fun _ ↦ one_pos)

@[simp] theorem exactHammingAtom_eval (b : ℝ) (h : Fin n)
    (bits : Fin n → Bool) :
    (exactHammingAtom b h).eval bits =
      b / ((hammingWeight bits : ℕ) + exactProfileShift n h) := by
  rw [exactHammingAtom, FracAtom.ofPositiveAffineRatio_eval]
  congr 1
  · simp [affineValue]
  · unfold affineValue hammingWeight
    simp only [one_mul]
    rw [← hammingWeight_eq_sum bits]
    simp [hammingWeight, add_comm]

/-- An arbitrary scalar Hamming profile is exactly a constant plus `n`
fractional atoms on the Boolean cube. -/
theorem exists_exact_hamming_atoms (target : Fin (n + 1) → ℝ) :
    ∃ (phi : Fin n → FracAtom n) (c : ℝ), ∀ bits,
      c + ∑ h, (phi h).eval bits =
        target ⟨hammingWeight bits,
          Nat.lt_succ_of_le (hammingWeight_le n bits)⟩ := by
  obtain ⟨b, c, hexact⟩ := exists_exact_hamming_reciprocals target
  refine ⟨fun h ↦ exactHammingAtom (b h) h, c, fun bits ↦ ?_⟩
  simpa using hexact
    ⟨hammingWeight bits, Nat.lt_succ_of_le (hammingWeight_le n bits)⟩

end HeadComplexity
