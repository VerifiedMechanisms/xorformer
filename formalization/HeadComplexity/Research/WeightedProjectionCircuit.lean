import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false

/-!
An eleven-point minimal Boolean projection circuit with a primitive coefficient
of magnitude two. Iterated separated gluing is described in the accompanying
note; only the base circuit and its uniqueness are formalized here.
-/
noncomputable section
namespace HeadComplexity.WeightedProjectionCircuit
open Finset
open scoped BigOperators

def left : Fin 11 → ℝ := ![3, 2, 3, 0, 2, 0, 1, 0, 2, 2, 1]
def right : Fin 11 → ℝ := ![1, 1, 2, 1, 3, 2, 0, 3, 0, 2, 1]
def coeff : Fin 11 → ℝ := ![-1, -1, 1, 1, -1, -2, -1, 1, 1, 1, 1]

/-- All scalar-kernel projections vanish, including every moment and every
reciprocal with an arbitrary common base. -/
theorem scalar_kernel_identity (F : ℝ → ℝ) (x y : Bool) :
    ∑ i, coeff i * F (left i * boolToReal x + right i * boolToReal y) = 0 := by
  cases x <;> cases y <;>
    norm_num [left, right, coeff, Fin.sum_univ_succ, boolToReal] <;> ring

/-- The universal relation is one-dimensional, with scale equal to the
coefficient of the third support point. -/
theorem constant_residue_identity_unique (c : Fin 11 → ℝ)
    (h : ∀ (F : ℝ → ℝ) (x y : Bool),
      ∑ i, c i * F (left i * boolToReal x + right i * boolToReal y) = 0) :
    ∀ i, c i = c 2 * coeff i := by
  have r0 := h (fun t => if t = 0 then 1 else 0) true false
  have r1 := h (fun t => if t = 1 then 1 else 0) true false
  have r2 := h (fun t => if t = 2 then 1 else 0) true false
  have r3 := h (fun t => if t = 3 then 1 else 0) true false
  have c0 := h (fun t => if t = 0 then 1 else 0) false true
  have c1 := h (fun t => if t = 1 then 1 else 0) false true
  have c2 := h (fun t => if t = 2 then 1 else 0) false true
  have c3 := h (fun t => if t = 3 then 1 else 0) false true
  have d1 := h (fun t => if t = 1 then 1 else 0) true true
  have d2 := h (fun t => if t = 2 then 1 else 0) true true
  have d3 := h (fun t => if t = 3 then 1 else 0) true true
  have d4 := h (fun t => if t = 4 then 1 else 0) true true
  have d5 := h (fun t => if t = 5 then 1 else 0) true true
  norm_num [left, right, Fin.sum_univ_succ, boolToReal] at r0 r1 r2 r3 c0 c1 c2 c3
  norm_num [left, right, Fin.sum_univ_succ, boolToReal] at d1 d2 d3 d4 d5
  intro i
  fin_cases i <;> norm_num [coeff] <;> linarith

/-- Every displayed coefficient is nonzero, so uniqueness excludes a relation
supported on a proper subset. -/
theorem coeff_ne_zero (i : Fin 11) : coeff i ≠ 0 := by
  fin_cases i <;> norm_num [coeff]

/-- A universal relation vanishing at one support point vanishes everywhere. -/
theorem no_proper_support_relation (c : Fin 11 → ℝ)
    (h : ∀ (F : ℝ → ℝ) (x y : Bool),
      ∑ i, c i * F (left i * boolToReal x + right i * boolToReal y) = 0)
    (i : Fin 11) (hi : c i = 0) : ∀ j, c j = 0 := by
  have hc := constant_residue_identity_unique c h
  have hz : c 2 = 0 := by
    have hh := hc i
    rw [hi] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_right (coeff_ne_zero i)
  intro j
  rw [hc j, hz, zero_mul]

/-- The primitive base circuit has the unequal ratio used by the gluing
construction. -/
theorem distinguished_coefficients : coeff 2 = 1 ∧ coeff 5 = -2 := by
  norm_num [coeff]

end HeadComplexity.WeightedProjectionCircuit
