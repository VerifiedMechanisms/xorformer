import Mathlib.Tactic
import Mathlib.LinearAlgebra.Span.Basic

/-! Local algebra and the separating-functional step of Boolean moment-circuit
surgery. The general induction is stated and proved in the companion writeup. -/

namespace HeadComplexity.MomentCircuitSurgery

theorem replacement_identity (D e : ℝ) (x y : Bool) :
    1 / D =
      -(1 / (D + e * ((if x then 1 else 0) + (if y then 1 else 0)))) +
      1 / (D + e * (2 * (if y then 1 else 0))) +
      1 / (D + e * (if x then 1 else 0)) -
      1 / (D + e * (-(if x then 1 else 0) + 2 * (if y then 1 else 0))) +
      1 / (D + e * (-(if x then 1 else 0) + (if y then 1 else 0))) := by
  cases x <;> cases y <;> norm_num; ring

theorem replacement_affine {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p u v : M) (T : R) :
    -(p + T • (u + v)) + (p + (2 * T) • v) + (p + T • u) -
      (p + T • (-u + 2 • v)) + (p + T • (-u + v)) = p := by
  module

theorem offset_moments_force (T a b e f : ℝ) (hT : T ≠ 0)
    (h₁ : T * (a + 2 * b + 2 * e + f) = 0)
    (h₂ : T ^ 2 * (a + 4 * b + 4 * e + f) = 0)
    (h₃ : T ^ 2 * (a - 2 * e - f) = 0) :
    a = e ∧ b = -a ∧ f = -a := by
  have q₁ := (mul_eq_zero.mp h₁).resolve_left hT
  have q₂ := (mul_eq_zero.mp h₂).resolve_left (pow_ne_zero 2 hT)
  have q₃ := (mul_eq_zero.mp h₃).resolve_left (pow_ne_zero 2 hT)
  constructor
  · linarith
  constructor <;> linarith

theorem first_offset_expansion (L T a b e f : ℝ) :
    a * ((L + T) - L) + b * ((L + 2 * T) - L) +
      e * ((L + 2 * T) - L) + f * ((L + T) - L) =
      T * (a + 2 * b + 2 * e + f) := by ring

theorem second_offset_expansion (L T a b e f : ℝ) :
    a * ((L + T) ^ 2 - L ^ 2) + b * ((L + 2 * T) ^ 2 - L ^ 2) +
      e * ((L + 2 * T) ^ 2 - L ^ 2) + f * ((L + T) ^ 2 - L ^ 2) -
      2 * L * (T * (a + 2 * b + 2 * e + f)) =
      T ^ 2 * (a + 4 * b + 4 * e + f) := by ring

theorem pair_offset_expansion (P T a b e f : ℝ) :
    a * ((P + 2 * T) ^ 2 - (P + T) ^ 2) +
      b * ((P + 2 * T) ^ 2 - P ^ 2) +
      e * ((P + T) ^ 2 - (P - T) ^ 2) +
      f * (P ^ 2 - (P - T) ^ 2) -
      2 * P * (T * (a + 2 * b + 2 * e + f)) -
      T ^ 2 * (a + 4 * b + 4 * e + f) =
      2 * T ^ 2 * (a - 2 * e - f) := by ring

theorem outside_span_coefficient {M : Type*} [AddCommGroup M] [Module ℝ M]
    (U : Submodule ℝ M) (w y : M) (hw : w ∉ U) (hy : y ∈ U)
    (a : ℝ) (h : y + a • w = 0) : a = 0 := by
  by_contra ha
  have he : a • w = -y := (eq_neg_iff_add_eq_zero).mpr (by simpa [add_comm] using h)
  have hm : a • w ∈ U := he ▸ U.neg_mem hy
  have hh := U.smul_mem (a⁻¹) hm
  apply hw
  simpa [smul_smul, ha] using hh

theorem relation_rewrite {M : Type*} [AddCommGroup M] [Module ℝ M]
    (p A B C E F : M) (h : p = -A + B + C - E + F) (t s : ℝ) :
    t • A + (-t) • B + s • C + t • E + (-t) • F =
      (-t) • p + (s + t) • C := by
  rw [h]
  module

end HeadComplexity.MomentCircuitSurgery
