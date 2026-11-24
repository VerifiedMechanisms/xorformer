import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
One-head full-unit-gap extensions from a fixed address face. One prescribed
unit-valued actual observation per new coordinate makes the full truth table
independent of all new denominator slopes, provided full unit feasibility holds.
The canonical zero-slope limit is used only as an algebraic certificate.
-/

noncomputable section
namespace HeadComplexity.OneHeadAddressExtension
open scoped BigOperators

variable {X : Type*} {k : ℕ}

def label (b : Bool) : ℝ := if b then 1 else -1

def canonicalNumerator (A B : X → ℝ) (contact : Fin k → X)
    (g : Fin k → Bool) (x : X) (y : Fin k → Bool) : ℝ :=
  A x + ∑ j, (label (g j) * B (contact j) - A (contact j)) * boolToReal (y j)

def numerator (A B : X → ℝ) (contact : Fin k → X)
    (g : Fin k → Bool) (q : Fin k → ℝ) (x : X) (y : Fin k → Bool) : ℝ :=
  canonicalNumerator A B contact g x y + ∑ j, label (g j) * q j * boolToReal (y j)

def denominator (B : X → ℝ) (q : Fin k → ℝ) (x : X)
    (y : Fin k → Bool) : ℝ := B x + ∑ j, q j * boolToReal (y j)

/-- The prescribed actual observations have exactly their signed unit values. -/
theorem contact_value (A B : X → ℝ) (contact : Fin k → X)
    (g : Fin k → Bool) (q : Fin k → ℝ) (j : Fin k) :
    numerator A B contact g q (contact j) (fun i => decide (i = j)) =
      label (g j) * denominator B q (contact j) (fun i => decide (i = j)) := by
  simp [numerator, canonicalNumerator, denominator, boolToReal]
  ring

theorem residual_eq (A B : X → ℝ) (contact : Fin k → X)
    (g : Fin k → Bool) (q : Fin k → ℝ) (x : X)
    (y : Fin k → Bool) (f : Bool) :
    label f * numerator A B contact g q x y - denominator B q x y =
      label f * canonicalNumerator A B contact g x y - B x +
        ∑ j, (label f * label (g j) - 1) * q j * boolToReal (y j) := by
  unfold numerator denominator
  rw [mul_add, Finset.mul_sum]
  have hs : (∑ j, (label f * label (g j) - 1) * q j * boolToReal (y j)) =
      (∑ j, label f * (label (g j) * q j * boolToReal (y j))) -
        ∑ j, q j * boolToReal (y j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  ring

/-- Lowering the new denominator slopes increases every correctly signed residual. -/
theorem residual_mono (A B : X → ℝ) (contact : Fin k → X)
    (g : Fin k → Bool) (q q' : Fin k → ℝ) (hqq : ∀ j, q' j ≤ q j)
    (x : X) (y : Fin k → Bool) (f : Bool) :
    label f * numerator A B contact g q x y - denominator B q x y ≤
      label f * numerator A B contact g q' x y - denominator B q' x y := by
  rw [residual_eq, residual_eq]
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro j _
  have hc : label f * label (g j) - 1 ≤ 0 := by
    cases f <;> cases hgj : g j <;> norm_num [label, hgj]
  have hy : 0 ≤ boolToReal (y j) := by cases hyj : y j <;> norm_num [boolToReal, hyj]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonpos_left (hqq j) hc) hy

/-- A positive old denominator prevents a zero score in the canonical limit. -/
theorem canonical_signed_gap (A B : X → ℝ) (contact : Fin k → X)
    (g : Fin k → Bool) (q : Fin k → ℝ) (hq : ∀ j, 0 ≤ q j)
    (x : X) (y : Fin k → Bool) (f : Bool)
    (hf : denominator B q x y ≤ label f * numerator A B contact g q x y) :
    B x ≤ label f * canonicalNumerator A B contact g x y := by
  have hm := residual_mono A B contact g q (fun _ => 0) hq x y f
  simp only [numerator, denominator, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero] at hm
  dsimp only [numerator, denominator] at hf
  linarith

/-- Any two fully unit-feasible extensions of the same fixed address data agree. -/
theorem feasible_labels_unique (A B : X → ℝ) (contact : Fin k → X)
    (g : Fin k → Bool) (q q' : Fin k → ℝ)
    (hq : ∀ j, 0 ≤ q j) (hq' : ∀ j, 0 ≤ q' j)
    (x : X) (y : Fin k → Bool) (hB : 0 < B x) (f f' : Bool)
    (hf : denominator B q x y ≤ label f * numerator A B contact g q x y)
    (hf' : denominator B q' x y ≤ label f' * numerator A B contact g q' x y) :
    f = f' := by
  have hc := canonical_signed_gap A B contact g q hq x y f hf
  have hc' := canonical_signed_gap A B contact g q' hq' x y f' hf'
  cases f <;> cases f' <;> simp_all [label] <;> linarith

/-- Every positive smaller choice of slopes keeps the same full unit-gap table. -/
theorem full_gap_preserved (A B : X → ℝ) (contact : Fin k → X)
    (g : Fin k → Bool) (q q' : Fin k → ℝ) (hqq : ∀ j, q' j ≤ q j)
    (f : X → (Fin k → Bool) → Bool)
    (hf : ∀ x y, denominator B q x y ≤
      label (f x y) * numerator A B contact g q x y) :
    ∀ x y, denominator B q' x y ≤ label (f x y) * numerator A B contact g q' x y := by
  intro x y
  have hm := residual_mono A B contact g q q' hqq x y (f x y)
  have hx := hf x y
  linarith

end HeadComplexity.OneHeadAddressExtension
