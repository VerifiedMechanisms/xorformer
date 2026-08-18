import HeadComplexity.Atoms.FracAtomHead
import Mathlib.Probability.Moments.SubGaussian

set_option linter.style.header false

/-!
# Output-normalized atomic-margin certificates

This module packages finite convex combinations of genuine fractional atoms,
normalized in output space. It also records the elementary operation which
absorbs a real coefficient into an atom's readout parameters.
-/

namespace HeadComplexity

open Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

variable {n : ℕ}

namespace FracAtom

/-- Multiply an atom's output by an arbitrary real scalar. The positive
attention parameters and denominator are unchanged. -/
noncomputable def scale (a : ℝ) (phi : FracAtom n) : FracAtom n where
  η := a * phi.η
  δ := a * phi.δ
  γ := phi.γ
  α := phi.α
  ρ := phi.ρ
  m := fun i ↦ a * phi.m i
  hγ := phi.hγ
  hα := phi.hα
  hρ := phi.hρ

@[simp] theorem scale_eval (a : ℝ) (phi : FracAtom n)
    (bits : Fin n → Bool) :
    (phi.scale a).eval bits = a * phi.eval bits := by
  unfold eval scale
  simp only [wt]
  have hden :
      phi.γ + ∑ i, phi.ρ i * (if bits i then phi.α else 1) ≠ 0 := by
    simpa [wt] using (phi.denom_pos bits).ne'
  rw [← mul_div_assoc]
  rw [div_eq_div_iff hden hden]
  congr 1
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split <;> ring

end FracAtom

/-- The `±1` label associated with a Boolean predicate. -/
def signedLabel (f : (Fin n → Bool) → Bool) (bits : Fin n → Bool) : ℝ :=
  if f bits then 1 else -1

@[simp] theorem signedLabel_of_true
    {f : (Fin n → Bool) → Bool} {bits : Fin n → Bool}
    (h : f bits = true) : signedLabel f bits = 1 := by
  simp [signedLabel, h]

@[simp] theorem signedLabel_of_false
    {f : (Fin n → Bool) → Bool} {bits : Fin n → Bool}
    (h : f bits = false) : signedLabel f bits = -1 := by
  simp [signedLabel, h]

theorem abs_signedLabel (f : (Fin n → Bool) → Bool)
    (bits : Fin n → Bool) :
    |signedLabel f bits| = 1 := by
  cases h : f bits <;> simp [signedLabel, h]

/-- The output-space average of a finite family of atoms under a probability
measure on its index type. -/
noncomputable def atomicAverage {J : Type*} [MeasurableSpace J]
    (mu : Measure J) (atom : J → FracAtom n) (bits : Fin n → Bool) : ℝ :=
  ∫ j, (atom j).eval bits ∂mu

/-- A faithful finite convex atomic-margin certificate. The probability
measure supplies the convex weights, and every atom is normalized by its
actual output vector on the Boolean cube. -/
structure AtomicMarginCertificate
    (f : (Fin n → Bool) → Bool) (J : Type*) [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure J) [IsProbabilityMeasure mu] where
  atom : J → FracAtom n
  normalized : ∀ j bits, |(atom j).eval bits| ≤ 1
  bias : ℝ
  scale : ℝ
  margin : ℝ
  scale_pos : 0 < scale
  margin_pos : 0 < margin
  separates : ∀ bits,
    margin ≤ signedLabel f bits *
      (bias + scale * atomicAverage mu atom bits)

namespace AtomicMarginCertificate

variable {J : Type*} [Fintype J] [MeasurableSpace J]
  [MeasurableSingletonClass J] {mu : Measure J} [IsProbabilityMeasure mu]
  {f : (Fin n → Bool) → Bool}

/-- A selected empirical average with a positive signed margin is an exact
head representation. Each common coefficient is absorbed into its atom. -/
theorem computableWithHeadsN_of_empirical_margin
    (C : AtomicMarginCertificate f J mu) {m : ℕ}
    (sample : Fin m → J)
    (hmargin : ∀ bits,
      0 < signedLabel f bits *
        (C.bias + (C.scale / (m : ℝ)) *
          ∑ i, (C.atom (sample i)).eval bits)) :
    computableWithHeadsN n m f := by
  apply computable_of_fracComputable
  let phi : Fin m → FracAtom n :=
    fun i ↦ (C.atom (sample i)).scale (C.scale / (m : ℝ))
  refine ⟨phi, C.bias, fun bits ↦ ?_⟩
  have hscore :
      C.bias + ∑ i, (phi i).eval bits =
        C.bias + (C.scale / (m : ℝ)) *
          ∑ i, (C.atom (sample i)).eval bits := by
    dsimp [phi]
    simp_rw [FracAtom.scale_eval]
    rw [Finset.mul_sum]
  rw [hscore]
  cases hbit : f bits with
  | false =>
      have hsigned := hmargin bits
      rw [signedLabel_of_false hbit] at hsigned
      constructor
      · intro hpos
        linarith
      · intro h
        exact (Bool.false_ne_true h).elim
  | true =>
      have hsigned := hmargin bits
      rw [signedLabel_of_true hbit, one_mul] at hsigned
      exact ⟨fun _ ↦ rfl, fun _ ↦ hsigned⟩

end AtomicMarginCertificate

end HeadComplexity
