import TheoremSubsumption

import HeadComplexity.Results.AtomicMarginRefinement

set_option linter.style.header false

/-!
# Certified comparison of the refined theorem-195 bound

The sampling contract has a checked bridge from genuine atomic-margin
certificates. Its fields assert normalization and the sampling rule, not the
real-valued bound being compared. The context-free numeric refutation below
does not assert the existence of a Boolean function with those numeric data.
-/

namespace HeadComplexity.AtomicMarginSubsumption

open Lean Meta Elab TheoremSubsumption

/-- Arithmetic implication, independent of either compared declaration. -/
theorem refined_implies_legacy (n heads : ℕ) (ratio : ℝ) :
    (heads : ℝ) ≤ 3 * (n + 1 : ℝ) * ratio ^ 2 →
      (heads : ℝ) ≤ 33 * (n + 1 : ℝ) * ratio ^ 2 := by
  intro h
  have hnonneg : 0 ≤ (n + 1 : ℝ) * ratio ^ 2 := by positivity
  nlinarith

/-- The reverse context-free implication fails at n = 1, heads = 7, ratio = 1.
This tuple need not satisfy the sampling requirements. -/
theorem not_legacy_implies_refined :
    ¬ ∀ (n heads : ℕ) (ratio : ℝ),
      (heads : ℝ) ≤ 33 * (n + 1 : ℝ) * ratio ^ 2 →
        (heads : ℝ) ≤ 3 * (n + 1 : ℝ) * ratio ^ 2 := by
  intro h
  have hbad := h 1 7 1 (by norm_num)
  norm_num at hbad

theorem refined_atomic_margin_contract (n heads : ℕ) (ratio : ℝ)
    (sampling : AtomicMarginSamplingContract n heads ratio) :
    (heads : ℝ) ≤ 3 * (n + 1 : ℝ) * ratio ^ 2 :=
  sampling.real_bound

theorem legacy_atomic_margin_contract (n heads : ℕ) (ratio : ℝ)
    (sampling : AtomicMarginSamplingContract n heads ratio) :
    (heads : ℝ) ≤ 33 * (n + 1 : ℝ) * ratio ^ 2 :=
  refined_implies_legacy n heads ratio sampling.real_bound

/-- The normalized legacy guarantee is exactly the original theorem's bound
at every genuine certificate, independently of the refined proof. -/
theorem legacy_guarantee_at_certificate
    {n : ℕ} {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] {mu : MeasureTheory.Measure J}
    [MeasureTheory.IsProbabilityMeasure mu]
    {f : (Fin n → Bool) → Bool} (C : AtomicMarginCertificate f J mu) :
    (HStar n f : ℝ) ≤ 33 * (n + 1 : ℝ) * (C.scale / C.margin) ^ 2 :=
  C.HStar_real_le_atomicCondition

/-- Every valid certificate has strictly smaller real-valued upper endpoints. -/
theorem certificate_endpoints_strictly_improve
    {n : ℕ} {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] {mu : MeasureTheory.Measure J}
    [MeasureTheory.IsProbabilityMeasure mu]
    {f : (Fin n → Bool) → Bool} (C : AtomicMarginCertificate f J mu) :
    3 * (n + 1 : ℝ) * (C.scale / C.margin) ^ 2 <
      33 * (n + 1 : ℝ) * (C.scale / C.margin) ^ 2 := by
  have hpos : 0 < (n + 1 : ℝ) * (C.scale / C.margin) ^ 2 := by
    have hr := div_pos C.scale_pos C.margin_pos
    positivity
  nlinarith

/-- For every nonconstant genuine certificate, even the rounded natural
sample bound is strictly smaller, not just weakly monotone. -/
theorem certificate_sample_counts_strictly_improve
    {n : ℕ} {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] {mu : MeasureTheory.Measure J}
    [MeasureTheory.IsProbabilityMeasure mu]
    {f : (Fin n → Bool) → Bool} (C : AtomicMarginCertificate f J mu)
    (hn : ¬ ∀ x y, f x = f y) :
    refinedAtomicSampleCount n C.scale C.margin < atomicSampleCount n C.scale C.margin := by
  let A : ℝ := (n + 1 : ℝ) * (C.scale / C.margin) ^ 2
  have hr := C.one_le_scale_div_margin hn
  have hA : 1 ≤ A := by
    have hn1 : (1 : ℝ) ≤ (n + 1 : ℝ) := by norm_num
    have hr2 : 1 ≤ (C.scale / C.margin) ^ 2 := by nlinarith
    exact one_le_mul_of_one_le_of_one_le hn1 hr2
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * A)
  have hfloor := Nat.le_ceil (32 * A)
  have hstrict : (↑⌈2 * A⌉₊ : ℝ) < (↑⌈32 * A⌉₊ : ℝ) := by linarith
  have hnat : ⌈2 * A⌉₊ < ⌈32 * A⌉₊ := by exact_mod_cast hstrict
  simpa [A, refinedAtomicSampleCount, atomicSampleCount, mul_assoc] using hnat

private def expectStatus
    (actual expected : ProofStatus) (label : String) : TermElabM Unit := do
  unless actual == expected do
    throwError "unexpected {label}: expected {expected.label}, got {actual.label}"

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``refined_atomic_margin_contract
    ``legacy_atomic_margin_contract {
      mode := .logical
      facts := #[``refined_implies_legacy, ``not_legacy_implies_refined]
      allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound]
    }
  expectStatus report.req_2_to_1.status .proved "refined/195 forward requirements"
  expectStatus report.req_1_to_2.status .proved "refined/195 reverse requirements"
  expectStatus report.guarantee_1_to_2.status .proved "refined/195 forward guarantee"
  expectStatus report.guarantee_2_to_1.status .refuted "refined/195 reverse guarantee"
  unless report.classification == "source strictly subsumes target under this alignment" do
    throwError "unexpected classification:\n{report.format}"
  logInfo report.format

end HeadComplexity.AtomicMarginSubsumption
