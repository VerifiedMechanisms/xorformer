import TheoremSubsumption

import HeadComplexity.Results.AtomicMarginEntropy

set_option linter.style.header false

/-!
# Certified strict improvements to the refined atomic-margin bounds

Both comparisons use the original sampling contract, whose bridge from
genuine certificates is already proved by the existing refinement. The reversed numeric
guarantees are refuted independently of those requirements. Additional
theorems prove strict endpoint improvement on genuine certificate data.
-/

namespace HeadComplexity.AtomicEntropySubsumption

open Lean Meta Elab TheoremSubsumption

theorem entropy_implies_baseline (n heads : ℕ) (ratio : ℝ) :
    (heads : ℝ) ≤ (2 * (n : ℝ) * Real.log 2 + 1) * ratio ^ 2 →
      (heads : ℝ) ≤ 3 * (n + 1 : ℝ) * ratio ^ 2 := by
  intro h
  have hlog := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)
  have hc : 2 * (n : ℝ) * Real.log 2 + 1 ≤ 3 * (n + 1 : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog.le (by positivity : (0 : ℝ) ≤ 2 * n)]
  exact h.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _))

theorem not_baseline_implies_entropy :
    ¬ ∀ (n heads : ℕ) (ratio : ℝ),
      (heads : ℝ) ≤ 3 * (n + 1 : ℝ) * ratio ^ 2 →
        (heads : ℝ) ≤ (2 * (n : ℝ) * Real.log 2 + 1) * ratio ^ 2 := by
  intro h
  have hbad := h 1 3 1 (by norm_num)
  have hlog := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)
  norm_num at hbad
  linarith

theorem entropy_real_contract (n heads : ℕ) (ratio : ℝ)
    (sampling : AtomicMarginSamplingContract n heads ratio) :
    (heads : ℝ) ≤ (2 * (n : ℝ) * Real.log 2 + 1) * ratio ^ 2 :=
  sampling.entropy_real_bound

theorem baseline_real_contract (n heads : ℕ) (ratio : ℝ)
    (sampling : AtomicMarginSamplingContract n heads ratio) :
    (heads : ℝ) ≤ 3 * (n + 1 : ℝ) * ratio ^ 2 :=
  sampling.real_bound

theorem entropy_natural_implies_baseline (n heads : ℕ) (ratio : ℝ) :
    heads ≤ min (entropyAtomicSampleCount n ratio 1) (refinedAtomicSampleCount n ratio 1) →
      heads ≤ refinedAtomicSampleCount n ratio 1 :=
  fun h ↦ h.trans (min_le_right _ _)

theorem not_baseline_natural_implies_entropy :
    ¬ ∀ (n heads : ℕ) (ratio : ℝ), heads ≤ refinedAtomicSampleCount n ratio 1 →
      heads ≤ min (entropyAtomicSampleCount n ratio 1) (refinedAtomicSampleCount n ratio 1) := by
  intro h
  have hbad := h 1 3 1 (by norm_num [refinedAtomicSampleCount])
  have hlog := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)
  have hf : ⌊2 * (1 : ℝ) * Real.log 2 * (1 / 1) ^ 2⌋₊ < 2 := by
    apply (Nat.floor_lt (by positivity)).mpr
    norm_num
    linarith
  have hb := hbad.trans (min_le_left _ _)
  unfold entropyAtomicSampleCount at hb
  simp only [Nat.cast_one] at hb
  omega

theorem entropy_natural_contract (n heads : ℕ) (ratio : ℝ)
    (sampling : AtomicMarginSamplingContract n heads ratio) :
    heads ≤ min (entropyAtomicSampleCount n ratio 1) (refinedAtomicSampleCount n ratio 1) :=
  le_min sampling.entropy_sample_bound sampling.sample_bound

theorem baseline_natural_contract (n heads : ℕ) (ratio : ℝ)
    (sampling : AtomicMarginSamplingContract n heads ratio) :
    heads ≤ refinedAtomicSampleCount n ratio 1 :=
  sampling.sample_bound

section SemanticBridges

variable {n : ℕ} {J : Type*} [Fintype J] [MeasurableSpace J]
  [MeasurableSingletonClass J] {mu : MeasureTheory.Measure J}
  [MeasureTheory.IsProbabilityMeasure mu] {f : (Fin n → Bool) → Bool}

/-- This uses the refined declaration directly, independently of the new proof. -/
theorem baseline_real_at_certificate (C : AtomicMarginCertificate f J mu) :
    (HStar n f : ℝ) ≤ 3 * (n + 1 : ℝ) * (C.scale / C.margin) ^ 2 :=
  C.HStar_real_le_atomicCondition_refined

theorem entropy_real_at_certificate (C : AtomicMarginCertificate f J mu) :
    (HStar n f : ℝ) ≤
      (2 * (n : ℝ) * Real.log 2 + 1) * (C.scale / C.margin) ^ 2 :=
  entropy_real_contract n (HStar n f) (C.scale / C.margin) C.samplingContract

theorem baseline_natural_at_certificate (C : AtomicMarginCertificate f J mu) :
    HStar n f ≤ refinedAtomicSampleCount n C.scale C.margin :=
  C.HStar_le_refinedAtomicSampleCount

theorem entropy_natural_at_certificate (C : AtomicMarginCertificate f J mu) :
    HStar n f ≤ min (entropyAtomicSampleCount n C.scale C.margin)
      (refinedAtomicSampleCount n C.scale C.margin) :=
  C.HStar_le_min_entropy_refined

/-- Strictness holds for every genuine certificate, not just numeric tuples. -/
theorem certificate_real_endpoints_strict (C : AtomicMarginCertificate f J mu) :
    (2 * (n : ℝ) * Real.log 2 + 1) * (C.scale / C.margin) ^ 2 <
      3 * (n + 1 : ℝ) * (C.scale / C.margin) ^ 2 :=
  entropy_endpoint_lt_refined n (div_pos C.scale_pos C.margin_pos)

theorem certificate_natural_endpoints_strict (C : AtomicMarginCertificate f J mu)
    (hn : ¬ ∀ x y, f x = f y) :
    min (entropyAtomicSampleCount n C.scale C.margin)
      (refinedAtomicSampleCount n C.scale C.margin) <
        refinedAtomicSampleCount n C.scale C.margin :=
  (min_le_left _ _).trans_lt (entropy_sampleCount_lt_refined n (C.one_le_scale_div_margin hn))

theorem conditionNumber_endpoints_strict (f : (Fin n → Bool) → Bool)
    (hn : ¬ ∀ x y, f x = f y) :
    (2 * (n : ℝ) * Real.log 2 + 1) * (atomicConditionNumber f) ^ 2 <
      3 * (n + 1 : ℝ) * (atomicConditionNumber f) ^ 2 :=
  entropy_endpoint_lt_refined n (lt_of_lt_of_le (by norm_num) (one_le_atomicConditionNumber f hn))

end SemanticBridges

private def checkStrict (report : ComparisonReport) : TermElabM Unit := do
  unless report.req_2_to_1.status == .proved && report.req_1_to_2.status == .proved &&
      report.guarantee_1_to_2.status == .proved && report.guarantee_2_to_1.status == .refuted do
    throwError "unsettled or incorrect strict comparison:\n{report.format}"
  unless report.classification == "source strictly subsumes target under this alignment" do
    throwError "unexpected classification:\n{report.format}"
  logInfo report.format

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``entropy_real_contract ``baseline_real_contract {
    mode := .logical
    facts := #[``entropy_implies_baseline, ``not_baseline_implies_entropy]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound]
  }
  checkStrict report

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``entropy_natural_contract ``baseline_natural_contract {
    mode := .logical
    facts := #[``entropy_natural_implies_baseline, ``not_baseline_natural_implies_entropy]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound]
  }
  checkStrict report

end HeadComplexity.AtomicEntropySubsumption
