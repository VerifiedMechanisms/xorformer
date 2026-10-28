import HeadComplexity.AtomicProfileSubsumption
import HeadComplexity.Results.AtomicMarginRange

set_option linter.style.header false

/-!
# Certified atomic-range sampling comparisons

This module certifies that sampling with the actual atom output ranges strengthens the uniform
sampling bound, with bridges to the original head-complexity statements.
-/

namespace HeadComplexity.AtomicRangeSubsumption

open Lean Meta Elab TheoremSubsumption MeasureTheory
open AtomicProfileSubsumption

theorem range_contract (heads m : ℕ) (fine coarse : ℝ)
    (sampling : AtomicProfileSamplingContract heads m fine coarse) (budget : fine < 1) :
    heads ≤ m := sampling.sampling budget

theorem baseline_contract (heads m : ℕ) (fine coarse : ℝ)
    (sampling : AtomicProfileSamplingContract heads m fine coarse) (budget : coarse < 1) :
    heads ≤ m := sampling.sampling (sampling.fine_le_coarse.trans_lt budget)

section Bridges

variable {n : ℕ} {J : Type*} [Fintype J] [MeasurableSpace J]
  [MeasurableSingletonClass J] {mu : Measure J} [IsProbabilityMeasure mu]
  {f : (Fin n → Bool) → Bool}

theorem range_at_certificate (C : AtomicMarginCertificate f J mu)
    (m : ℕ) (hm : 0 < m) (hb : C.tightRangeBudget m < 1) : HStar n f ≤ m :=
  range_contract (HStar n f) m _ _ (C.tightRangeSamplingContract m hm) hb

/-- The target is the genuine pre-existing uniform compiler. -/
theorem baseline_at_certificate (C : AtomicMarginCertificate f J mu)
    (m : ℕ) (hm : 0 < m) (hb : C.uniformBudget m < 1) : HStar n f ≤ m :=
  HStar_le_of_computableWithHeadsN (C.computableWithHeadsN_of_exp_budget m hm hb)

end Bridges

theorem tightOrCertificate_radius_zero (bits : Fin 2 → Bool) :
    tightOrCertificate.tightOutputRange.radius bits = 0 := by
  simp [AtomicMarginCertificate.tightOutputRange, AtomicMarginCertificate.minAtomOutput,
    AtomicMarginCertificate.maxAtomOutput, tightOrCertificate]

theorem tightOrCertificate_rangeBudget_zero (m : ℕ) :
    tightOrCertificate.tightRangeBudget m = 0 := by
  unfold AtomicMarginCertificate.tightRangeBudget AtomicMarginCertificate.rangeBudget
  simp_rw [tightOrCertificate_radius_zero]
  simp

/-- A nonconstant, tight original certificate passes the automatic range
compiler with one sample, while the original sharp uniform budget fails. -/
theorem genuine_strict_budget :
    tightOrCertificate.tightRangeBudget 1 < 1 ∧
      ¬ tightOrCertificate.uniformBudget 1 < 1 := by
  rw [tightOrCertificate_rangeBudget_zero]
  constructor
  · norm_num
  · have hstep : Real.exp (-1) ≤ Real.exp (-(1 : ℝ) / 50) :=
      Real.exp_le_exp.mpr (by norm_num)
    have hlow := Real.exp_neg_one_gt_d9
    norm_num [AtomicMarginCertificate.uniformBudget, tightOrCertificate]
    linarith

theorem range_compiler_one_head : HStar 2 orTwo ≤ 1 :=
  tightOrCertificate.HStar_le_of_tightRange_budget 1 (by norm_num) genuine_strict_budget.1

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``range_contract ``baseline_contract {
    mode := .logical
    facts := #[``uniform_requirements_imply_profile, ``not_profile_requirements_imply_uniform]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound]
  }
  unless report.req_2_to_1.status == .proved && report.req_1_to_2.status == .refuted &&
      report.guarantee_1_to_2.status == .proved && report.guarantee_2_to_1.status == .proved do
    throwError "unsettled range comparison:\n{report.format}"
  unless report.classification == "source strictly subsumes target under this alignment" do
    throwError "unexpected classification:\n{report.format}"
  logInfo report.format

end HeadComplexity.AtomicRangeSubsumption
