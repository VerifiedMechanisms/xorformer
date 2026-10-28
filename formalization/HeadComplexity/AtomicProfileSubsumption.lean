import HeadComplexity.Results.AtomicMarginProfile
import Mathlib.Analysis.Complex.ExponentialBounds
import TheoremSubsumption

set_option linter.style.header false

namespace HeadComplexity.AtomicProfileSubsumption

open Lean Meta Elab TheoremSubsumption MeasureTheory
open scoped BigOperators

theorem profile_contract (heads m : ℕ) (fine coarse : ℝ)
    (sampling : AtomicProfileSamplingContract heads m fine coarse) (budget : fine < 1) :
    heads ≤ m := sampling.sampling budget

theorem baseline_contract (heads m : ℕ) (fine coarse : ℝ)
    (sampling : AtomicProfileSamplingContract heads m fine coarse) (budget : coarse < 1) :
    heads ≤ m := sampling.sampling (sampling.fine_le_coarse.trans_lt budget)

theorem uniform_requirements_imply_profile (heads m : ℕ) (fine coarse : ℝ)
    (sampling : AtomicProfileSamplingContract heads m fine coarse) (budget : coarse < 1) :
    ∃ (_ : AtomicProfileSamplingContract heads m fine coarse) (_ : fine < 1), True :=
  ⟨sampling, sampling.fine_le_coarse.trans_lt budget, trivial⟩

theorem not_profile_requirements_imply_uniform :
    ¬ ∀ (heads m : ℕ) (fine coarse : ℝ),
      AtomicProfileSamplingContract heads m fine coarse → fine < 1 →
        ∃ (_ : AtomicProfileSamplingContract heads m fine coarse) (_ : coarse < 1), True := by
  intro h
  have C : AtomicProfileSamplingContract 1 2 0 2 :=
    ⟨by norm_num, by norm_num, fun _ ↦ by norm_num⟩
  obtain ⟨_, hbad, _⟩ := h 1 2 0 2 C (by norm_num)
  norm_num at hbad

section Bridges

variable {n : ℕ} {J : Type*} [Fintype J] [MeasurableSpace J]
  [MeasurableSingletonClass J] {mu : Measure J} [IsProbabilityMeasure mu]
  {f : (Fin n → Bool) → Bool}

theorem profile_at_certificate (C : AtomicMarginCertificate f J mu)
    (m : ℕ) (hm : 0 < m) (hb : C.profileBudget m < 1) : HStar n f ≤ m :=
  profile_contract (HStar n f) m _ _ (C.profileSamplingContract m hm) hb

/-- Independent bridge to the exact pre-existing compiler declaration. -/
theorem baseline_at_certificate (C : AtomicMarginCertificate f J mu)
    (m : ℕ) (hm : 0 < m) (hb : C.uniformBudget m < 1) : HStar n f ≤ m :=
  HStar_le_of_computableWithHeadsN (C.computableWithHeadsN_of_exp_budget m hm hb)

end Bridges

/-! A tight, nonconstant, genuine certificate witnessing strict applicability. -/

def orTwo (bits : Fin 2 → Bool) : Bool := bits 0 || bits 1

noncomputable def orTwoAtom : FracAtom 2 where
  η := -4 / 5
  δ := 8 / 5
  γ := 1
  α := 1
  ρ := fun i ↦ if i = 0 then 1 else 2
  m := fun _ ↦ 0
  hγ := by norm_num
  hα := by norm_num
  hρ := by intro i; split <;> norm_num

theorem orTwoAtom_eval (bits : Fin 2 → Bool) :
    orTwoAtom.eval bits = ((if bits 0 then 2 else 0) + (if bits 1 then 4 else 0) - 1) / 5 := by
  cases h0 : bits 0 <;> cases h1 : bits 1 <;>
    norm_num [FracAtom.eval, FracAtom.wt, orTwoAtom, Fin.sum_univ_two, h0, h1]

noncomputable def tightOrCertificate : AtomicMarginCertificate orTwo Unit (Measure.dirac ()) where
  atom := fun _ ↦ orTwoAtom
  normalized := by
    intro j bits
    rw [orTwoAtom_eval]
    cases bits 0 <;> cases bits 1 <;> norm_num
  bias := 0
  scale := 5
  margin := 1
  scale_pos := by norm_num
  margin_pos := by norm_num
  separates := by
    intro bits
    simp only [atomicAverage, integral_const, probReal_univ, one_smul]
    rw [orTwoAtom_eval]
    cases h0 : bits 0 <;> cases h1 : bits 1 <;>
      norm_num [signedLabel, orTwo, h0, h1]

theorem tightOrCertificate_pointMargin (bits : Fin 2 → Bool) :
    tightOrCertificate.pointMargin bits =
      if bits 1 then (if bits 0 then 5 else 3) else 1 := by
  simp only [AtomicMarginCertificate.pointMargin, tightOrCertificate, atomicAverage,
    integral_const, probReal_univ, one_smul]
  rw [orTwoAtom_eval]
  cases h0 : bits 0 <;> cases h1 : bits 1 <;>
    norm_num [signedLabel, orTwo, h0, h1]

theorem orTwo_nonconstant : ¬ ∀ x y, orTwo x = orTwo y := by
  intro h
  have hbad := h (fun _ ↦ false) (fun _ ↦ true)
  simp [orTwo] at hbad

theorem tightOrCertificate_margin_attained :
    tightOrCertificate.pointMargin (fun _ ↦ false) = tightOrCertificate.margin := by
  rw [tightOrCertificate_pointMargin]
  norm_num [tightOrCertificate]

theorem tightOrCertificate_uniformBudget :
    tightOrCertificate.uniformBudget 50 = 4 * Real.exp (-1) := by
  norm_num [AtomicMarginCertificate.uniformBudget, tightOrCertificate]

theorem tightOrCertificate_profileBudget :
    tightOrCertificate.profileBudget 50 =
      2 * Real.exp (-1) + Real.exp (-9) + Real.exp (-25) := by
  classical
  have huniv : (Finset.univ : Finset (Fin 2 → Bool)) =
      {![false, false], ![true, false], ![false, true], ![true, true]} := by decide
  unfold AtomicMarginCertificate.profileBudget
  rw [huniv]
  simp_rw [tightOrCertificate_pointMargin]
  norm_num [tightOrCertificate]
  ring

theorem genuine_strict_budget :
    tightOrCertificate.profileBudget 50 < 1 ∧
      ¬ tightOrCertificate.uniformBudget 50 < 1 := by
  rw [tightOrCertificate_profileBudget, tightOrCertificate_uniformBudget]
  have h1 : Real.exp (-1) < (3 : ℝ) / 8 := by linarith [Real.exp_neg_one_lt_d9]
  have h3 : Real.exp (-3) < ((3 : ℝ) / 8) ^ 3 := by
    rw [show (-3 : ℝ) = (3 : ℕ) * (-1) by norm_num, Real.exp_nat_mul]
    gcongr
  have h9 := Real.exp_le_exp.mpr (by norm_num : (-9 : ℝ) ≤ -3)
  have h25 := Real.exp_le_exp.mpr (by norm_num : (-25 : ℝ) ≤ -3)
  have hlo := Real.exp_neg_one_gt_d9
  constructor <;> norm_num at h3 ⊢ <;> linarith

private def checkGeneralization (report : ComparisonReport) : TermElabM Unit := do
  unless report.req_2_to_1.status == .proved && report.req_1_to_2.status == .refuted &&
      report.guarantee_1_to_2.status == .proved && report.guarantee_2_to_1.status == .proved do
    throwError "unsettled profile comparison:\n{report.format}"
  unless report.classification == "source strictly subsumes target under this alignment" do
    throwError "unexpected classification:\n{report.format}"
  logInfo report.format

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``profile_contract ``baseline_contract {
    mode := .logical
    facts := #[``uniform_requirements_imply_profile, ``not_profile_requirements_imply_uniform]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound]
  }
  checkGeneralization report

end HeadComplexity.AtomicProfileSubsumption
