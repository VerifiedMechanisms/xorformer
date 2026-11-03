import TheoremSubsumption

import HeadComplexity.Results.AddressingCertificates
import HeadComplexity.Results.FixedDegreeCounting
import HeadComplexity.Results.SharedWidthNormalForm
import HeadComplexity.Results.StarDegreeUpperBound
import HeadComplexity.Results.UniversalNeighborhoodBound
import HeadComplexity.UniversalLinearSavingSubsumption

set_option linter.style.header false

/-!
# Certified integration of the independently re-derived improvements

All numerical contracts have checked bridges to actual `HStar` results.
Reverse witnesses refute context-free implications between the numerical
guarantees; they are not claimed to be realizable head counts.
-/

namespace HeadComplexity.AutomlrSubsumption

open Lean Meta Elab TheoremSubsumption
open StarUpperBoundSubsumption UniversalLinearSavingSubsumption

theorem neighborhood_contract (n heads : ℕ) (h : HeadCountRealized n heads) :
    heads ≤ universalNeighborhoodBound n := by
  obtain ⟨f, rfl⟩ := h
  exact HStar_le_universalNeighborhoodBound f

theorem neighborhood_forward (n heads : ℕ) :
    heads ≤ universalNeighborhoodBound n → heads ≤ universalElevenStarBound n :=
  fun h ↦ h.trans (universalNeighborhoodBound_le_previous n)

theorem previous_permits_8192 : 8192 ≤ universalElevenStarBound 16 := by
  have hfloor : 8192 ≤ ⌊logarithmicStarBudget 16⌋₊ := by
    apply Nat.le_floor
    have hlog : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    norm_num [logarithmicStarBudget]
    nlinarith
  norm_num [universalElevenStarBound, universalLinearStarBound, universalStarBound]
  exact hfloor

theorem neighborhood_reverse_refuted :
    ¬ ∀ n heads : ℕ, heads ≤ universalElevenStarBound n →
      heads ≤ universalNeighborhoodBound n := by
  intro h
  have hnew := h 16 8192 previous_permits_8192
  have hcap := hnew.trans (min_le_right _ _)
  norm_num at hcap

theorem baseline_IDX2_contract (heads : ℕ) (h : heads = HStar 6 (IDX 2)) :
    3 ≤ heads ∧ heads ≤ 16 := by
  subst heads
  refine ⟨addressCount_succ_le_HStar 2, ?_⟩
  have hupper := HStar_le_starDegreeBound_of_ThresholdDegLE (IDX_thresholdDegLE 2)
  norm_num [starDegreeBound, starCenterRanks] at hupper
  exact hupper

theorem exact_IDX2_contract (heads : ℕ) (h : heads = HStar 6 (IDX 2)) : heads = 3 := by
  rw [h, AddressingCertificates.HStar_IDX2]

theorem IDX2_forward (heads : ℕ) : heads = 3 → 3 ≤ heads ∧ heads ≤ 16 := by omega

theorem IDX2_reverse_refuted : ¬ ∀ heads : ℕ, (3 ≤ heads ∧ heads ≤ 16) → heads = 3 := by
  intro h
  have := h 4 (by omega)
  omega

theorem baseline_IDX3_contract (heads : ℕ) (h : heads = HStar 11 (IDX 3)) :
    4 ≤ heads ∧ heads ≤ 176 := by
  subst heads
  refine ⟨addressCount_succ_le_HStar 3, ?_⟩
  have hupper := HStar_le_starDegreeBound_of_ThresholdDegLE (IDX_thresholdDegLE 3)
  norm_num [starDegreeBound, starCenterRanks] at hupper
  exact hupper

theorem exact_IDX3_contract (heads : ℕ) (h : heads = HStar 11 (IDX 3)) : heads = 4 := by
  rw [h, AddressingCertificates.HStar_IDX3]

theorem IDX3_forward (heads : ℕ) : heads = 4 → 4 ≤ heads ∧ heads ≤ 176 := by omega

theorem IDX3_reverse_refuted : ¬ ∀ heads : ℕ, (4 ≤ heads ∧ heads ≤ 176) → heads = 4 := by
  intro h
  have := h 5 (by omega)
  omega

/-- Exact degree-class realization and the explicit analytic/counting
requirements are shared by both sides of this conditional comparison. -/
structure FixedDegreeCountingRequirements (d m H maximum : ℕ) : Prop where
  realized : maximum = degreeClassHeadMaximum (d * m) d
  nonempty_class : ∃ f : (Fin (d * m) → Bool) → Bool, thresholdDeg f = d
  warren : WarrenStrictSignPatternBound
  head_dimension : 1 + 2 * H * (d * m + 1) ≤ m ^ d
  lower_positive : 0 < Fintype.card (LowerDegreeParameter (d * m) d)
  lower_dimension : Fintype.card (LowerDegreeParameter (d * m) d) ≤ m ^ d
  budget : headTraceBudget (d * m) H (m ^ d) +
    lowerDegreeTraceBudget (d * m) d (m ^ d) < (2 : ℝ) ^ (m ^ d)

theorem fixed_degree_baseline_contract (d m H maximum : ℕ)
    (h : FixedDegreeCountingRequirements d m H maximum) : d ≤ maximum := by
  rw [h.realized]
  exact degree_le_degreeClassHeadMaximum h.nonempty_class

theorem fixed_degree_counting_contract (d m H maximum : ℕ)
    (h : FixedDegreeCountingRequirements d m H maximum) : d ≤ maximum ∧ H < maximum := by
  refine ⟨fixed_degree_baseline_contract d m H maximum h, ?_⟩
  rw [h.realized]
  exact fixed_degree_maximum_gt d m H h.warren h.head_dimension
    h.lower_positive h.lower_dimension h.budget

theorem fixed_degree_forward (d _m H maximum : ℕ) :
    (d ≤ maximum ∧ H < maximum) → d ≤ maximum := And.left

theorem fixed_degree_reverse_refuted :
    ¬ ∀ d _m H maximum : ℕ, d ≤ maximum → (d ≤ maximum ∧ H < maximum) := by
  intro h
  have hbad := (h 2 1 3 2 (by omega)).2
  omega

def SharedWidthRealized (n H width : ℕ) : Prop :=
  ∃ f : (Fin n → Bool) → Bool, computableWithHeadsN n H f ∧ width = sharedWidthAtHeads n H f

theorem baseline_width_contract (n H width : ℕ) (h : SharedWidthRealized n H width) :
    width ≤ H * 3 := by
  obtain ⟨f, hf, rfl⟩ := h
  exact sharedWidthAtHeads_le_three_mul hf

theorem improved_width_contract (n H width : ℕ) (h : SharedWidthRealized n H width) :
    width ≤ min (H * 3) (n + 2) := by
  obtain ⟨f, hf, rfl⟩ := h
  exact sharedWidthAtHeads_le_min hf

theorem width_forward (n H width : ℕ) : width ≤ min (H * 3) (n + 2) → width ≤ H * 3 :=
  fun h ↦ h.trans (min_le_left _ _)

theorem width_reverse_refuted :
    ¬ ∀ n H width : ℕ, width ≤ H * 3 → width ≤ min (H * 3) (n + 2) := by
  intro h
  have := h 1 2 4 (by omega)
  omega

private def checkStrict (report : ComparisonReport) : TermElabM Unit := do
  unless report.req_2_to_1.status == .proved && report.req_1_to_2.status == .proved &&
      report.guarantee_1_to_2.status == .proved && report.guarantee_2_to_1.status == .refuted do
    throwError "unsettled or incorrect strict comparison:\n{report.format}"
  unless report.classification == "source strictly subsumes target under this alignment" do
    throwError "unexpected classification:\n{report.format}"
  logInfo report.format

run_cmd Command.liftTermElabM do
  checkStrict (← compareTheorems ``neighborhood_contract ``linear_contract {
    mode := .logical
    facts := #[``neighborhood_forward, ``neighborhood_reverse_refuted]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound] })

run_cmd Command.liftTermElabM do
  checkStrict (← compareTheorems ``exact_IDX2_contract ``baseline_IDX2_contract {
    mode := .logical
    facts := #[``IDX2_forward, ``IDX2_reverse_refuted]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound] })

run_cmd Command.liftTermElabM do
  checkStrict (← compareTheorems ``exact_IDX3_contract ``baseline_IDX3_contract {
    mode := .logical
    facts := #[``IDX3_forward, ``IDX3_reverse_refuted]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound] })

run_cmd Command.liftTermElabM do
  checkStrict (← compareTheorems ``fixed_degree_counting_contract ``fixed_degree_baseline_contract {
    mode := .logical
    facts := #[``fixed_degree_forward, ``fixed_degree_reverse_refuted]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound] })

run_cmd Command.liftTermElabM do
  checkStrict (← compareTheorems ``improved_width_contract ``baseline_width_contract {
    mode := .logical
    facts := #[``width_forward, ``width_reverse_refuted]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound] })

end HeadComplexity.AutomlrSubsumption
