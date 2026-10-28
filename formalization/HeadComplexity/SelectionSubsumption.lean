import TheoremSubsumption

open Lean Meta Elab TheoremSubsumption

/-!
# Certified theorem-selection comparisons

This module records the normalized contracts used to audit the theorem
selection.  The normalization exposes numeric bounds as independent variables,
so the comparison measures the promises made by the statements rather than
re-proving already established closed propositions.

The comparison tool checks requirements contravariantly and guarantees
covariantly.  Its generated certificates are ordinary Lean theorems and are
therefore included in the repository-wide axiom audit.

These contracts are five spot checks, not semantic bridges to every original
result declaration.  In particular, a refuting numeric tuple need not be
realized by an actual Boolean function.
-/

namespace HeadComplexity.SelectionSubsumption

private def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def expectStatus
    (actual expected : ProofStatus) (label : String) : TermElabM Unit := do
  unless actual == expected do
    throwError "unexpected {label}: expected {expected.label}, got {actual.label}"

private def finishReport
    (report : ComparisonReport) (classification : String) : TermElabM Unit := do
  unless report.classification == classification do
    throwError "unexpected classification:\n{report.format}"
  logInfo report.format

/-! ## Theorem 110 versus the headline bound of theorem 48 -/

structure AffineCylinderBounds
    (degree heads cylinder affineFree : Nat) : Prop where
  degree_le_heads : degree ≤ heads
  heads_le_cylinder : heads ≤ cylinder
  cylinder_le_affineFree : cylinder ≤ affineFree

theorem theorem110_contract
    (degree heads cylinder affineFree : Nat)
    (bounds : AffineCylinderBounds degree heads cylinder affineFree) :
    degree ≤ heads ∧ heads ≤ cylinder ∧ cylinder ≤ affineFree :=
  ⟨bounds.degree_le_heads, bounds.heads_le_cylinder,
    bounds.cylinder_le_affineFree⟩

theorem theorem48_headline_contract
    (degree heads cylinder affineFree : Nat)
    (bounds : AffineCylinderBounds degree heads cylinder affineFree) :
    heads ≤ affineFree :=
  Nat.le_trans bounds.heads_le_cylinder bounds.cylinder_le_affineFree

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``theorem110_contract
    ``theorem48_headline_contract {
      mode := .logical
      allowedAxioms? := some allowedAxioms
    }
  expectStatus report.req_2_to_1.status .proved "110/48 forward requirements"
  expectStatus report.req_1_to_2.status .proved "110/48 reverse requirements"
  expectStatus report.guarantee_1_to_2.status .proved "110/48 forward guarantee"
  expectStatus report.guarantee_2_to_1.status .refuted "110/48 reverse guarantee"
  finishReport report "source strictly subsumes target under this alignment"

/-! ## Theorem 69 versus the positive-projection upper bound -/

structure PositiveProjectionBounds
    (degree heads projection : Nat) : Prop where
  degree_le_heads : degree ≤ heads
  heads_le_projection : heads ≤ projection

theorem theorem69_contract
    (degree heads projection : Nat)
    (bounds : PositiveProjectionBounds degree heads projection) :
    degree ≤ heads ∧ heads ≤ projection :=
  ⟨bounds.degree_le_heads, bounds.heads_le_projection⟩

theorem theorem013_positive_projection_contract
    (degree heads projection : Nat)
    (bounds : PositiveProjectionBounds degree heads projection) :
    heads ≤ projection :=
  bounds.heads_le_projection

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``theorem69_contract
    ``theorem013_positive_projection_contract {
      mode := .logical
      allowedAxioms? := some allowedAxioms
    }
  expectStatus report.req_2_to_1.status .proved "69/013 forward requirements"
  expectStatus report.req_1_to_2.status .proved "69/013 reverse requirements"
  expectStatus report.guarantee_1_to_2.status .proved "69/013 forward guarantee"
  expectStatus report.guarantee_2_to_1.status .refuted "69/013 reverse guarantee"
  finishReport report "source strictly subsumes target under this alignment"

/-! ## Theorem 144 versus its degree-tight specialization, theorem 141 -/

structure OneBitGateBounds (degree heads positiveCost : Nat) : Prop where
  degree_le_heads : degree ≤ heads
  heads_le_positiveCost : heads ≤ positiveCost

theorem theorem144_contract
    (degree heads positiveCost : Nat)
    (bounds : OneBitGateBounds degree heads positiveCost) :
    degree ≤ heads ∧ heads ≤ positiveCost :=
  ⟨bounds.degree_le_heads, bounds.heads_le_positiveCost⟩

theorem theorem141_contract
    (degree heads positiveCost : Nat)
    (bounds : OneBitGateBounds degree heads positiveCost)
    (tight : degree = positiveCost) :
    heads = degree := by
  apply Nat.le_antisymm
  · simpa [tight] using bounds.heads_le_positiveCost
  · exact bounds.degree_le_heads

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``theorem144_contract ``theorem141_contract {
    allowedAxioms? := some allowedAxioms
  }
  expectStatus report.req_2_to_1.status .proved "144/141 forward requirements"
  expectStatus report.req_1_to_2.status .unknown "144/141 reverse requirements"
  expectStatus report.guarantee_1_to_2.status .refuted "144/141 forward guarantee"
  expectStatus report.guarantee_2_to_1.status .refuted "144/141 reverse guarantee"
  expectStatus report.contextual_1_to_2.status .proved "144/141 contextual adapter"
  finishReport report "incomparable under this alignment"

/-! ## Theorem 93 versus the explicit calibration theorem 85 -/

structure RawVoteBounds (heads rawCost : Nat) : Prop where
  heads_le_rawCost : heads ≤ rawCost

structure CalibratedVoteBounds
    (heads rawCost explicitCost : Nat) : Prop
    extends RawVoteBounds heads rawCost where
  heads_le_explicitCost : heads ≤ explicitCost

theorem theorem93_contract
    (heads rawCost _explicitCost : Nat)
    (bounds : RawVoteBounds heads rawCost) :
    heads ≤ rawCost :=
  bounds.heads_le_rawCost

theorem theorem85_contract
    (heads rawCost explicitCost : Nat)
    (bounds : CalibratedVoteBounds heads rawCost explicitCost) :
    heads ≤ explicitCost :=
  bounds.heads_le_explicitCost

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``theorem93_contract ``theorem85_contract {
    facts := #[``CalibratedVoteBounds.toRawVoteBounds,
      ``CalibratedVoteBounds.heads_le_explicitCost]
    allowedAxioms? := some allowedAxioms
  }
  expectStatus report.req_2_to_1.status .proved "93/85 forward requirements"
  expectStatus report.req_1_to_2.status .unknown "93/85 reverse requirements"
  expectStatus report.guarantee_1_to_2.status .refuted "93/85 forward guarantee"
  expectStatus report.guarantee_2_to_1.status .refuted "93/85 reverse guarantee"
  expectStatus report.contextual_1_to_2.status .proved "93/85 contextual adapter"
  finishReport report "incomparable under this alignment"

/-! ## The optimized invariant 173 versus the fixed certificate 170 -/

structure PositiveMultigridBounds
    (heads optimized fixed fiber : Nat) : Prop where
  heads_le_optimized : heads ≤ optimized
  optimized_le_fixed : optimized ≤ fixed
  fiber_le_heads : fiber ≤ heads

theorem theorem173_contract
    (heads optimized fixed fiber : Nat) (_certificateAvailable : Bool)
    (bounds : PositiveMultigridBounds heads optimized fixed fiber) :
    heads ≤ optimized ∧ optimized ≤ fixed :=
  ⟨bounds.heads_le_optimized, bounds.optimized_le_fixed⟩

theorem theorem170_contract
    (heads optimized fixed fiber : Nat) (certificateAvailable : Bool)
    (bounds : PositiveMultigridBounds heads optimized fixed fiber)
    (_certificatePresent : certificateAvailable = true) :
    heads ≤ fixed ∧ fiber ≤ heads :=
  ⟨Nat.le_trans bounds.heads_le_optimized bounds.optimized_le_fixed,
    bounds.fiber_le_heads⟩

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``theorem173_contract ``theorem170_contract {
    mode := .logical
    heartbeat := 50000
    allowedAxioms? := some allowedAxioms
  }
  expectStatus report.req_2_to_1.status .proved "173/170 forward requirements"
  expectStatus report.req_1_to_2.status .unknown "173/170 reverse requirements"
  expectStatus report.guarantee_1_to_2.status .refuted "173/170 forward guarantee"
  expectStatus report.guarantee_2_to_1.status .refuted "173/170 reverse guarantee"
  finishReport report "incomparable under this alignment"

end HeadComplexity.SelectionSubsumption
