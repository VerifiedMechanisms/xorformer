import TheoremSubsumption

import HeadComplexity.Results.AtomicConditionGap
import HeadComplexity.Results.ExactFamilies

set_option linter.style.header false

/-!
# Certified atomic-condition gap comparisons

This module compares the refined atomic-condition lower bounds with the baseline normalization
bound, retaining the invariant's exact value in both contracts.
-/

namespace HeadComplexity.AtomicConditionGapSubsumption

open Lean Meta Elab TheoremSubsumption
open scoped BigOperators

/-- Expose the value of the invariant as a shared scalar, with its exact
semantic equality retained as a requirement in both compared declarations. -/
theorem strengthened_lower_contract (n : ℕ) (f : (Fin n → Bool) → Bool) (kappa : ℝ)
    (hn : ¬ ∀ x y, f x = f y) (hk : kappa = atomicConditionNumber f) :
    1 ≤ kappa ∧ (2 ≤ HStar n f → 1 + atomicOneHeadGap n ≤ kappa) ∧
      (2 ≤ n → (∑ bits : Fin n → Bool, signedLabel f bits) = 0 →
        2 ≤ HStar n f → (2 : ℝ) ^ n / ((2 : ℝ) ^ n - 2) ≤ kappa) := by
  rw [hk]
  exact atomicConditionNumber_lower_bounds f hn

/-- The target is the old normalization lower bound, with the same exact
value exposure as the source, and no additional hypotheses. -/
theorem baseline_lower_contract (n : ℕ) (f : (Fin n → Bool) → Bool) (kappa : ℝ)
    (hn : ¬ ∀ x y, f x = f y) (hk : kappa = atomicConditionNumber f) :
    1 ≤ kappa := by
  rw [hk]
  exact one_le_atomicConditionNumber f hn

theorem strengthened_implies_baseline (n : ℕ) (f : (Fin n → Bool) → Bool) (kappa : ℝ) :
    (1 ≤ kappa ∧ (2 ≤ HStar n f → 1 + atomicOneHeadGap n ≤ kappa) ∧
      (2 ≤ n → (∑ bits : Fin n → Bool, signedLabel f bits) = 0 →
        2 ≤ HStar n f → (2 : ℝ) ^ n / ((2 : ℝ) ^ n - 2) ≤ kappa)) → 1 ≤ kappa :=
  And.left

/-- This refutes a context-free implication. The exposed scalar 1 is not
claimed to equal the true condition number of two-bit parity. -/
theorem not_baseline_implies_strengthened :
    ¬ ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (kappa : ℝ),
      1 ≤ kappa → (1 ≤ kappa ∧ (2 ≤ HStar n f → 1 + atomicOneHeadGap n ≤ kappa) ∧
        (2 ≤ n → (∑ bits : Fin n → Bool, signedLabel f bits) = 0 →
          2 ≤ HStar n f → (2 : ℝ) ^ n / ((2 : ℝ) ^ n - 2) ≤ kappa)) := by
  intro h
  have hbad := (h 2 (PARITY 2) 1 (by norm_num)).2.1
    (by rw [HStar_parity])
  linarith [atomicOneHeadGap_pos 2]

/-- Specializing the value exposure back to the literal invariant is exact. -/
theorem strengthened_at_actual_invariant {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hn : ¬ ∀ x y, f x = f y) :
    1 ≤ atomicConditionNumber f ∧
      (2 ≤ HStar n f → 1 + atomicOneHeadGap n ≤ atomicConditionNumber f) ∧
      (2 ≤ n → (∑ bits : Fin n → Bool, signedLabel f bits) = 0 →
        2 ≤ HStar n f → (2 : ℝ) ^ n / ((2 : ℝ) ^ n - 2) ≤ atomicConditionNumber f) :=
  strengthened_lower_contract n f (atomicConditionNumber f) hn rfl

theorem baseline_at_actual_invariant {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hn : ¬ ∀ x y, f x = f y) : 1 ≤ atomicConditionNumber f :=
  one_le_atomicConditionNumber f hn

/-- Strictly better actual lower endpoints for every affected function. -/
theorem actual_gap_endpoints_strict {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hH : 2 ≤ HStar n f) :
    1 < 1 + atomicOneHeadGap n ∧ 1 + atomicOneHeadGap n ≤ atomicConditionNumber f :=
  ⟨by linarith [atomicOneHeadGap_pos n],
    one_add_gap_le_atomicConditionNumber_of_two_le_HStar f hH⟩

/-- A concrete nonempty family to which the strictly improved bound applies. -/
theorem parity_atomicCondition_gap (n : ℕ) (hn : 2 ≤ n) :
    1 < 1 + atomicOneHeadGap n ∧
      1 + atomicOneHeadGap n ≤ atomicConditionNumber (PARITY n) :=
  actual_gap_endpoints_strict (PARITY n) (by simpa [HStar_parity] using hn)

/-- A concrete strengthened lower bound on the actual invariant, compared
with the pre-existing normalization endpoint one. -/
theorem xor2_atomicConditionNumber_ge_two : 2 ≤ atomicConditionNumber (PARITY 2) := by
  have hbal : (∑ bits : Fin 2 → Bool, signedLabel (PARITY 2) bits) = 0 := by
    classical
    have huniv : (Finset.univ : Finset (Fin 2 → Bool)) =
        {![false, false], ![true, false], ![false, true], ![true, true]} := by decide
    rw [huniv]
    have h00 : PARITY 2 ![false, false] = false := by decide
    have h10 : PARITY 2 ![true, false] = true := by decide
    have h01 : PARITY 2 ![false, true] = true := by decide
    have h11 : PARITY 2 ![true, true] = false := by decide
    norm_num [signedLabel, h00, h10, h01, h11]
  have h := balanced_atomicConditionNumber_lower_bound (PARITY 2) (by norm_num)
    hbal (by rw [HStar_parity])
  norm_num at h
  exact h

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``strengthened_lower_contract ``baseline_lower_contract {
    mode := .logical
    facts := #[``strengthened_implies_baseline, ``not_baseline_implies_strengthened]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound]
  }
  unless report.req_2_to_1.status == .proved && report.req_1_to_2.status == .proved &&
      report.guarantee_1_to_2.status == .proved && report.guarantee_2_to_1.status == .refuted do
    throwError "unsettled condition-gap comparison:\n{report.format}"
  unless report.classification == "source strictly subsumes target under this alignment" do
    throwError "unexpected classification:\n{report.format}"
  logInfo report.format

end HeadComplexity.AtomicConditionGapSubsumption
