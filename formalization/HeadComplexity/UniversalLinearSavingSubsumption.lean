import HeadComplexity.Results.UniversalLinearSaving
import HeadComplexity.UniversalSublinearSubsumption
import TheoremSubsumption

set_option linter.style.header false

/-!
# Strict certification of the universal linear saving

Both comparisons use the exact same actual-head realization premise. The
second comparison preserves the full natural-number logarithmic budget,
including its earlier minima, rather than a weaker real relaxation.
-/

namespace HeadComplexity.UniversalLinearSavingSubsumption

open Lean Meta Elab TheoremSubsumption
open StarUpperBoundSubsumption UniversalSublinearSubsumption

theorem linear_contract (n heads : ℕ) (h : HeadCountRealized n heads) :
    heads ≤ universalElevenStarBound n := by
  obtain ⟨f, rfl⟩ := h
  exact HStar_le_universalElevenStarBound f

theorem linear_implies_logarithmic (n heads : ℕ) :
    heads ≤ universalElevenStarBound n → heads ≤ universalStarBound n :=
  fun h ↦ h.trans (universalElevenStarBound_le_logarithmic n)

theorem linear_implies_original (n heads : ℕ) :
    heads ≤ universalElevenStarBound n → heads ≤ 2 ^ n - 1 :=
  fun h ↦ (linear_implies_logarithmic n heads h).trans (universalStarBound_le_original n)

theorem original_reverse_refuted :
    ¬ ∀ n heads : ℕ, heads ≤ 2 ^ n - 1 → heads ≤ universalElevenStarBound n := by
  intro h
  have hbad := ((h 13 4097 (by decide)).trans
    (universalElevenStarBound_le_logarithmic 13)).trans (universalStarBound_le_half 13)
  norm_num at hbad

/-- The full old natural budget permits this value in dimension 256; the
linear-saving budget excludes it. All calculations are exact. -/
theorem logarithmic_reverse_refuted :
    ¬ ∀ n heads : ℕ, heads ≤ universalStarBound n → heads ≤ universalElevenStarBound n := by
  intro h
  let b : ℕ := 2 ^ 247
  let heads : ℕ := 23 * b
  have hb : 0 < b := by dsimp [b]; positivity
  have hpowNat : 2 ^ 256 = 512 * b := by
    rw [show (256 : ℕ) = 247 + 9 by decide, pow_add,
      show (2 : ℕ) ^ 9 = 512 by decide]
    exact Nat.mul_comm _ _
  have hhalfNat : 2 ^ 255 = 256 * b := by
    rw [show (255 : ℕ) = 247 + 8 by decide, pow_add,
      show (2 : ℕ) ^ 8 = 256 by decide]
    exact Nat.mul_comm _ _
  have hpowReal : (2 : ℝ) ^ 256 = 512 * (b : ℝ) := by exact_mod_cast hpowNat
  have hlogtwo : (19 / 28 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog128 : (19 / 4 : ℝ) ≤ Real.log 128 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hreal : (heads : ℝ) ≤ logarithmicStarBudget 256 := by
    have hscaled := mul_le_mul_of_nonneg_left hlog128
      (by positivity : (0 : ℝ) ≤ 4 * (b : ℝ))
    calc
      (heads : ℝ) = 23 * (b : ℝ) := by simp [heads]
      _ ≤ 4 * (b : ℝ) * (Real.log 128 + 1) := by nlinarith
      _ = logarithmicStarBudget 256 := by
        change 4 * (b : ℝ) * (Real.log 128 + 1) =
          2 * (2 : ℝ) ^ 256 * (Real.log ((256 : ℝ) / 2) + 1) / 256
        rw [show (256 : ℝ) / 2 = 128 by norm_num, hpowReal]
        ring
  have hold : heads ≤ universalStarBound 256 := by
    simp only [universalStarBound, if_pos (by decide : 2 ≤ 256)]
    apply Nat.le_min.mpr
    refine ⟨?_, Nat.le_floor hreal⟩
    change 23 * b ≤ min (2 ^ 256 - 1) (2 ^ 255)
    rw [hpowNat, hhalfNat]
    omega
  have hbad : heads ≤ ⌊11 * (2 : ℝ) ^ 256 / 256⌋₊ :=
    (h 256 heads hold).trans (min_le_right _ _)
  have hcast : (heads : ℝ) ≤ 11 * (2 : ℝ) ^ 256 / 256 :=
    (by exact_mod_cast hbad : (heads : ℝ) ≤ ⌊11 * (2 : ℝ) ^ 256 / 256⌋₊).trans
      (Nat.floor_le (by positivity))
  have hbReal : (0 : ℝ) < b := by exact_mod_cast hb
  simp only [heads, Nat.cast_mul, Nat.cast_ofNat] at hcast
  rw [hpowReal] at hcast
  nlinarith

/-- Checked witness of strict improvement for all actual functions at every
dimension at least 256, at the real endpoint before integer rounding. -/
theorem linear_endpoints_strict {n : ℕ} (hn : 256 ≤ n)
    (_f : (Fin n → Bool) → Bool) :
    11 * (2 : ℝ) ^ n / n < logarithmicStarBudget n :=
  eleven_budget_lt_logarithmic hn

private def checkStrict (report : ComparisonReport) : TermElabM Unit := do
  unless report.req_2_to_1.status == .proved && report.req_1_to_2.status == .proved &&
      report.guarantee_1_to_2.status == .proved && report.guarantee_2_to_1.status == .refuted do
    throwError "unsettled or incorrect strict comparison:\n{report.format}"
  unless report.classification == "source strictly subsumes target under this alignment" do
    throwError "unexpected classification:\n{report.format}"
  logInfo report.format

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``linear_contract ``original_universal_contract {
    mode := .logical
    facts := #[``linear_implies_original, ``original_reverse_refuted]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound]
  }
  checkStrict report

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``linear_contract ``logarithmic_contract {
    mode := .logical
    facts := #[``linear_implies_logarithmic, ``logarithmic_reverse_refuted]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound]
  }
  checkStrict report

end HeadComplexity.UniversalLinearSavingSubsumption
