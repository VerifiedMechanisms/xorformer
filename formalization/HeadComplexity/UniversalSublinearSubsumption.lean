import HeadComplexity.Results.UniversalSublinearUpperBound
import HeadComplexity.StarUpperBoundSubsumption
import TheoremSubsumption

set_option linter.style.header false

/-!
# Certified universal quantitative and asymptotic strengthenings

The numerical alignments use the same actual-head realization premise as the
first star-cover comparisons. The sequence alignment identifies the shared
sequence with the unchanged normalized worst-case attention complexity.
-/

namespace HeadComplexity.UniversalSublinearSubsumption

open Lean Meta Elab TheoremSubsumption Filter
open StarUpperBoundSubsumption
open scoped Topology

theorem logarithmic_contract (n heads : ℕ) (h : HeadCountRealized n heads) :
    heads ≤ universalStarBound n := by
  obtain ⟨f, rfl⟩ := h
  exact HStar_le_universalStarBound f

theorem logarithmic_implies_original (n heads : ℕ) :
    heads ≤ universalStarBound n → heads ≤ 2 ^ n - 1 :=
  fun h ↦ h.trans (universalStarBound_le_original n)

theorem original_reverse_refuted :
    ¬ ∀ n heads : ℕ, heads ≤ 2 ^ n - 1 → heads ≤ universalStarBound n := by
  intro h
  have hbad := (h 13 4097 (by decide)).trans (universalStarBound_le_half 13)
  norm_num at hbad

theorem logarithmic_implies_half (n heads : ℕ) :
    heads ≤ universalStarBound n → heads ≤ min (2 ^ n - 1) (2 ^ (n - 1)) :=
  fun h ↦ h.trans (min_le_left _ _)

theorem half_reverse_refuted :
    ¬ ∀ n heads : ℕ, heads ≤ min (2 ^ n - 1) (2 ^ (n - 1)) →
      heads ≤ universalStarBound n := by
  intro h
  have hbad := h 32 (2 ^ 31) (by decide)
  have hstrict := universalStarBound_lt_half (n := 32) (by decide)
  exact (not_lt_of_ge hbad) hstrict

/-- The exact normalized endpoint of the pre-existing worst-case theorem. -/
noncomputable def originalUniversalRatio (n : ℕ) : ℝ :=
  ((2 ^ n - 1 : ℕ) : ℝ) / (2 : ℝ) ^ n

noncomputable def normalizedWorstCase (n : ℕ) : ℝ :=
  (worstCaseHeadComplexity n : ℝ) / (2 : ℝ) ^ n

/-- Checked bridge from the original worst-case upper bound. -/
theorem baseline_ratio_at_worstCase (n : ℕ) :
    normalizedWorstCase n ≤ originalUniversalRatio n := by
  apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ n)).mpr
  exact_mod_cast (worstCaseHeadComplexity_le (n := n))

theorem original_sequence_contract (g : ℕ → ℝ) (halign : g = normalizedWorstCase) :
    (∀ n, g n ≤ originalUniversalRatio n) ∧ True := by
  subst g
  exact ⟨baseline_ratio_at_worstCase, True.intro⟩

/-- The conjunction only keeps the universal quantifier inside the guarantee
for the comparison parser; it is logically equivalent to the exact baseline. -/
theorem sequence_baseline_guarantee_iff (g : ℕ → ℝ) :
    ((∀ n, g n ≤ originalUniversalRatio n) ∧ True) ↔
      (∀ n, g n ≤ originalUniversalRatio n) := by simp

theorem sublinear_sequence_contract (g : ℕ → ℝ) (halign : g = normalizedWorstCase) :
    (∀ n, g n ≤ originalUniversalRatio n) ∧ Tendsto g atTop (𝓝 0) := by
  subst g
  exact ⟨baseline_ratio_at_worstCase, tendsto_worstCaseHeadComplexity_div_two_pow⟩

theorem sequence_forward (g : ℕ → ℝ) :
    ((∀ n, g n ≤ originalUniversalRatio n) ∧ Tendsto g atTop (𝓝 0)) →
      ((∀ n, g n ≤ originalUniversalRatio n) ∧ True) := fun h ↦ ⟨h.1, True.intro⟩

/-- A sequence obeying every exact old endpoint may stay at one half for
all positive dimensions. The old guarantees therefore do not imply decay. -/
theorem sequence_reverse_refuted :
    ¬ ∀ g : ℕ → ℝ, ((∀ n, g n ≤ originalUniversalRatio n) ∧ True) →
      ((∀ n, g n ≤ originalUniversalRatio n) ∧ Tendsto g atTop (𝓝 0)) := by
  intro h
  let g : ℕ → ℝ := fun n ↦ if n = 0 then 0 else 1 / 2
  have hold : ∀ n, g n ≤ originalUniversalRatio n := by
    intro n
    by_cases hn : n = 0
    · simp [g, hn, originalUniversalRatio]
    · have hnpos : 1 ≤ n := by omega
      have hpowNat : 2 ≤ 2 ^ n := by
        have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hnpos
        simpa using this
      have hpowReal : (2 : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hpowNat
      dsimp [g, originalUniversalRatio]
      rw [if_neg hn, Nat.cast_sub (by omega : 1 ≤ 2 ^ n)]
      push_cast
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr
      nlinarith
  have hzero := (h g ⟨hold, True.intro⟩).2
  have hhalf : Tendsto g atTop (𝓝 (1 / 2 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    simp [g, show n ≠ 0 by omega]
  have hbad := tendsto_nhds_unique hhalf hzero
  norm_num at hbad

private def checkStrict (report : ComparisonReport) : TermElabM Unit := do
  unless report.req_2_to_1.status == .proved && report.req_1_to_2.status == .proved &&
      report.guarantee_1_to_2.status == .proved && report.guarantee_2_to_1.status == .refuted do
    throwError "unsettled or incorrect strict comparison:\n{report.format}"
  unless report.classification == "source strictly subsumes target under this alignment" do
    throwError "unexpected classification:\n{report.format}"
  logInfo report.format

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``logarithmic_contract ``original_universal_contract {
    mode := .logical
    facts := #[``logarithmic_implies_original, ``original_reverse_refuted]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound]
  }
  checkStrict report

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``logarithmic_contract ``star_universal_contract {
    mode := .logical
    facts := #[``logarithmic_implies_half, ``half_reverse_refuted]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound]
  }
  checkStrict report

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``sublinear_sequence_contract ``original_sequence_contract {
    mode := .logical
    facts := #[``sequence_forward, ``sequence_reverse_refuted]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound]
  }
  checkStrict report

end HeadComplexity.UniversalSublinearSubsumption
