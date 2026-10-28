import HeadComplexity.Results.UniversalStarUpperBound
import TheoremSubsumption

set_option linter.style.header false

/-!
# Strict certification against the old universal and support-count bounds

The shared realization premise ties the numerical variable to the unchanged
attention invariant. Both directions of requirement alignment are checked.
The guarantee comparisons are context-free numerical implications. Separate
endpoint theorems show strict improvement of applicable budgets, including
all truth tables of dimension at least two.
-/

namespace HeadComplexity.StarUpperBoundSubsumption

open Lean Meta Elab TheoremSubsumption
open scoped BigOperators

def HeadCountRealized (n heads : ℕ) : Prop :=
  ∃ f : (Fin n → Bool) → Bool, heads = HStar n f

def DegreeHeadCountRealized (n d heads : ℕ) : Prop :=
  ∃ f : (Fin n → Bool) → Bool, ThresholdDegLE f d ∧ heads = HStar n f

/-- Baseline bridge uses the original theorem 9 declaration directly. -/
theorem original_universal_contract (n heads : ℕ) (h : HeadCountRealized n heads) :
    heads ≤ 2 ^ n - 1 := by
  obtain ⟨f, rfl⟩ := h
  exact HStar_le_universal_boolean f

theorem star_universal_contract (n heads : ℕ) (h : HeadCountRealized n heads) :
    heads ≤ min (2 ^ n - 1) (2 ^ (n - 1)) := by
  obtain ⟨f, rfl⟩ := h
  exact HStar_le_min_universal_star f

theorem universal_forward (n heads : ℕ) :
    heads ≤ min (2 ^ n - 1) (2 ^ (n - 1)) → heads ≤ 2 ^ n - 1 :=
  fun h ↦ h.trans (min_le_left _ _)

theorem universal_reverse_refuted :
    ¬ ∀ n heads : ℕ, heads ≤ 2 ^ n - 1 →
      heads ≤ min (2 ^ n - 1) (2 ^ (n - 1)) := by
  intro h
  have := h 3 5 (by decide)
  norm_num at this

/-- Baseline bridge uses the curated support-count theorem directly. -/
theorem original_degree_contract (n d heads : ℕ) (h : DegreeHeadCountRealized n d heads) :
    heads ≤ 1 + ∑ r ∈ Finset.Icc 2 d, n.choose r := by
  obtain ⟨f, hdeg, rfl⟩ := h
  exact HStar_le_one_add_sum_choose_of_ThresholdDegLE hdeg

theorem star_degree_contract (n d heads : ℕ) (h : DegreeHeadCountRealized n d heads) :
    heads ≤ min (starDegreeBound n d) (1 + ∑ r ∈ Finset.Icc 2 d, n.choose r) := by
  obtain ⟨f, hdeg, rfl⟩ := h
  exact HStar_le_min_starDegree_affineFree_of_ThresholdDegLE hdeg

theorem degree_forward (n d heads : ℕ) :
    heads ≤ min (starDegreeBound n d) (1 + ∑ r ∈ Finset.Icc 2 d, n.choose r) →
      heads ≤ 1 + ∑ r ∈ Finset.Icc 2 d, n.choose r :=
  fun h ↦ h.trans (min_le_right _ _)

theorem degree_reverse_refuted :
    ¬ ∀ n d heads : ℕ, heads ≤ 1 + ∑ r ∈ Finset.Icc 2 d, n.choose r →
      heads ≤ min (starDegreeBound n d) (1 + ∑ r ∈ Finset.Icc 2 d, n.choose r) := by
  intro h
  have := h 4 2 7 (by decide)
  norm_num [Finset.Icc_self] at this

/-- Every genuine model has the shared numerical realization premise. -/
theorem realized_at_function {n : ℕ} (f : (Fin n → Bool) → Bool) :
    HeadCountRealized n (HStar n f) := ⟨f, rfl⟩

theorem degree_realized_at_function {n d : ℕ} {f : (Fin n → Bool) → Bool}
    (h : ThresholdDegLE f d) : DegreeHeadCountRealized n d (HStar n f) :=
  ⟨f, h, rfl⟩

/-- All functions in dimension at least two receive a strictly smaller
applicable numerical budget, independently of the tool countermodel. -/
theorem universal_endpoints_strict {n : ℕ} (hn : 2 ≤ n)
    (_f : (Fin n → Bool) → Bool) :
    min (2 ^ n - 1) (2 ^ (n - 1)) < 2 ^ n - 1 :=
  (min_le_right _ _).trans_lt (two_pow_pred_lt_original_universal hn)

/-- The degree comparison is strict for the entire applicable quadratic
four-bit class, rather than requiring any additional hypothesis. -/
theorem quadratic_four_bit_endpoints_strict
    (_f : (Fin 4 → Bool) → Bool) (_h : ThresholdDegLE _f 2) :
    min (starDegreeBound 4 2) (1 + ∑ r ∈ Finset.Icc 2 2, Nat.choose 4 r) <
      1 + ∑ r ∈ Finset.Icc 2 2, Nat.choose 4 r := by
  simp only [starDegreeBound_two]
  decide

/-- The same support-budget saving applies beyond the archived small-cube
exact classifications: eight-bit quadratics improve from 29 to eight. -/
theorem quadratic_eight_bit_endpoints_strict
    (_f : (Fin 8 → Bool) → Bool) (_h : ThresholdDegLE _f 2) :
    min (starDegreeBound 8 2) (1 + ∑ r ∈ Finset.Icc 2 2, Nat.choose 8 r) <
      1 + ∑ r ∈ Finset.Icc 2 2, Nat.choose 8 r := by
  simp only [starDegreeBound_two]
  decide

def MinimumDegreeHeadCountRealized (n degree heads : ℕ) : Prop :=
  ∃ f : (Fin n → Bool) → Bool, degree = thresholdDeg f ∧ heads = HStar n f

/-- Exact bridge to core theorem 6. -/
theorem original_threshold_degree_contract (n degree heads : ℕ)
    (h : MinimumDegreeHeadCountRealized n degree heads) : degree ≤ heads := by
  obtain ⟨f, rfl, rfl⟩ := h
  exact thresholdDeg_le_of_ThresholdDegLE
    (degree_le_of_computableWithHeadsN (HStar_computable f))

theorem star_threshold_degree_contract (n degree heads : ℕ)
    (h : MinimumDegreeHeadCountRealized n degree heads) :
    degree ≤ heads ∧ heads ≤ starDegreeBound n degree := by
  obtain ⟨f, rfl, rfl⟩ := h
  exact thresholdDeg_le_HStar_le_starDegreeBound f

theorem threshold_degree_forward (n degree heads : ℕ) :
    (degree ≤ heads ∧ heads ≤ starDegreeBound n degree) → degree ≤ heads :=
  fun h ↦ h.1

theorem threshold_degree_reverse_refuted :
    ¬ ∀ n degree heads : ℕ, degree ≤ heads →
      (degree ≤ heads ∧ heads ≤ starDegreeBound n degree) := by
  intro h
  have hbad := (h 8 2 9 (by decide)).2
  norm_num at hbad

private def checkStrict (report : ComparisonReport) : TermElabM Unit := do
  unless report.req_2_to_1.status == .proved && report.req_1_to_2.status == .proved &&
      report.guarantee_1_to_2.status == .proved && report.guarantee_2_to_1.status == .refuted do
    throwError "unsettled or incorrect strict comparison:\n{report.format}"
  unless report.classification == "source strictly subsumes target under this alignment" do
    throwError "unexpected classification:\n{report.format}"
  logInfo report.format

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``star_universal_contract ``original_universal_contract {
    mode := .logical
    facts := #[``universal_forward, ``universal_reverse_refuted]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound]
  }
  checkStrict report

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``star_degree_contract ``original_degree_contract {
    mode := .logical
    facts := #[``degree_forward, ``degree_reverse_refuted]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound]
  }
  checkStrict report

run_cmd Command.liftTermElabM do
  let report ← compareTheorems ``star_threshold_degree_contract
    ``original_threshold_degree_contract {
    mode := .logical
    facts := #[``threshold_degree_forward, ``threshold_degree_reverse_refuted]
    allowedAxioms? := some #[``propext, ``Classical.choice, ``Quot.sound]
  }
  checkStrict report

end HeadComplexity.StarUpperBoundSubsumption
