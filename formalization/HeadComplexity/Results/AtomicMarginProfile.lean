import HeadComplexity.Results.AtomicMarginEntropy

set_option linter.style.header false

/-!
# Atomic sparsification using the complete signed-margin profile

The smallest certified margin need not describe most inputs. Summing the
individual tail bounds retains that information and weakens the sufficient
sampling requirement, while producing the same exact attention model.
-/

namespace HeadComplexity

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace AtomicMarginCertificate

variable {n : ℕ} {J : Type*} [Fintype J] [MeasurableSpace J]
  [MeasurableSingletonClass J] {mu : Measure J} [IsProbabilityMeasure mu]
  {f : (Fin n → Bool) → Bool}

/-- Actual signed margin at an input, rather than its global lower bound. -/
noncomputable def pointMargin (C : AtomicMarginCertificate f J mu)
    (bits : Fin n → Bool) : ℝ :=
  signedLabel f bits * (C.bias + C.scale * atomicAverage mu C.atom bits)

theorem margin_le_pointMargin (C : AtomicMarginCertificate f J mu)
    (bits : Fin n → Bool) : C.margin ≤ C.pointMargin bits :=
  C.separates bits

theorem pointMargin_pos (C : AtomicMarginCertificate f J mu)
    (bits : Fin n → Bool) : 0 < C.pointMargin bits :=
  C.margin_pos.trans_le (C.margin_le_pointMargin bits)

/-- The full coordinatewise Hoeffding budget at a specified head count. -/
noncomputable def profileBudget (C : AtomicMarginCertificate f J mu) (m : ℕ) : ℝ :=
  ∑ bits : Fin n → Bool,
    Real.exp (-((m : ℝ) * (C.pointMargin bits / C.scale) ^ 2) / 2)

/-- The budget used by the refined uniform compiler. -/
noncomputable def uniformBudget (C : AtomicMarginCertificate f J mu) (m : ℕ) : ℝ :=
  (Fintype.card (Fin n → Bool) : ℝ) *
    Real.exp (-((m : ℝ) * (C.margin / C.scale) ^ 2) / 2)

theorem profileBudget_le_uniformBudget (C : AtomicMarginCertificate f J mu) (m : ℕ) :
    C.profileBudget m ≤ C.uniformBudget m := by
  unfold profileBudget uniformBudget
  calc
    _ ≤ ∑ _bits : Fin n → Bool,
        Real.exp (-((m : ℝ) * (C.margin / C.scale) ^ 2) / 2) := by
      apply Finset.sum_le_sum
      intro bits _
      apply Real.exp_le_exp.mpr
      have hratio : C.margin / C.scale ≤ C.pointMargin bits / C.scale :=
        (div_le_div_iff_of_pos_right C.scale_pos).mpr (C.margin_le_pointMargin bits)
      have hsq := (sq_le_sq₀ (div_pos C.margin_pos C.scale_pos).le
        (div_pos (C.pointMargin_pos bits) C.scale_pos).le).mpr hratio
      nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg m)]
    _ = _ := by simp

/-- Deterministic compilation of any sample satisfying the actual pointwise
loss budgets. All probabilistic samplers feed this same model bridge. -/
theorem computableWithHeadsN_of_empirical_pointLoss
    (C : AtomicMarginCertificate f J mu) {m : ℕ} (hm : 0 < m) (sample : Fin m → J)
    (hsample : ∀ bits, (∑ i : Fin m, signedLabel f bits *
      (atomicAverage mu C.atom bits - (C.atom (sample i)).eval bits)) <
        (m : ℝ) * (C.pointMargin bits / C.scale)) :
    computableWithHeadsN n m f := by
  apply C.computableWithHeadsN_of_empirical_margin sample
  intro bits
  let y : ℝ := signedLabel f bits
  let u : ℝ := atomicAverage mu C.atom bits
  let loss : ℝ := ∑ i : Fin m, y * (u - (C.atom (sample i)).eval bits)
  have hloss : loss < (m : ℝ) * (C.pointMargin bits / C.scale) := hsample bits
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hloss_eq : loss =
      (m : ℝ) * y * u - y * ∑ i : Fin m, (C.atom (sample i)).eval bits := by
    dsimp [loss]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    simp [Finset.mul_sum]
    ring
  have herror : (C.scale / (m : ℝ)) * loss < C.pointMargin bits := by
    calc
      (C.scale / (m : ℝ)) * loss <
          (C.scale / (m : ℝ)) * ((m : ℝ) * (C.pointMargin bits / C.scale)) :=
        mul_lt_mul_of_pos_left hloss (div_pos C.scale_pos hmreal)
      _ = C.pointMargin bits := by field_simp [C.scale_pos.ne', hmreal.ne']
  have hscore :
      y * (C.bias + (C.scale / (m : ℝ)) *
        ∑ i : Fin m, (C.atom (sample i)).eval bits) =
      C.pointMargin bits - (C.scale / (m : ℝ)) * loss := by
    rw [hloss_eq]
    dsimp [pointMargin, y, u]
    field_simp [hmreal.ne']
    ring
  change 0 < y * (C.bias + (C.scale / (m : ℝ)) *
    ∑ i : Fin m, (C.atom (sample i)).eval bits)
  rw [hscore]
  linarith

/-- A strictly feasible profile budget compiles genuine atoms to m heads. -/
theorem computableWithHeadsN_of_profile_budget
    (C : AtomicMarginCertificate f J mu) (m : ℕ) (hm : 0 < m)
    (hbudget : C.profileBudget m < 1) :
    computableWithHeadsN n m f := by
  let value : J → (Fin n → Bool) → ℝ := fun j bits ↦ (C.atom j).eval bits
  obtain ⟨sample, hsample⟩ := exists_empirical_oneSided_approximation_profile
    mu value C.normalized m hm (signedLabel f) (abs_signedLabel f)
    (fun bits ↦ C.pointMargin bits / C.scale)
    (fun bits ↦ (div_pos (C.pointMargin_pos bits) C.scale_pos).le) hbudget
  exact C.computableWithHeadsN_of_empirical_pointLoss hm sample hsample

theorem HStar_le_of_profile_budget (C : AtomicMarginCertificate f J mu)
    (m : ℕ) (hm : 0 < m) (hbudget : C.profileBudget m < 1) :
    HStar n f ≤ m :=
  HStar_le_of_computableWithHeadsN (C.computableWithHeadsN_of_profile_budget m hm hbudget)

/-- The profile condition contains every instance of the original compiler. -/
theorem profile_budget_of_uniform (C : AtomicMarginCertificate f J mu) (m : ℕ)
    (hbudget : C.uniformBudget m < 1) : C.profileBudget m < 1 :=
  (C.profileBudget_le_uniformBudget m).trans_lt hbudget

end AtomicMarginCertificate

/-- A comparison interface for a fixed candidate sample size. Its sampling
rule has a semantic bridge to the new atom compiler, and the old uniform
compiler independently supplies the target guarantee at genuine data. -/
structure AtomicProfileSamplingContract (heads m : ℕ) (fine coarse : ℝ) : Prop where
  m_pos : 0 < m
  fine_le_coarse : fine ≤ coarse
  sampling : fine < 1 → heads ≤ m

theorem AtomicMarginCertificate.profileSamplingContract
    {n : ℕ} {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] {mu : Measure J} [IsProbabilityMeasure mu]
    {f : (Fin n → Bool) → Bool} (C : AtomicMarginCertificate f J mu)
    (m : ℕ) (hm : 0 < m) :
    AtomicProfileSamplingContract (HStar n f) m (C.profileBudget m) (C.uniformBudget m) where
  m_pos := hm
  fine_le_coarse := C.profileBudget_le_uniformBudget m
  sampling := C.HStar_le_of_profile_budget m hm

end HeadComplexity
