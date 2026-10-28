import HeadComplexity.Results.AtomicMarginRefinement

set_option linter.style.header false

/-!
# Entropy-sensitive atomic-margin sparsification

Retaining the exact logarithm of the number of Boolean inputs removes the
exponential slack in the union budget. All old certificate hypotheses and
all old declarations are preserved.
-/

namespace HeadComplexity

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n : ℕ}

/-- The least positive integer strictly above the sharp Hoeffding threshold.
The strict successor is essential when the threshold is an integer. -/
noncomputable def entropyAtomicSampleCount (n : ℕ) (scale margin : ℝ) : ℕ :=
  ⌊2 * (n : ℝ) * Real.log 2 * (scale / margin) ^ 2⌋₊ + 1

theorem entropyAtomicSampleCount_exp_budget (n : ℕ) {scale margin : ℝ}
    (hscale : 0 < scale) (hmargin : 0 < margin) :
    (Fintype.card (Fin n → Bool) : ℝ) *
      Real.exp (-((entropyAtomicSampleCount n scale margin : ℝ) *
        (margin / scale) ^ 2) / 2) < 1 := by
  let X : ℝ := 2 * (n : ℝ) * Real.log 2 * (scale / margin) ^ 2
  have hm : X < (entropyAtomicSampleCount n scale margin : ℝ) := by
    simpa [entropyAtomicSampleCount, X] using Nat.lt_floor_add_one X
  have hpos : 0 < (margin / scale) ^ 2 / 2 := by positivity
  have hexponent : (n : ℝ) * Real.log 2 <
      (entropyAtomicSampleCount n scale margin : ℝ) * (margin / scale) ^ 2 / 2 := by
    calc
      (n : ℝ) * Real.log 2 = X * ((margin / scale) ^ 2 / 2) := by
        dsimp [X]
        field_simp [hscale.ne', hmargin.ne']
      _ < _ := by simpa [mul_div_assoc] using mul_lt_mul_of_pos_right hm hpos
  rw [show (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n by simp]
  calc
    (2 : ℝ) ^ n * Real.exp (-((entropyAtomicSampleCount n scale margin : ℝ) *
        (margin / scale) ^ 2) / 2) =
        Real.exp ((n : ℝ) * Real.log 2 -
          (entropyAtomicSampleCount n scale margin : ℝ) * (margin / scale) ^ 2 / 2) := by
      rw [show (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)],
        ← Real.exp_add]
      congr 1
      ring
    _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)

namespace AtomicMarginSamplingContract

theorem entropy_sample_bound {heads : ℕ} {ratio : ℝ}
    (C : AtomicMarginSamplingContract n heads ratio) :
    heads ≤ entropyAtomicSampleCount n ratio 1 := by
  apply C.sampling
  · exact Nat.succ_pos _
  · exact entropyAtomicSampleCount_exp_budget n C.ratio_pos (by norm_num)

/-- Exact logarithmic real endpoint, including only one rounding unit. -/
theorem entropy_additive_bound {heads : ℕ} {ratio : ℝ}
    (C : AtomicMarginSamplingContract n heads ratio) :
    (heads : ℝ) ≤ 2 * (n : ℝ) * Real.log 2 * ratio ^ 2 + 1 := by
  have hcast : (heads : ℝ) ≤ (entropyAtomicSampleCount n ratio 1 : ℝ) := by
    exact_mod_cast C.entropy_sample_bound
  have hf := Nat.floor_le (by positivity :
    (0 : ℝ) ≤ 2 * (n : ℝ) * Real.log 2 * ratio ^ 2)
  simp only [entropyAtomicSampleCount, div_one, Nat.cast_add, Nat.cast_one] at hcast
  linarith

/-- A homogeneous endpoint that also passes to an unattained infimum. -/
theorem entropy_real_bound {heads : ℕ} {ratio : ℝ}
    (C : AtomicMarginSamplingContract n heads ratio) :
    (heads : ℝ) ≤ (2 * (n : ℝ) * Real.log 2 + 1) * ratio ^ 2 := by
  rcases C.zero_or_one_le_ratio with hzero | hr
  · rw [hzero]
    push_cast
    positivity
  · have hr2 : 1 ≤ ratio ^ 2 := by nlinarith
    have h := C.entropy_additive_bound
    nlinarith

end AtomicMarginSamplingContract

namespace AtomicMarginCertificate

variable {J : Type*} [Fintype J] [MeasurableSpace J]
  [MeasurableSingletonClass J] {mu : Measure J} [IsProbabilityMeasure mu]
  {f : (Fin n → Bool) → Bool}

theorem HStar_le_entropyAtomicSampleCount
    (C : AtomicMarginCertificate f J mu) :
    HStar n f ≤ entropyAtomicSampleCount n C.scale C.margin := by
  apply HStar_le_of_computableWithHeadsN
  apply C.computableWithHeadsN_of_exp_budget
  · exact Nat.succ_pos _
  · exact entropyAtomicSampleCount_exp_budget n C.scale_pos C.margin_pos

/-- A pointwise improvement without changing even the constant-function case. -/
theorem HStar_le_min_entropy_refined
    (C : AtomicMarginCertificate f J mu) :
    HStar n f ≤ min (entropyAtomicSampleCount n C.scale C.margin)
      (refinedAtomicSampleCount n C.scale C.margin) :=
  le_min C.HStar_le_entropyAtomicSampleCount C.HStar_le_refinedAtomicSampleCount

theorem HStar_real_le_atomicCondition_entropy
    (C : AtomicMarginCertificate f J mu) :
    (HStar n f : ℝ) ≤
      (2 * (n : ℝ) * Real.log 2 + 1) * (C.scale / C.margin) ^ 2 :=
  C.samplingContract.entropy_real_bound

theorem HStar_real_le_atomicCondition_entropy_additive
    (C : AtomicMarginCertificate f J mu) :
    (HStar n f : ℝ) ≤
      2 * (n : ℝ) * Real.log 2 * (C.scale / C.margin) ^ 2 + 1 :=
  C.samplingContract.entropy_additive_bound

end AtomicMarginCertificate

theorem FiniteAtomicMarginCertificate.HStar_real_le_atomicCondition_entropy
    {f : (Fin n → Bool) → Bool} (C : FiniteAtomicMarginCertificate f) :
    (HStar n f : ℝ) ≤
      (2 * (n : ℝ) * Real.log 2 + 1) * (C.scale / C.margin) ^ 2 :=
  C.toAtomicMarginCertificate.HStar_real_le_atomicCondition_entropy

/-- The entropy coefficient improves the literal atomic condition number,
without an attainment hypothesis. -/
theorem HStar_real_le_atomicConditionNumber_entropy
    (f : (Fin n → Bool) → Bool) (hn : ¬ ∀ x y, f x = f y) :
    (HStar n f : ℝ) ≤
      (2 * (n : ℝ) * Real.log 2 + 1) * (atomicConditionNumber f) ^ 2 := by
  let K : ℝ := 2 * (n : ℝ) * Real.log 2 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hq : 0 ≤ (HStar n f : ℝ) / K := by positivity
  have hlower : Real.sqrt ((HStar n f : ℝ) / K) ≤ atomicConditionNumber f := by
    apply le_csInf (atomicConditionRatios_nonempty f hn)
    rintro r ⟨C, rfl⟩
    apply Real.sqrt_le_iff.mpr
    refine ⟨(div_pos C.scale_pos C.margin_pos).le, ?_⟩
    apply (div_le_iff₀ hK).mpr
    simpa [K, mul_assoc, mul_comm, mul_left_comm] using
      C.HStar_real_le_atomicCondition_entropy
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg ((HStar n f : ℝ) / K))
    ((Real.sqrt_nonneg _).trans hlower)).mpr hlower
  rw [Real.sq_sqrt hq] at hsq
  have hmul := (div_le_iff₀ hK).mp hsq
  simpa [K, mul_assoc, mul_comm, mul_left_comm] using hmul

/-- Strict endpoint improvement over the refined coefficient 3. -/
theorem entropy_endpoint_lt_refined (n : ℕ) {ratio : ℝ} (hr : 0 < ratio) :
    (2 * (n : ℝ) * Real.log 2 + 1) * ratio ^ 2 <
      3 * (n + 1 : ℝ) * ratio ^ 2 := by
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hlog.le (by positivity : (0 : ℝ) ≤ 2 * n)
  have hc : 2 * (n : ℝ) * Real.log 2 + 1 < 3 * (n + 1 : ℝ) := by nlinarith
  exact mul_lt_mul_of_pos_right hc (sq_pos_of_pos hr)

/-- Even after integer rounding, every nonconstant certificate improves. -/
theorem entropy_sampleCount_lt_refined (n : ℕ) {scale margin : ℝ}
    (hr : 1 ≤ scale / margin) :
    entropyAtomicSampleCount n scale margin < refinedAtomicSampleCount n scale margin := by
  let r : ℝ := scale / margin
  have hr2 : 1 ≤ r ^ 2 := by dsimp [r]; nlinarith
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  have hmul : 2 * (n : ℝ) * Real.log 2 * r ^ 2 ≤ 2 * (n : ℝ) * r ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 2 * n * r ^ 2)]
  have hf := Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) * Real.log 2 * r ^ 2)
  have hc := Nat.le_ceil (2 * (n + 1 : ℝ) * r ^ 2)
  have hcast : (entropyAtomicSampleCount n scale margin : ℝ) <
      (refinedAtomicSampleCount n scale margin : ℝ) := by
    simp only [entropyAtomicSampleCount, refinedAtomicSampleCount, Nat.cast_add, Nat.cast_one]
    change (↑⌊2 * (n : ℝ) * Real.log 2 * r ^ 2⌋₊ : ℝ) + 1 <
      (↑⌈2 * (n + 1 : ℝ) * r ^ 2⌉₊ : ℝ)
    nlinarith
  exact_mod_cast hcast

end HeadComplexity
