import HeadComplexity.Results.AtomicCondition

set_option linter.style.header false

/-!
# Atomic-margin sparsification with the full strict margin

The width-two centered interval gives sub-Gaussian parameter one. Since the
empirical loss is strictly below its threshold, the entire original margin
can be spent. Together these improve the sample constant from 32 to 2 and
the real-valued constant from 33 to 3, with the same certificate hypotheses.
-/

namespace HeadComplexity

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {n : ℕ}

/-- Refined empirical sample count for theorem 195. -/
noncomputable def refinedAtomicSampleCount (n : ℕ) (scale margin : ℝ) : ℕ :=
  ⌈2 * (n + 1 : ℝ) * (scale / margin) ^ 2⌉₊

private theorem refinedAtomicSampleCount_exp_budget (n : ℕ) {scale margin : ℝ}
    (hscale : 0 < scale) (hmargin : 0 < margin) :
    (Fintype.card (Fin n → Bool) : ℝ) *
      Real.exp (-((refinedAtomicSampleCount n scale margin : ℝ) *
        (margin / scale) ^ 2) / 2) < 1 := by
  let X : ℝ := 2 * (n + 1 : ℝ) * (scale / margin) ^ 2
  let m : ℕ := refinedAtomicSampleCount n scale margin
  have hm : X ≤ (m : ℝ) := Nat.le_ceil X
  have hexponent : (n + 1 : ℝ) ≤ (m : ℝ) * (margin / scale) ^ 2 / 2 := by
    calc
      (n + 1 : ℝ) = X * (margin / scale) ^ 2 / 2 := by
        dsimp [X]
        field_simp [hscale.ne', hmargin.ne']
      _ ≤ (m : ℝ) * (margin / scale) ^ 2 / 2 := by gcongr
  have hbase : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    norm_num at h ⊢
    exact h.le
  have hpow : (2 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
    calc
      (2 : ℝ) ^ n ≤ (Real.exp 1) ^ n := by gcongr
      _ = Real.exp (n : ℝ) := by rw [← Real.exp_nat_mul]; simp
  rw [show (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n by simp]
  change (2 : ℝ) ^ n * Real.exp (-((m : ℝ) * (margin / scale) ^ 2) / 2) < 1
  calc
    (2 : ℝ) ^ n * Real.exp (-((m : ℝ) * (margin / scale) ^ 2) / 2) ≤
        Real.exp (n : ℝ) * Real.exp (-(n + 1 : ℝ)) := by
      gcongr
      nlinarith [hexponent]
    _ = Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring
    _ < 1 := Real.exp_lt_one_iff.mpr (by norm_num)

/-- A numeric interface to sampling, with no head bound assumed as a field.
The actual atomic certificates below supply a checked bridge to this contract. -/
structure AtomicMarginSamplingContract (n heads : ℕ) (ratio : ℝ) : Prop where
  ratio_pos : 0 < ratio
  zero_or_one_le_ratio : heads = 0 ∨ 1 ≤ ratio
  sampling : ∀ m : ℕ, 0 < m →
    (Fintype.card (Fin n → Bool) : ℝ) *
      Real.exp (-((m : ℝ) * (1 / ratio) ^ 2) / 2) < 1 → heads ≤ m

namespace AtomicMarginSamplingContract

theorem sample_bound {heads : ℕ} {ratio : ℝ}
    (C : AtomicMarginSamplingContract n heads ratio) :
    heads ≤ refinedAtomicSampleCount n ratio 1 := by
  apply C.sampling
  · apply Nat.ceil_pos.mpr
    have hr := C.ratio_pos
    positivity
  · exact refinedAtomicSampleCount_exp_budget n C.ratio_pos (by norm_num)

theorem real_bound {heads : ℕ} {ratio : ℝ}
    (C : AtomicMarginSamplingContract n heads ratio) :
    (heads : ℝ) ≤ 3 * (n + 1 : ℝ) * ratio ^ 2 := by
  rcases C.zero_or_one_le_ratio with hzero | hr
  · rw [hzero]
    push_cast
    positivity
  · let A : ℝ := (n + 1 : ℝ) * ratio ^ 2
    have hA : 1 ≤ A := by
      have hn1 : (1 : ℝ) ≤ (n + 1 : ℝ) := by norm_num
      have hr2 : 1 ≤ ratio ^ 2 := by nlinarith
      exact one_le_mul_of_one_le_of_one_le hn1 hr2
    have hcast : (heads : ℝ) ≤ (refinedAtomicSampleCount n ratio 1 : ℝ) := by
      exact_mod_cast C.sample_bound
    have hceil : (refinedAtomicSampleCount n ratio 1 : ℝ) < 2 * A + 1 := by
      change (↑⌈2 * (n + 1 : ℝ) * (ratio / 1) ^ 2⌉₊ : ℝ) < 2 * A + 1
      calc
        _ < 2 * (n + 1 : ℝ) * (ratio / 1) ^ 2 + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        _ = 2 * A + 1 := by dsimp [A]; ring
    nlinarith

end AtomicMarginSamplingContract

namespace AtomicMarginCertificate

variable {J : Type*} [Fintype J] [MeasurableSpace J]
  [MeasurableSingletonClass J] {mu : Measure J} [IsProbabilityMeasure mu]
  {f : (Fin n → Bool) → Bool}

/-- Any sharp union-bound budget suffices when the full strict margin is used. -/
theorem computableWithHeadsN_of_exp_budget
    (C : AtomicMarginCertificate f J mu) (m : ℕ) (hm : 0 < m)
    (hbudget : (Fintype.card (Fin n → Bool) : ℝ) *
      Real.exp (-((m : ℝ) * (C.margin / C.scale) ^ 2) / 2) < 1) :
    computableWithHeadsN n m f := by
  let value : J → (Fin n → Bool) → ℝ := fun j bits ↦ (C.atom j).eval bits
  obtain ⟨sample, hsample⟩ := exists_empirical_oneSided_approximation_sharp
    mu value C.normalized m hm (signedLabel f) (abs_signedLabel f)
      (C.margin / C.scale) (div_pos C.margin_pos C.scale_pos).le hbudget
  apply C.computableWithHeadsN_of_empirical_margin sample
  intro bits
  let y : ℝ := signedLabel f bits
  let u : ℝ := atomicAverage mu C.atom bits
  let loss : ℝ := ∑ i : Fin m, y * (u - (C.atom (sample i)).eval bits)
  have hloss : loss < (m : ℝ) * (C.margin / C.scale) := hsample bits
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hloss_eq : loss =
      (m : ℝ) * y * u - y * ∑ i : Fin m, (C.atom (sample i)).eval bits := by
    dsimp [loss]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    simp [Finset.mul_sum]
    ring
  have herror : (C.scale / (m : ℝ)) * loss < C.margin := by
    calc
      (C.scale / (m : ℝ)) * loss <
          (C.scale / (m : ℝ)) * ((m : ℝ) * (C.margin / C.scale)) :=
        mul_lt_mul_of_pos_left hloss (div_pos C.scale_pos hmreal)
      _ = C.margin := by field_simp [C.scale_pos.ne', hmreal.ne']
  have hscore :
      y * (C.bias + (C.scale / (m : ℝ)) *
        ∑ i : Fin m, (C.atom (sample i)).eval bits) =
      y * (C.bias + C.scale * u) - (C.scale / (m : ℝ)) * loss := by
    rw [hloss_eq]
    field_simp [hmreal.ne']
    ring
  change 0 < y * (C.bias + (C.scale / (m : ℝ)) *
    ∑ i : Fin m, (C.atom (sample i)).eval bits)
  rw [hscore]
  have hsep := C.separates bits
  change C.margin ≤ y * (C.bias + C.scale * u) at hsep
  linarith

/-- Theorem 195 with sample constant 2 instead of 32. -/
theorem HStar_le_refinedAtomicSampleCount
    (C : AtomicMarginCertificate f J mu) :
    HStar n f ≤ refinedAtomicSampleCount n C.scale C.margin := by
  apply HStar_le_of_computableWithHeadsN
  apply C.computableWithHeadsN_of_exp_budget
  · apply Nat.ceil_pos.mpr
    have hs := C.scale_pos
    have hm := C.margin_pos
    positivity
  · exact refinedAtomicSampleCount_exp_budget n C.scale_pos C.margin_pos

/-- Semantic bridge from the genuine atom certificate to the comparison
contract. Its sampling field uses no real-valued head-bound theorem. -/
theorem samplingContract (C : AtomicMarginCertificate f J mu) :
    AtomicMarginSamplingContract n (HStar n f) (C.scale / C.margin) where
  ratio_pos := div_pos C.scale_pos C.margin_pos
  zero_or_one_le_ratio := by
    by_cases hn : ¬ ∀ x y, f x = f y
    · exact Or.inr (C.one_le_scale_div_margin hn)
    · push Not at hn
      exact Or.inl ((HStar_eq_zero_iff f).mpr hn)
  sampling := by
    intro m hm hbudget
    apply HStar_le_of_computableWithHeadsN
    apply C.computableWithHeadsN_of_exp_budget m hm
    have heq : 1 / (C.scale / C.margin) = C.margin / C.scale := by field_simp
    rwa [heq] at hbudget

/-- The same certificate hypotheses give real constant 3 instead of 33. -/
theorem HStar_real_le_atomicCondition_refined
    (C : AtomicMarginCertificate f J mu) :
    (HStar n f : ℝ) ≤ 3 * (n + 1 : ℝ) * (C.scale / C.margin) ^ 2 :=
  C.samplingContract.real_bound

end AtomicMarginCertificate

/-- The finite certificate presentation inherits the refined bound. -/
theorem FiniteAtomicMarginCertificate.HStar_real_le_atomicCondition_refined
    {f : (Fin n → Bool) → Bool} (C : FiniteAtomicMarginCertificate f) :
    (HStar n f : ℝ) ≤ 3 * (n + 1 : ℝ) * (C.scale / C.margin) ^ 2 :=
  C.toAtomicMarginCertificate.HStar_real_le_atomicCondition_refined

/-- The literal infimum in theorem 195 satisfies the refined bound, without
assuming that its infimum is attained. -/
theorem HStar_real_le_atomicConditionNumber_refined
    (f : (Fin n → Bool) → Bool) (hn : ¬ ∀ x y, f x = f y) :
    (HStar n f : ℝ) ≤ 3 * (n + 1 : ℝ) * (atomicConditionNumber f) ^ 2 := by
  let K : ℝ := 3 * (n + 1 : ℝ)
  have hK : 0 < K := by dsimp [K]; positivity
  have hq : 0 ≤ (HStar n f : ℝ) / K := by positivity
  have hlower : Real.sqrt ((HStar n f : ℝ) / K) ≤ atomicConditionNumber f := by
    apply le_csInf (atomicConditionRatios_nonempty f hn)
    rintro r ⟨C, rfl⟩
    apply Real.sqrt_le_iff.mpr
    refine ⟨(div_pos C.scale_pos C.margin_pos).le, ?_⟩
    apply (div_le_iff₀ hK).mpr
    simpa [K, mul_assoc, mul_comm, mul_left_comm] using
      C.HStar_real_le_atomicCondition_refined
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg ((HStar n f : ℝ) / K))
    ((Real.sqrt_nonneg _).trans hlower)).mpr hlower
  rw [Real.sq_sqrt hq] at hsq
  have hmul := (div_le_iff₀ hK).mp hsq
  simpa [K, mul_assoc, mul_comm, mul_left_comm] using hmul

/-- The refined natural-valued upper certificate never costs more. -/
theorem refinedAtomicSampleCount_le_atomicSampleCount
    (n : ℕ) (scale margin : ℝ) :
    refinedAtomicSampleCount n scale margin ≤ atomicSampleCount n scale margin := by
  apply Nat.ceil_le_ceil
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (n + 1 : ℝ))
    (sq_nonneg (scale / margin))]

end HeadComplexity
