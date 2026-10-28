import HeadComplexity.Results.AtomicMarginEntropy

set_option linter.style.header false

/-!
# A gap above atomic condition number one

A first-moment deficit argument forces a single genuine atom to classify
every input when the condition ratio is sufficiently close to one. Passing
to the literal infimum needs no attainment assumption.
-/

namespace HeadComplexity

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- A uniform gap for functions requiring at least two heads. -/
noncomputable def atomicOneHeadGap (n : ℕ) : ℝ := 1 / max 1 ((2 : ℝ) ^ n - 1)

theorem atomicOneHeadGap_pos (n : ℕ) : 0 < atomicOneHeadGap n := by
  unfold atomicOneHeadGap
  positivity

namespace AtomicMarginCertificate

variable {n : ℕ} {J : Type*} [Fintype J] [MeasurableSpace J]
  [MeasurableSingletonClass J] {mu : Measure J} [IsProbabilityMeasure mu]
  {f : (Fin n → Bool) → Bool}

theorem abs_bias_le_scale_sub_margin (C : AtomicMarginCertificate f J mu)
    (hn : ¬ ∀ x y, f x = f y) : |C.bias| ≤ C.scale - C.margin := by
  have htf : ∃ x y, f x = true ∧ f y = false := by
    push Not at hn
    obtain ⟨x, y, hxy⟩ := hn
    cases hx : f x <;> cases hy : f y
    · exact (hxy (by rw [hx, hy])).elim
    · exact ⟨y, x, hy, hx⟩
    · exact ⟨x, y, hx, hy⟩
    · exact (hxy (by rw [hx, hy])).elim
  obtain ⟨x, y, hx, hy⟩ := htf
  let value : J → (Fin n → Bool) → ℝ := fun j bits ↦ (C.atom j).eval bits
  have hux : atomicAverage mu C.atom x ∈ Set.Icc (-1 : ℝ) 1 :=
    finiteProbabilityAverage_mem_Icc mu value C.normalized x
  have huy : atomicAverage mu C.atom y ∈ Set.Icc (-1 : ℝ) 1 :=
    finiteProbabilityAverage_mem_Icc mu value C.normalized y
  have hsx := C.separates x
  have hsy := C.separates y
  rw [signedLabel_of_true hx, one_mul] at hsx
  rw [signedLabel_of_false hy] at hsy
  have hmx := mul_le_mul_of_nonneg_left hux.2 C.scale_pos.le
  have hmy := mul_le_mul_of_nonneg_left huy.1 C.scale_pos.le
  apply abs_le.mpr
  constructor <;> linarith

/-- The nonnegative loss of an individual normalized output against a label. -/
noncomputable def outputDeficit (C : AtomicMarginCertificate f J mu) (j : J)
    (bits : Fin n → Bool) : ℝ := 1 - signedLabel f bits * (C.atom j).eval bits

theorem outputDeficit_nonneg (C : AtomicMarginCertificate f J mu) (j : J)
    (bits : Fin n → Bool) : 0 ≤ C.outputDeficit j bits := by
  have h : |signedLabel f bits * (C.atom j).eval bits| ≤ 1 := by
    rw [abs_mul, abs_signedLabel, one_mul]
    exact C.normalized j bits
  exact sub_nonneg.mpr (abs_le.mp h).2

theorem integral_outputDeficit_le (C : AtomicMarginCertificate f J mu)
    (hn : ¬ ∀ x y, f x = f y) (bits : Fin n → Bool) :
    (∫ j, C.outputDeficit j bits ∂mu) ≤ 2 * (C.scale - C.margin) / C.scale := by
  have hi : (∫ j, C.outputDeficit j bits ∂mu) =
      1 - signedLabel f bits * atomicAverage mu C.atom bits := by
    unfold outputDeficit atomicAverage
    rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul]
    simp
  have hb : signedLabel f bits * C.bias ≤ C.scale - C.margin := by
    calc
      _ ≤ |signedLabel f bits * C.bias| := le_abs_self _
      _ = |C.bias| := by rw [abs_mul, abs_signedLabel, one_mul]
      _ ≤ _ := C.abs_bias_le_scale_sub_margin hn
  rw [hi]
  apply (le_div_iff₀ C.scale_pos).mpr
  have hs := C.separates bits
  nlinarith

/-- Total label deficit below two forces strict ordering between every true
and false input. The selected atom may choose its own readout threshold. -/
theorem computableWithOneHead_of_totalDeficit_lt_two
    (C : AtomicMarginCertificate f J mu) (hn : ¬ ∀ x y, f x = f y)
    (j : J) (hj : (∑ bits : Fin n → Bool, C.outputDeficit j bits) < 2) :
    computableWithHeadsN n 1 f := by
  classical
  have hfalse : ∃ bits, f bits = false := by
    by_contra h
    push Not at h
    apply hn
    intro x y
    have hx : f x = true := Bool.eq_true_of_not_eq_false (h x)
    have hy : f y = true := Bool.eq_true_of_not_eq_false (h y)
    rw [hx, hy]
  have horder (x y : Fin n → Bool) (hx : f x = true) (hy : f y = false) :
      (C.atom j).eval y < (C.atom j).eval x := by
    have hxy : x ≠ y := by intro h; subst y; simp [hx] at hy
    have hsum : (∑ bits ∈ ({x, y} : Finset (Fin n → Bool)), C.outputDeficit j bits) ≤
        ∑ bits : Fin n → Bool, C.outputDeficit j bits :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun bits _ _ ↦
        C.outputDeficit_nonneg j bits)
    rw [Finset.sum_pair hxy] at hsum
    simp only [outputDeficit, signedLabel_of_true hx, signedLabel_of_false hy,
      one_mul, neg_mul, one_mul] at hsum
    dsimp [outputDeficit] at hj
    linarith
  let negatives : Finset (Fin n → Bool) := Finset.univ.filter fun bits ↦ f bits = false
  have hneg : negatives.Nonempty := by
    obtain ⟨bits, hbits⟩ := hfalse
    exact ⟨bits, by simp [negatives, hbits]⟩
  let cutoff : ℝ := negatives.sup' hneg (fun bits ↦ (C.atom j).eval bits)
  apply computable_of_fracComputable
  refine ⟨(fun _ : Fin 1 ↦ C.atom j), -cutoff, fun bits ↦ ?_⟩
  simp only [Fin.sum_univ_one]
  by_cases hbits : f bits = true
  · have hc : cutoff < (C.atom j).eval bits := by
      dsimp [cutoff]
      rw [Finset.sup'_lt_iff]
      intro y hy
      exact horder bits y hbits (by simpa [negatives] using hy)
    exact ⟨fun _ ↦ hbits, fun _ ↦ by linarith⟩
  · have hf : f bits = false := Bool.eq_false_of_not_eq_true hbits
    have hc : (C.atom j).eval bits ≤ cutoff :=
      Finset.le_sup' (fun bits ↦ (C.atom j).eval bits) (by simp [negatives, hf])
    constructor
    · intro hpos
      linarith
    · intro htrue
      exact (hbits htrue).elim

/-- A first-moment argument, without independence or concentration, finds
one existing atom whose deficit is small simultaneously at all inputs. -/
theorem computableWithOneHead_of_ratio_lt_gap (C : AtomicMarginCertificate f J mu)
    (hn : ¬ ∀ x y, f x = f y)
    (hr : C.scale / C.margin < 1 + atomicOneHeadGap n) :
    computableWithHeadsN n 1 f := by
  let D : J → ℝ := fun j ↦ ∑ bits : Fin n → Bool, C.outputDeficit j bits
  have hmean : (∫ j, D j ∂mu) ≤
      (2 * (2 : ℝ) ^ n) * (C.scale - C.margin) / C.scale := by
    dsimp [D]
    rw [integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
    calc
      _ ≤ ∑ _bits : Fin n → Bool, 2 * (C.scale - C.margin) / C.scale :=
        Finset.sum_le_sum (fun bits _ ↦ C.integral_outputDeficit_le hn bits)
      _ = _ := by simp; ring
  have hn0 : n ≠ 0 := by
    intro hzero
    subst n
    apply hn
    intro x y
    congr 1
    exact Subsingleton.elim x y
  have hpow : 2 ≤ (2 : ℝ) ^ n := by
    have hp : 1 ≤ (2 : ℝ) ^ (n - 1) := one_le_pow₀ (by norm_num)
    rw [show n = (n - 1) + 1 by omega, pow_succ]
    nlinarith
  have hden : 0 < (2 : ℝ) ^ n - 1 := by linarith
  have hr' : C.scale / C.margin - 1 < 1 / ((2 : ℝ) ^ n - 1) := by
    have hr0 : C.scale / C.margin < 1 + 1 / ((2 : ℝ) ^ n - 1) := by
      simpa only [atomicOneHeadGap, max_eq_right (by linarith : (1 : ℝ) ≤ 2 ^ n - 1)] using hr
    linarith
  have hs := (lt_div_iff₀ hden).mp hr'
  have hid : (C.scale / C.margin - 1) * ((2 : ℝ) ^ n - 1) =
      ((C.scale - C.margin) * ((2 : ℝ) ^ n - 1)) / C.margin := by
    field_simp [C.margin_pos.ne']
  rw [hid] at hs
  have hmain := (div_lt_one C.margin_pos).mp hs
  have hstrict : (∫ j, D j ∂mu) < 2 := by
    apply hmean.trans_lt
    apply (div_lt_iff₀ C.scale_pos).mpr
    nlinarith
  have hex : ∃ j, D j < 2 := by
    by_contra h
    push Not at h
    have hi := integral_mono (μ := mu)
      (f := fun _ : J ↦ (2 : ℝ)) (g := D)
      Integrable.of_finite Integrable.of_finite h
    simp only [integral_const, probReal_univ, one_smul] at hi
    linarith
  obtain ⟨j, hj⟩ := hex
  exact C.computableWithOneHead_of_totalDeficit_lt_two hn j hj

theorem HStar_le_one_of_ratio_lt_gap (C : AtomicMarginCertificate f J mu)
    (hr : C.scale / C.margin < 1 + atomicOneHeadGap n) : HStar n f ≤ 1 := by
  by_cases hn : ∀ x y, f x = f y
  · rw [(HStar_eq_zero_iff f).mpr hn]
    omega
  · exact HStar_le_of_computableWithHeadsN (C.computableWithOneHead_of_ratio_lt_gap hn hr)

/-- Balanced labels cancel the readout bias in the expected total deficit.
This gives a stronger quantitative obstruction than the general gap. -/
theorem balanced_ratio_lower_bound (C : AtomicMarginCertificate f J mu)
    (hn : 2 ≤ n) (hbal : (∑ bits : Fin n → Bool, signedLabel f bits) = 0)
    (hH : 2 ≤ HStar n f) :
    (2 : ℝ) ^ n / ((2 : ℝ) ^ n - 2) ≤ C.scale / C.margin := by
  have hnc : ¬ ∀ x y, f x = f y := by
    intro h
    rw [(HStar_eq_zero_iff f).mpr h] at hH
    omega
  let D : J → ℝ := fun j ↦ ∑ bits : Fin n → Bool, C.outputDeficit j bits
  have hD (j : J) : 2 ≤ D j := by
    by_contra h
    have hhead := HStar_le_of_computableWithHeadsN
      (C.computableWithOneHead_of_totalDeficit_lt_two hnc j (lt_of_not_ge h))
    omega
  have hlow : 2 ≤ ∫ j, D j ∂mu := by
    have h := integral_mono (μ := mu) (f := fun _ : J ↦ (2 : ℝ))
      (g := D) Integrable.of_finite Integrable.of_finite hD
    simpa using h
  have hcoord (bits : Fin n → Bool) :
      (∫ j, C.outputDeficit j bits ∂mu) * C.scale ≤
        C.scale - C.margin + signedLabel f bits * C.bias := by
    have hi : (∫ j, C.outputDeficit j bits ∂mu) =
        1 - signedLabel f bits * atomicAverage mu C.atom bits := by
      unfold outputDeficit atomicAverage
      rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul]
      simp
    rw [hi]
    have hs := C.separates bits
    nlinarith
  have hsum : (∫ j, D j ∂mu) * C.scale ≤
      (2 : ℝ) ^ n * (C.scale - C.margin) := by
    dsimp [D]
    rw [integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite), Finset.sum_mul]
    calc
      _ ≤ ∑ bits : Fin n → Bool, (C.scale - C.margin + signedLabel f bits * C.bias) :=
        Finset.sum_le_sum (fun bits _ ↦ hcoord bits)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hbal]
        simp
        ring
  have hpow : 4 ≤ (2 : ℝ) ^ n := by
    have hp : 1 ≤ (2 : ℝ) ^ (n - 2) := one_le_pow₀ (by norm_num)
    rw [show n = (n - 2) + 2 by omega, pow_add]
    norm_num
    nlinarith
  have hden : 0 < (2 : ℝ) ^ n - 2 := by linarith
  apply (div_le_div_iff₀ hden C.margin_pos).mpr
  have hmul := mul_le_mul_of_nonneg_right hlow C.scale_pos.le
  nlinarith

end AtomicMarginCertificate

/-- The criterion passes to the literal infimum without an optimizer. -/
theorem HStar_le_one_of_atomicConditionNumber_lt_gap
    {n : ℕ} (f : (Fin n → Bool) → Bool) (hn : ¬ ∀ x y, f x = f y)
    (hk : atomicConditionNumber f < 1 + atomicOneHeadGap n) : HStar n f ≤ 1 := by
  obtain ⟨r, ⟨C, hr⟩, hsmall⟩ :=
    exists_lt_of_csInf_lt (atomicConditionRatios_nonempty f hn) hk
  rw [hr] at hsmall
  exact C.toAtomicMarginCertificate.HStar_le_one_of_ratio_lt_gap hsmall

/-- Every function requiring at least two heads has a genuine condition gap. -/
theorem one_add_gap_le_atomicConditionNumber_of_two_le_HStar
    {n : ℕ} (f : (Fin n → Bool) → Bool) (hH : 2 ≤ HStar n f) :
    1 + atomicOneHeadGap n ≤ atomicConditionNumber f := by
  have hn : ¬ ∀ x y, f x = f y := by
    intro h
    rw [(HStar_eq_zero_iff f).mpr h] at hH
    omega
  by_contra h
  have hsmall : atomicConditionNumber f < 1 + atomicOneHeadGap n := lt_of_not_ge h
  have h := HStar_le_one_of_atomicConditionNumber_lt_gap f hn hsmall
  omega

/-- The stronger balanced obstruction also passes to the literal infimum. -/
theorem balanced_atomicConditionNumber_lower_bound {n : ℕ}
    (f : (Fin n → Bool) → Bool) (hn : 2 ≤ n)
    (hbal : (∑ bits : Fin n → Bool, signedLabel f bits) = 0) (hH : 2 ≤ HStar n f) :
    (2 : ℝ) ^ n / ((2 : ℝ) ^ n - 2) ≤ atomicConditionNumber f := by
  have hnc : ¬ ∀ x y, f x = f y := by
    intro h
    rw [(HStar_eq_zero_iff f).mpr h] at hH
    omega
  apply le_csInf (atomicConditionRatios_nonempty f hnc)
  rintro r ⟨C, rfl⟩
  exact C.toAtomicMarginCertificate.balanced_ratio_lower_bound hn hbal hH

/-- Joint strengthening of the old universal lower endpoint. -/
theorem atomicConditionNumber_lower_bounds {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hn : ¬ ∀ x y, f x = f y) :
    1 ≤ atomicConditionNumber f ∧
      (2 ≤ HStar n f → 1 + atomicOneHeadGap n ≤ atomicConditionNumber f) ∧
      (2 ≤ n → (∑ bits : Fin n → Bool, signedLabel f bits) = 0 →
        2 ≤ HStar n f → (2 : ℝ) ^ n / ((2 : ℝ) ^ n - 2) ≤ atomicConditionNumber f) :=
  ⟨one_le_atomicConditionNumber f hn,
    one_add_gap_le_atomicConditionNumber_of_two_le_HStar f,
    fun hdim hbal hheads ↦ balanced_atomicConditionNumber_lower_bound f hdim hbal hheads⟩

end HeadComplexity
