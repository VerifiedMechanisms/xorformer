import HeadComplexity.Results.AtomicMarginProfile

set_option linter.style.header false

/-!
# Range-sensitive atomic sparsification

Only the output variation among atoms matters to sampling. A separate center
and radius may be used at every Boolean input. Zero-radius inputs are exact
under every sample and consume no tail budget.
-/

namespace HeadComplexity

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Range sampling with exact treatment of zero-width coordinates. -/
theorem exists_empirical_oneSided_approximation_nonnegRange
    {J K : Type*} [Finite J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (mu : Measure J) [IsProbabilityMeasure mu]
    [Fintype K] (v : J → K → ℝ) (center radius : K → ℝ)
    (hr : ∀ k, 0 ≤ radius k) (hv : ∀ j k, |v j k - center k| ≤ radius k)
    (m : ℕ) (hm : 0 < m) (y : K → ℝ) (hy : ∀ k, |y k| = 1)
    (epsilon : K → ℝ) (hepsilon : ∀ k, 0 < epsilon k)
    (hbudget : (∑ k : K, if radius k = 0 then 0 else
      Real.exp (-((m : ℝ) * (epsilon k / radius k) ^ 2) / 2)) < 1) :
    ∃ sample : Fin m → J, ∀ k : K,
      (∑ i : Fin m, y k * (finiteProbabilityAverage mu v k - v (sample i) k)) <
        (m : ℝ) * epsilon k := by
  classical
  let Active := {k : K // radius k ≠ 0}
  have hbudget' : (∑ k : Active,
      Real.exp (-((m : ℝ) * (epsilon k / radius k) ^ 2) / 2)) < 1 := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun k : K ↦ radius k ≠ 0)
      (by intro k; simp) (fun k ↦ Real.exp (-((m : ℝ) * (epsilon k / radius k) ^ 2) / 2))]
    simpa only [Finset.sum_filter, ne_eq, ite_not] using hbudget
  obtain ⟨sample, hsample⟩ := exists_empirical_oneSided_approximation_range
    mu (fun j (k : Active) ↦ v j k) (fun k ↦ center k) (fun k ↦ radius k)
    (fun k ↦ lt_of_le_of_ne (hr k) (Ne.symm k.property)) (fun j k ↦ hv j k)
    m hm (fun k ↦ y k) (fun k ↦ hy k) (fun k ↦ epsilon k)
    (fun k ↦ (hepsilon k).le) hbudget'
  refine ⟨sample, fun k ↦ ?_⟩
  by_cases hk : radius k = 0
  · have hconst (j : J) : v j k = center k := by
      have h := hv j k
      rw [hk] at h
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
    have havg : finiteProbabilityAverage mu v k = center k := by
      simp [finiteProbabilityAverage, hconst]
    simp_rw [havg, hconst, sub_self, mul_zero]
    simpa using mul_pos (show (0 : ℝ) < m by exact_mod_cast hm) (hepsilon k)
  · exact hsample ⟨k, hk⟩

namespace AtomicMarginCertificate

variable {n : ℕ} {J : Type*} [Fintype J] [MeasurableSpace J]
  [MeasurableSingletonClass J] {mu : Measure J} [IsProbabilityMeasure mu]
  {f : (Fin n → Bool) → Bool}

/-- Centers and nonnegative half-widths of the actual atom output intervals. -/
structure OutputRange (C : AtomicMarginCertificate f J mu) where
  center : (Fin n → Bool) → ℝ
  radius : (Fin n → Bool) → ℝ
  radius_nonneg : ∀ bits, 0 ≤ radius bits
  bounded : ∀ j bits, |(C.atom j).eval bits - center bits| ≤ radius bits

/-- Minimum atom output at a fixed input. The probability measure ensures
the finite atom index type is nonempty. -/
noncomputable def minAtomOutput (C : AtomicMarginCertificate f J mu)
    (bits : Fin n → Bool) : ℝ :=
  Finset.univ.inf' (by
    have : Nonempty J := nonempty_of_isProbabilityMeasure mu
    exact Finset.univ_nonempty) (fun j ↦ (C.atom j).eval bits)

/-- Maximum atom output at a fixed input. -/
noncomputable def maxAtomOutput (C : AtomicMarginCertificate f J mu)
    (bits : Fin n → Bool) : ℝ :=
  Finset.univ.sup' (by
    have : Nonempty J := nonempty_of_isProbabilityMeasure mu
    exact Finset.univ_nonempty) (fun j ↦ (C.atom j).eval bits)

theorem minAtomOutput_le (C : AtomicMarginCertificate f J mu) (j : J) (bits : Fin n → Bool) :
    C.minAtomOutput bits ≤ (C.atom j).eval bits :=
  Finset.inf'_le (fun j ↦ (C.atom j).eval bits) (Finset.mem_univ j)

theorem le_maxAtomOutput (C : AtomicMarginCertificate f J mu) (j : J) (bits : Fin n → Bool) :
    (C.atom j).eval bits ≤ C.maxAtomOutput bits :=
  Finset.le_sup' (fun j ↦ (C.atom j).eval bits) (Finset.mem_univ j)

theorem minAtomOutput_le_maxAtomOutput (C : AtomicMarginCertificate f J mu) (bits : Fin n → Bool) :
    C.minAtomOutput bits ≤ C.maxAtomOutput bits := by
  let j : J := Classical.choice (nonempty_of_isProbabilityMeasure mu)
  exact (C.minAtomOutput_le j bits).trans (C.le_maxAtomOutput j bits)

theorem neg_one_le_minAtomOutput (C : AtomicMarginCertificate f J mu) (bits : Fin n → Bool) :
    -1 ≤ C.minAtomOutput bits := by
  apply Finset.le_inf'
  intro j _
  exact (abs_le.mp (C.normalized j bits)).1

theorem maxAtomOutput_le_one (C : AtomicMarginCertificate f J mu) (bits : Fin n → Bool) :
    C.maxAtomOutput bits ≤ 1 := by
  apply Finset.sup'_le
  intro j _
  exact (abs_le.mp (C.normalized j bits)).2

/-- Canonical optimal interval center and half-width for the given outputs.
No additional data or regularity hypothesis is needed. -/
noncomputable def tightOutputRange (C : AtomicMarginCertificate f J mu) : C.OutputRange where
  center := fun bits ↦ (C.minAtomOutput bits + C.maxAtomOutput bits) / 2
  radius := fun bits ↦ (C.maxAtomOutput bits - C.minAtomOutput bits) / 2
  radius_nonneg := by intro bits; linarith [C.minAtomOutput_le_maxAtomOutput bits]
  bounded := by
    intro j bits
    apply abs_le.mpr
    constructor <;> linarith [C.minAtomOutput_le j bits, C.le_maxAtomOutput j bits]

theorem tightOutputRange_radius_le_one (C : AtomicMarginCertificate f J mu) (bits : Fin n → Bool) :
    C.tightOutputRange.radius bits ≤ 1 := by
  change (C.maxAtomOutput bits - C.minAtomOutput bits) / 2 ≤ 1
  linarith [C.neg_one_le_minAtomOutput bits, C.maxAtomOutput_le_one bits]

/-- The canonical half-width is minimal among all enclosing intervals,
including intervals with input-dependent nonlinear centers. -/
theorem tightOutputRange_radius_minimal (C : AtomicMarginCertificate f J mu)
    (R : C.OutputRange) (bits : Fin n → Bool) :
    C.tightOutputRange.radius bits ≤ R.radius bits := by
  have hlo : R.center bits - R.radius bits ≤ C.minAtomOutput bits := by
    apply Finset.le_inf'
    intro j _
    linarith [(abs_le.mp (R.bounded j bits)).1]
  have hhi : C.maxAtomOutput bits ≤ R.center bits + R.radius bits := by
    apply Finset.sup'_le
    intro j _
    linarith [(abs_le.mp (R.bounded j bits)).2]
  change (C.maxAtomOutput bits - C.minAtomOutput bits) / 2 ≤ R.radius bits
  linarith

/-- Every old normalized certificate has a default range presentation. -/
def unitOutputRange (C : AtomicMarginCertificate f J mu) : C.OutputRange where
  center := fun _ ↦ 0
  radius := fun _ ↦ 1
  radius_nonneg := fun _ ↦ by norm_num
  bounded := by simpa using C.normalized

/-- Zero-width coordinates have zero failure probability. -/
noncomputable def rangeBudget (C : AtomicMarginCertificate f J mu)
    (R : C.OutputRange) (m : ℕ) : ℝ :=
  ∑ bits : Fin n → Bool, if R.radius bits = 0 then 0 else
    Real.exp (-((m : ℝ) * ((C.pointMargin bits / C.scale) / R.radius bits) ^ 2) / 2)

theorem unitOutputRange_budget (C : AtomicMarginCertificate f J mu) (m : ℕ) :
    C.rangeBudget C.unitOutputRange m = C.profileBudget m := by
  simp [rangeBudget, unitOutputRange, profileBudget]

theorem rangeBudget_le_profileBudget (C : AtomicMarginCertificate f J mu)
    (R : C.OutputRange) (hr : ∀ bits, R.radius bits ≤ 1) (m : ℕ) :
    C.rangeBudget R m ≤ C.profileBudget m := by
  unfold rangeBudget profileBudget
  apply Finset.sum_le_sum
  intro bits _
  split_ifs with hzero
  · exact (Real.exp_pos _).le
  · have hrpos : 0 < R.radius bits := lt_of_le_of_ne (R.radius_nonneg bits) (Ne.symm hzero)
    have heps : 0 < C.pointMargin bits / C.scale := div_pos (C.pointMargin_pos bits) C.scale_pos
    have hratio : C.pointMargin bits / C.scale ≤
        (C.pointMargin bits / C.scale) / R.radius bits := by
      apply (le_div_iff₀ hrpos).mpr
      exact mul_le_of_le_one_right heps.le (hr bits)
    have hsq := (sq_le_sq₀ heps.le (div_pos heps hrpos).le).mpr hratio
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg m)]

/-- Range-sensitive, pointwise-margin compilation into the original model. -/
theorem computableWithHeadsN_of_range_budget (C : AtomicMarginCertificate f J mu)
    (R : C.OutputRange) (m : ℕ) (hm : 0 < m) (hb : C.rangeBudget R m < 1) :
    computableWithHeadsN n m f := by
  let value : J → (Fin n → Bool) → ℝ := fun j bits ↦ (C.atom j).eval bits
  obtain ⟨sample, hsample⟩ := exists_empirical_oneSided_approximation_nonnegRange
    mu value R.center R.radius R.radius_nonneg R.bounded m hm
    (signedLabel f) (abs_signedLabel f) (fun bits ↦ C.pointMargin bits / C.scale)
    (fun bits ↦ div_pos (C.pointMargin_pos bits) C.scale_pos) hb
  exact C.computableWithHeadsN_of_empirical_pointLoss hm sample hsample

theorem HStar_le_of_range_budget (C : AtomicMarginCertificate f J mu)
    (R : C.OutputRange) (m : ℕ) (hm : 0 < m) (hb : C.rangeBudget R m < 1) :
    HStar n f ≤ m :=
  HStar_le_of_computableWithHeadsN (C.computableWithHeadsN_of_range_budget R m hm hb)

/-- Genuine atom data provide the complete checked comparison interface. -/
theorem rangeSamplingContract (C : AtomicMarginCertificate f J mu)
    (R : C.OutputRange) (hr : ∀ bits, R.radius bits ≤ 1) (m : ℕ) (hm : 0 < m) :
    AtomicProfileSamplingContract (HStar n f) m (C.rangeBudget R m) (C.profileBudget m) where
  m_pos := hm
  fine_le_coarse := C.rangeBudget_le_profileBudget R hr m
  sampling := C.HStar_le_of_range_budget R m hm

/-- The fully automatic range budget for the original certificate. -/
noncomputable def tightRangeBudget (C : AtomicMarginCertificate f J mu) (m : ℕ) : ℝ :=
  C.rangeBudget C.tightOutputRange m

theorem tightRangeBudget_le_uniformBudget (C : AtomicMarginCertificate f J mu) (m : ℕ) :
    C.tightRangeBudget m ≤ C.uniformBudget m :=
  (C.rangeBudget_le_profileBudget C.tightOutputRange C.tightOutputRange_radius_le_one m).trans
    (C.profileBudget_le_uniformBudget m)

theorem HStar_le_of_tightRange_budget (C : AtomicMarginCertificate f J mu)
    (m : ℕ) (hm : 0 < m) (hb : C.tightRangeBudget m < 1) : HStar n f ≤ m :=
  C.HStar_le_of_range_budget C.tightOutputRange m hm hb

theorem tightRangeSamplingContract (C : AtomicMarginCertificate f J mu)
    (m : ℕ) (hm : 0 < m) :
    AtomicProfileSamplingContract (HStar n f) m (C.tightRangeBudget m) (C.uniformBudget m) where
  m_pos := hm
  fine_le_coarse := C.tightRangeBudget_le_uniformBudget m
  sampling := C.HStar_le_of_tightRange_budget m hm

end AtomicMarginCertificate

end HeadComplexity
