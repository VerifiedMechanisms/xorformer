import HeadComplexity.Atoms.AtomicMargin

set_option linter.style.header false

/-!
# Finite one-sided empirical approximation

An output-bounded finite probability average admits a uniform one-sided
empirical approximation. The proof samples independently, applies Mathlib's
sub-Gaussian Hoeffding inequality coordinatewise, and then uses a finite union
bound.
-/

namespace HeadComplexity

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- A coordinate of a finite probability average. -/
noncomputable def finiteProbabilityAverage
    {J K : Type*} [MeasurableSpace J] (mu : Measure J)
    (v : J → K → ℝ) (k : K) : ℝ :=
  ∫ j, v j k ∂mu

theorem finiteProbabilityAverage_mem_Icc
    {J K : Type*} [Finite J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (mu : Measure J) [IsProbabilityMeasure mu]
    (v : J → K → ℝ) (hv : ∀ j k, |v j k| ≤ 1) (k : K) :
    finiteProbabilityAverage mu v k ∈ Set.Icc (-1 : ℝ) 1 := by
  have hvlo : ∀ j, (-1 : ℝ) ≤ v j k :=
    fun j ↦ (abs_le.mp (hv j k)).1
  have hvhi : ∀ j, v j k ≤ (1 : ℝ) :=
    fun j ↦ (abs_le.mp (hv j k)).2
  have hlo := integral_mono (μ := mu)
    Integrable.of_finite Integrable.of_finite hvlo
  have hhi := integral_mono (μ := mu)
    Integrable.of_finite Integrable.of_finite hvhi
  constructor
  · change (-1 : ℝ) ≤ ∫ j, v j k ∂mu
    calc
      (-1 : ℝ) = ∫ _j : J, (-1 : ℝ) ∂mu := by simp
      _ ≤ ∫ j, v j k ∂mu := hlo
  · change (∫ j, v j k ∂mu) ≤ (1 : ℝ)
    calc
      (∫ j, v j k ∂mu) ≤ ∫ _j : J, (1 : ℝ) ∂mu := hhi
      _ = (1 : ℝ) := by simp

private theorem coordinate_integral
    {J K : Type*} [Finite J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (mu : Measure J) [IsProbabilityMeasure mu]
    (v : J → K → ℝ) (m : ℕ) (i : Fin m) (k : K) :
    ∫ omega : Fin m → J, v (omega i) k
        ∂Measure.pi (fun _ : Fin m ↦ mu) =
      finiteProbabilityAverage mu v k := by
  have hmp := measurePreserving_eval (fun _ : Fin m ↦ mu) i
  calc
    (∫ omega : Fin m → J, v (omega i) k
        ∂Measure.pi (fun _ : Fin m ↦ mu)) =
        ∫ j, v j k ∂Measure.map (Function.eval i)
          (Measure.pi (fun _ : Fin m ↦ mu)) := by
      rw [integral_map]
      · exact (measurable_pi_apply i).aemeasurable
      · exact (measurable_of_finite
          (fun j : J ↦ v j k)).aestronglyMeasurable
    _ = finiteProbabilityAverage mu v k := by
      rw [hmp.map_eq]
      rfl

private theorem centered_coordinate_integral
    {J K : Type*} [Finite J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (mu : Measure J) [IsProbabilityMeasure mu]
    (v : J → K → ℝ) (m : ℕ) (y : ℝ) (i : Fin m) (k : K) :
    ∫ omega : Fin m → J,
        y * (finiteProbabilityAverage mu v k - v (omega i) k)
        ∂Measure.pi (fun _ : Fin m ↦ mu) = 0 := by
  rw [integral_const_mul]
  have hc : Integrable
      (fun _omega : Fin m → J ↦ finiteProbabilityAverage mu v k)
      (Measure.pi (fun _ : Fin m ↦ mu)) := Integrable.of_finite
  have hvint : Integrable (fun omega : Fin m → J ↦ v (omega i) k)
      (Measure.pi (fun _ : Fin m ↦ mu)) := Integrable.of_finite
  rw [integral_sub hc hvint, coordinate_integral mu v m i k]
  simp

private theorem centered_coordinate_subgaussian
    {J K : Type*} [Finite J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (mu : Measure J) [IsProbabilityMeasure mu]
    (v : J → K → ℝ) (hv : ∀ j k, |v j k| ≤ 1)
    (m : ℕ) (y : ℝ) (hy : |y| = 1) (i : Fin m) (k : K) :
    HasSubgaussianMGF
      (fun omega : Fin m → J ↦
        y * (finiteProbabilityAverage mu v k - v (omega i) k))
      4 (Measure.pi (fun _ : Fin m ↦ mu)) := by
  have hsg := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (X := fun omega : Fin m → J ↦
      y * (finiteProbabilityAverage mu v k - v (omega i) k))
    (a := (-2 : ℝ)) (b := (2 : ℝ))
    (measurable_of_finite _).aemeasurable (by
      filter_upwards [] with omega
      have hu := finiteProbabilityAverage_mem_Icc mu v hv k
      have habsu : |finiteProbabilityAverage mu v k| ≤ 1 := abs_le.mpr hu
      have hdiff :
          |finiteProbabilityAverage mu v k - v (omega i) k| ≤ 2 :=
        (abs_sub _ _).trans (by linarith [hv (omega i) k])
      have hprod :
          |y * (finiteProbabilityAverage mu v k - v (omega i) k)| ≤ 2 := by
        rw [abs_mul, hy, one_mul]
        exact hdiff
      exact abs_le.mp hprod)
    (centered_coordinate_integral mu v m y i k)
  norm_num at hsg
  exact hsg

private theorem one_coordinate_tail
    {J K : Type*} [Finite J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (mu : Measure J) [IsProbabilityMeasure mu]
    (v : J → K → ℝ) (hv : ∀ j k, |v j k| ≤ 1)
    (m : ℕ) (hm : 0 < m) (y : K → ℝ) (hy : ∀ k, |y k| = 1)
    (k : K) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (Measure.pi (fun _ : Fin m ↦ mu)).real
      {omega | (m : ℝ) * epsilon ≤
        ∑ i : Fin m, y k *
          (finiteProbabilityAverage mu v k - v (omega i) k)} ≤
      Real.exp (-((m : ℝ) * epsilon ^ 2) / 8) := by
  let productMeasure : Measure (Fin m → J) :=
    Measure.pi (fun _ : Fin m ↦ mu)
  let centered : Fin m → (Fin m → J) → ℝ :=
    fun i omega ↦ y k *
      (finiteProbabilityAverage mu v k - v (omega i) k)
  have hindep : iIndepFun centered productMeasure := by
    dsimp [centered, productMeasure]
    exact iIndepFun_pi (μ := fun _ : Fin m ↦ mu)
      (X := fun _i j ↦ y k * (finiteProbabilityAverage mu v k - v j k))
      (fun _ ↦ (measurable_of_finite _).aemeasurable)
  have hsub : ∀ i : Fin m,
      HasSubgaussianMGF (centered i) 4 productMeasure := by
    intro i
    exact centered_coordinate_subgaussian mu v hv m (y k) (hy k) i k
  have htail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    hindep (c := fun _ : Fin m ↦ 4) (s := Finset.univ)
      (fun i _ ↦ hsub i) (ε := (m : ℝ) * epsilon)
      (mul_nonneg (Nat.cast_nonneg _) hepsilon)
  change productMeasure.real
    {omega | (m : ℝ) * epsilon ≤ ∑ i : Fin m, centered i omega} ≤ _
  calc
    productMeasure.real
        {omega | (m : ℝ) * epsilon ≤ ∑ i : Fin m, centered i omega} ≤
      Real.exp (-((m : ℝ) * epsilon) ^ 2 /
        (2 * (∑ _i : Fin m, (4 : NNReal) : NNReal))) := htail
    _ = Real.exp (-((m : ℝ) * epsilon ^ 2) / 8) := by
      congr 1
      push_cast
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
      ring

/-- Simultaneous one-sided empirical approximation on a finite coordinate
set. The displayed exponential condition is exactly the union-bound budget. -/
theorem exists_empirical_oneSided_approximation
    {J K : Type*} [Finite J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (mu : Measure J) [IsProbabilityMeasure mu]
    [Fintype K] (v : J → K → ℝ) (hv : ∀ j k, |v j k| ≤ 1)
    (m : ℕ) (hm : 0 < m) (y : K → ℝ) (hy : ∀ k, |y k| = 1)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hbudget : (Fintype.card K : ℝ) *
      Real.exp (-((m : ℝ) * epsilon ^ 2) / 8) < 1) :
    ∃ sample : Fin m → J, ∀ k : K,
      (∑ i : Fin m, y k *
        (finiteProbabilityAverage mu v k - v (sample i) k)) <
      (m : ℝ) * epsilon := by
  let productMeasure : Measure (Fin m → J) :=
    Measure.pi (fun _ : Fin m ↦ mu)
  letI : IsProbabilityMeasure productMeasure := by
    dsimp [productMeasure]
    infer_instance
  let bad : K → Set (Fin m → J) := fun k ↦
    {sample | (m : ℝ) * epsilon ≤
      ∑ i : Fin m, y k *
        (finiteProbabilityAverage mu v k - v (sample i) k)}
  have hbad : productMeasure.real (⋃ k, bad k) ≤
      (Fintype.card K : ℝ) *
        Real.exp (-((m : ℝ) * epsilon ^ 2) / 8) := by
    calc
      productMeasure.real (⋃ k, bad k) ≤
          ∑ k : K, productMeasure.real (bad k) :=
        measureReal_iUnion_fintype_le bad
      _ ≤ ∑ _k : K, Real.exp (-((m : ℝ) * epsilon ^ 2) / 8) := by
        apply Finset.sum_le_sum
        intro k _
        exact one_coordinate_tail mu v hv m hm y hy k epsilon hepsilon
      _ = (Fintype.card K : ℝ) *
          Real.exp (-((m : ℝ) * epsilon ^ 2) / 8) := by simp
  by_contra hsample
  push Not at hsample
  have hall : (⋃ k, bad k) = Set.univ :=
    Set.eq_univ_of_forall fun sample ↦ by
      rw [Set.mem_iUnion]
      obtain ⟨k, hk⟩ := hsample sample
      exact ⟨k, hk⟩
  have hone : (1 : ℝ) ≤ (Fintype.card K : ℝ) *
      Real.exp (-((m : ℝ) * epsilon ^ 2) / 8) := by
    calc
      (1 : ℝ) = productMeasure.real Set.univ :=
        (probReal_univ (μ := productMeasure)).symm
      _ = productMeasure.real (⋃ k, bad k) := by rw [hall]
      _ ≤ _ := hbad
  linarith

end HeadComplexity
