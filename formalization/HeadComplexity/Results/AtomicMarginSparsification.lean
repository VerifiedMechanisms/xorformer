import HeadComplexity.Atoms.AtomicSampling
import HeadComplexity.Results.LowComplexity

set_option linter.style.header false

/-!
# Output-normalized atomic-margin sparsification

A finite convex combination of genuine fractional-atom output vectors, each
normalized in sup norm on the Boolean cube, can be sampled down to an exact
head representation.  The quantitative bound is explicit.
-/

namespace HeadComplexity

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The explicit empirical sample count used by atomic-margin sparsification. -/
noncomputable def atomicSampleCount (n : ℕ) (scale margin : ℝ) : ℕ :=
  ⌈32 * (n + 1 : ℝ) * (scale / margin) ^ 2⌉₊

private theorem atomicSampleCount_pos (n : ℕ) {scale margin : ℝ}
    (hscale : 0 < scale) (hmargin : 0 < margin) :
    0 < atomicSampleCount n scale margin := by
  apply Nat.ceil_pos.mpr
  positivity

private theorem atomicSampleCount_exp_budget (n : ℕ) {scale margin : ℝ}
    (hscale : 0 < scale) (hmargin : 0 < margin) :
    (Fintype.card (Fin n → Bool) : ℝ) *
      Real.exp (-((atomicSampleCount n scale margin : ℝ) *
        (margin / (2 * scale)) ^ 2) / 8) < 1 := by
  let X : ℝ := 32 * (n + 1 : ℝ) * (scale / margin) ^ 2
  let m : ℕ := atomicSampleCount n scale margin
  let epsilon : ℝ := margin / (2 * scale)
  have hX : 0 < X := by
    dsimp [X]
    positivity
  have hm : X ≤ (m : ℝ) := by
    dsimp [m, atomicSampleCount]
    exact Nat.le_ceil X
  have hexponent : (n + 1 : ℝ) ≤ (m : ℝ) * epsilon ^ 2 / 8 := by
    calc
      (n + 1 : ℝ) = X * epsilon ^ 2 / 8 := by
        dsimp [X, epsilon]
        field_simp [hscale.ne', hmargin.ne']
        ring
      _ ≤ (m : ℝ) * epsilon ^ 2 / 8 := by
        gcongr
  have hbase : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    norm_num at h ⊢
    exact h.le
  have hpow : (2 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
    calc
      (2 : ℝ) ^ n ≤ (Real.exp 1) ^ n := by gcongr
      _ = Real.exp (n : ℝ) := by
        rw [← Real.exp_nat_mul]
        simp
  rw [show (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n by simp]
  change (2 : ℝ) ^ n *
    Real.exp (-((m : ℝ) * epsilon ^ 2) / 8) < 1
  calc
    (2 : ℝ) ^ n * Real.exp (-((m : ℝ) * epsilon ^ 2) / 8) ≤
        (2 : ℝ) ^ n * Real.exp (-(n + 1 : ℝ)) := by
      gcongr
      nlinarith [hexponent]
    _ ≤ Real.exp (n : ℝ) * Real.exp (-(n + 1 : ℝ)) := by gcongr
    _ = Real.exp (-1) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ < 1 := Real.exp_lt_one_iff.mpr (by norm_num)

namespace AtomicMarginCertificate

variable {J : Type*} [Fintype J] [MeasurableSpace J]
  [MeasurableSingletonClass J] {mu : Measure J} [IsProbabilityMeasure mu]
  {f : (Fin n → Bool) → Bool}

/-- A normalized atomic-margin certificate can be sampled to the explicit
number of heads `atomicSampleCount`. -/
theorem computableWithHeadsN_atomicSampleCount
    (C : AtomicMarginCertificate f J mu) :
    computableWithHeadsN n (atomicSampleCount n C.scale C.margin) f := by
  let m : ℕ := atomicSampleCount n C.scale C.margin
  let epsilon : ℝ := C.margin / (2 * C.scale)
  let value : J → (Fin n → Bool) → ℝ :=
    fun j bits ↦ (C.atom j).eval bits
  have hm : 0 < m := atomicSampleCount_pos n C.scale_pos C.margin_pos
  obtain ⟨sample, hsample⟩ := exists_empirical_oneSided_approximation
    mu value C.normalized m hm (signedLabel f) (abs_signedLabel f)
      epsilon (by
        dsimp [epsilon]
        exact (div_pos C.margin_pos (mul_pos (by norm_num) C.scale_pos)).le)
      (by
        dsimp [m, epsilon]
        exact atomicSampleCount_exp_budget n C.scale_pos C.margin_pos)
  apply C.computableWithHeadsN_of_empirical_margin sample
  intro bits
  let y : ℝ := signedLabel f bits
  let u : ℝ := atomicAverage mu C.atom bits
  let loss : ℝ := ∑ i : Fin m, y * (u - (C.atom (sample i)).eval bits)
  have hu : u = finiteProbabilityAverage mu value bits := rfl
  have hloss : loss < (m : ℝ) * epsilon := by
    dsimp [loss, y]
    rw [hu]
    dsimp [value]
    exact hsample bits
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hcoeff : 0 < C.scale / (m : ℝ) := div_pos C.scale_pos hmreal
  have hloss_eq : loss =
      (m : ℝ) * y * u - y * ∑ i : Fin m, (C.atom (sample i)).eval bits := by
    dsimp [loss]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    simp [Finset.mul_sum]
    ring
  have herror : (C.scale / (m : ℝ)) * loss < C.margin / 2 := by
    calc
      (C.scale / (m : ℝ)) * loss <
          (C.scale / (m : ℝ)) * ((m : ℝ) * epsilon) :=
        mul_lt_mul_of_pos_left hloss hcoeff
      _ = C.margin / 2 := by
        dsimp [epsilon]
        field_simp [C.scale_pos.ne', ne_of_gt hmreal]
  have hscore :
      y * (C.bias + (C.scale / (m : ℝ)) *
        ∑ i : Fin m, (C.atom (sample i)).eval bits) =
      y * (C.bias + C.scale * u) -
        (C.scale / (m : ℝ)) * loss := by
    rw [hloss_eq]
    field_simp [ne_of_gt hmreal]
    ring
  have hsep := C.separates bits
  dsimp [y, u] at hscore ⊢
  rw [hscore]
  linarith [C.margin_pos]

/-- The natural-valued sparsification bound, including the unavoidable
rounding of the explicit real sample count. -/
theorem HStar_le_atomicSampleCount
    (C : AtomicMarginCertificate f J mu) :
    HStar n f ≤ atomicSampleCount n C.scale C.margin :=
  HStar_le_of_computableWithHeadsN C.computableWithHeadsN_atomicSampleCount

private theorem scale_div_margin_of_true_false
    (C : AtomicMarginCertificate f J mu)
    {x y : Fin n → Bool} (hx : f x = true) (hy : f y = false) :
    1 ≤ C.scale / C.margin := by
  let value : J → (Fin n → Bool) → ℝ :=
    fun j bits ↦ (C.atom j).eval bits
  let ux : ℝ := atomicAverage mu C.atom x
  let uy : ℝ := atomicAverage mu C.atom y
  have hux : ux ∈ Set.Icc (-1 : ℝ) 1 := by
    change finiteProbabilityAverage mu value x ∈ Set.Icc (-1 : ℝ) 1
    exact finiteProbabilityAverage_mem_Icc mu value C.normalized x
  have huy : uy ∈ Set.Icc (-1 : ℝ) 1 := by
    change finiteProbabilityAverage mu value y ∈ Set.Icc (-1 : ℝ) 1
    exact finiteProbabilityAverage_mem_Icc mu value C.normalized y
  have hsepx := C.separates x
  have hsepy := C.separates y
  rw [signedLabel_of_true hx, one_mul] at hsepx
  rw [signedLabel_of_false hy] at hsepy
  have hgap : 2 * C.margin ≤ C.scale * (ux - uy) := by
    dsimp [ux, uy] at hsepx hsepy ⊢
    linarith
  have hdiff : ux - uy ≤ 2 := by
    exact sub_le_iff_le_add.mpr (by linarith [hux.2, huy.1])
  have hmul : C.scale * (ux - uy) ≤ C.scale * 2 :=
    mul_le_mul_of_nonneg_left hdiff C.scale_pos.le
  apply (le_div_iff₀ C.margin_pos).mpr
  nlinarith

/-- A nonconstant atomic-margin certificate necessarily has condition ratio
at least one. -/
theorem one_le_scale_div_margin
    (C : AtomicMarginCertificate f J mu)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    1 ≤ C.scale / C.margin := by
  push Not at hnonconstant
  obtain ⟨x, y, hxy⟩ := hnonconstant
  cases hx : f x <;> cases hy : f y
  · exact (hxy (by rw [hx, hy])).elim
  · exact scale_div_margin_of_true_false C hy hx
  · exact scale_div_margin_of_true_false C hx hy
  · exact (hxy (by rw [hx, hy])).elim

/-- Theorem 195 with an explicit absolute constant. The conclusion is stated
in the reals so the ceiling in the natural sample count can be absorbed into
the constant. -/
theorem HStar_real_le_atomicCondition
    (C : AtomicMarginCertificate f J mu) :
    (HStar n f : ℝ) ≤
      33 * (n + 1 : ℝ) * (C.scale / C.margin) ^ 2 := by
  by_cases hnonconstant : ¬ ∀ x y, f x = f y
  · let ratio : ℝ := C.scale / C.margin
    let A : ℝ := (n + 1 : ℝ) * ratio ^ 2
    have hratio : 1 ≤ ratio := by
      dsimp [ratio]
      exact C.one_le_scale_div_margin hnonconstant
    have hratioSq : 1 ≤ ratio ^ 2 := by nlinarith
    have hn1 : (1 : ℝ) ≤ (n + 1 : ℝ) := by norm_num
    have hA : 1 ≤ A := by
      dsimp [A]
      nlinarith [mul_le_mul hn1 hratioSq (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : (0 : ℝ) ≤ (n + 1 : ℝ))]
    have hnat := C.HStar_le_atomicSampleCount
    have hcast : (HStar n f : ℝ) ≤
        (atomicSampleCount n C.scale C.margin : ℝ) := by
      exact_mod_cast hnat
    have hceil : (atomicSampleCount n C.scale C.margin : ℝ) < 32 * A + 1 := by
      change (↑⌈(32 : ℝ) * (n + 1 : ℝ) *
        (C.scale / C.margin) ^ 2⌉₊ : ℝ) < 32 * A + 1
      calc
        (↑⌈(32 : ℝ) * (n + 1 : ℝ) *
            (C.scale / C.margin) ^ 2⌉₊ : ℝ) <
            32 * (n + 1 : ℝ) * (C.scale / C.margin) ^ 2 + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        _ = 32 * A + 1 := by dsimp [A, ratio]; ring
    rw [show 33 * (n + 1 : ℝ) * (C.scale / C.margin) ^ 2 = 33 * A by
      dsimp [A, ratio]
      ring]
    linarith
  · push Not at hnonconstant
    rw [(HStar_eq_zero_iff f).mpr hnonconstant]
    norm_num only [Nat.cast_zero]
    change (0 : ℝ) ≤ 33 * (n + 1 : ℝ) * (C.scale / C.margin) ^ 2
    exact mul_nonneg
      (mul_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le (n + 1)))
      (sq_nonneg _)

/-- A certificate-level upper bound on the output-normalized atomic condition
ratio. This avoids baking a potentially unattained real infimum into the core
formalization. -/
def AtomicConditionLE
    (C : AtomicMarginCertificate f J mu) (kappa : ℝ) : Prop :=
  C.scale / C.margin ≤ kappa

/-- Any certified upper bound on the atomic condition ratio gives the same
quadratic head bound. This is the directly usable, infimum-free condition
number corollary of Theorem 195. -/
theorem HStar_real_le_of_atomicConditionLE
    (C : AtomicMarginCertificate f J mu) {kappa : ℝ}
    (hcondition : AtomicConditionLE C kappa) :
    (HStar n f : ℝ) ≤ 33 * (n + 1 : ℝ) * kappa ^ 2 := by
  have hratioNonneg : 0 ≤ C.scale / C.margin :=
    (div_pos C.scale_pos C.margin_pos).le
  have hsq : (C.scale / C.margin) ^ 2 ≤ kappa ^ 2 :=
    (sq_le_sq₀ hratioNonneg (hratioNonneg.trans hcondition)).mpr hcondition
  exact C.HStar_real_le_atomicCondition |>.trans
    (mul_le_mul_of_nonneg_left hsq (by positivity))

end AtomicMarginCertificate

end HeadComplexity
