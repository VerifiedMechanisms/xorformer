import HeadComplexity.Results.AtomicMarginSparsification
import HeadComplexity.Results.FractionalNormalForm
import HeadComplexity.Atoms.ClearedNormalForm
import Mathlib.Probability.ProbabilityMassFunction.Integrals

set_option linter.style.header false

/-!
# The literal output-normalized atomic condition number

This file adds the infimum wrapper from theorem 195.  A finite certificate is
presented with explicit convex weights, converted to the measure-based
`AtomicMarginCertificate`, and then minimized over all finite certificates.
-/

namespace HeadComplexity

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

variable {n : ℕ} {f : (Fin n → Bool) → Bool}

/-- A finite convex combination of normalized genuine fractional atoms with a
strict output-space margin. -/
structure FiniteAtomicMarginCertificate
    (f : (Fin n → Bool) → Bool) where
  termCount : ℕ
  termCount_pos : 0 < termCount
  atom : Fin termCount → FracAtom n
  weight : Fin termCount → ℝ
  weight_nonneg : ∀ j, 0 ≤ weight j
  weight_sum_one : ∑ j, weight j = 1
  normalized : ∀ j bits, |(atom j).eval bits| ≤ 1
  bias : ℝ
  scale : ℝ
  margin : ℝ
  scale_pos : 0 < scale
  margin_pos : 0 < margin
  separates : ∀ bits,
    margin ≤ signedLabel f bits *
      (bias + scale * ∑ j, weight j * (atom j).eval bits)

namespace FiniteAtomicMarginCertificate

/-- The probability mass function carried by the explicit convex weights. -/
noncomputable def pmf (C : FiniteAtomicMarginCertificate f) :
    PMF (Fin C.termCount) :=
  PMF.ofFintype (fun j ↦ ENNReal.ofReal (C.weight j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [C.weight_sum_one]
      norm_num
    · intro j _
      exact C.weight_nonneg j)

@[simp] theorem pmf_apply_toReal
    (C : FiniteAtomicMarginCertificate f) (j : Fin C.termCount) :
    (C.pmf j).toReal = C.weight j := by
  rw [pmf, PMF.ofFintype_apply, ENNReal.toReal_ofReal]
  exact C.weight_nonneg j

/-- Convert explicit finite convex weights to the measure-based certificate
used by the sampling theorem. -/
noncomputable def toAtomicMarginCertificate
    (C : FiniteAtomicMarginCertificate f) :
    AtomicMarginCertificate f (Fin C.termCount) C.pmf.toMeasure where
  atom := C.atom
  normalized := C.normalized
  bias := C.bias
  scale := C.scale
  margin := C.margin
  scale_pos := C.scale_pos
  margin_pos := C.margin_pos
  separates := by
    intro bits
    have havg : atomicAverage C.pmf.toMeasure C.atom bits =
        ∑ j, C.weight j * (C.atom j).eval bits := by
      unfold atomicAverage
      rw [PMF.integral_eq_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp [C.pmf_apply_toReal, smul_eq_mul]
    rw [havg]
    exact C.separates bits

/-- The explicit finite certificate inherits the theorem-195 sparsification
bound. -/
theorem HStar_real_le_atomicCondition
    (C : FiniteAtomicMarginCertificate f) :
    (HStar n f : ℝ) ≤
      33 * (n + 1 : ℝ) * (C.scale / C.margin) ^ 2 :=
  C.toAtomicMarginCertificate.HStar_real_le_atomicCondition

/-- Every finite certificate for a nonconstant function has condition ratio
at least one. -/
theorem one_le_scale_div_margin
    (C : FiniteAtomicMarginCertificate f)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    1 ≤ C.scale / C.margin :=
  C.toAtomicMarginCertificate.one_le_scale_div_margin hnonconstant

/-- Every nonconstant Boolean function admits a finite normalized atomic
margin certificate.  A common output bound normalizes an exact minimum-head
fractional representation, and uniform convex weights recover its score. -/
theorem exists_of_nonconstant
    (f : (Fin n → Bool) → Bool)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    Nonempty (FiniteAtomicMarginCertificate f) := by
  classical
  let H := HStar n f
  have hH : 0 < H := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hnonconstant ((HStar_eq_zero_iff f).mp hzero)
  obtain ⟨phi, c, hstrict⟩ := exists_strict_fracCertificate
    (fracComputable_of_computable (HStar_computable f))
  let M : ℝ := 1 + ∑ h : Fin H, ∑ bits : Fin n → Bool, |(phi h).eval bits|
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hbound (h : Fin H) (bits : Fin n → Bool) :
      |(phi h).eval bits| ≤ M := by
    have hinner : |(phi h).eval bits| ≤
        ∑ y : Fin n → Bool, |(phi h).eval y| := by
      exact Finset.single_le_sum
        (fun y _ ↦ abs_nonneg ((phi h).eval y)) (Finset.mem_univ bits)
    have houter : (∑ y : Fin n → Bool, |(phi h).eval y|) ≤
        ∑ g : Fin H, ∑ y : Fin n → Bool, |(phi g).eval y| := by
      exact Finset.single_le_sum
        (fun g _ ↦ Finset.sum_nonneg fun y _ ↦ abs_nonneg ((phi g).eval y))
        (Finset.mem_univ h)
    dsimp [M]
    linarith
  let normalizedAtom : Fin H → FracAtom n :=
    fun h ↦ (phi h).scale M⁻¹
  have hnormalized : ∀ h bits, |(normalizedAtom h).eval bits| ≤ 1 := by
    intro h bits
    rw [FracAtom.scale_eval, abs_mul, abs_inv, abs_of_pos hMpos]
    calc
      M⁻¹ * |(phi h).eval bits| ≤ M⁻¹ * M :=
        mul_le_mul_of_nonneg_left (hbound h bits) (inv_pos.mpr hMpos).le
      _ = 1 := inv_mul_cancel₀ hMpos.ne'
  let uniformWeight : Fin H → ℝ := fun _ ↦ (H : ℝ)⁻¹
  have hweightNonneg : ∀ h, 0 ≤ uniformWeight h := by
    intro h
    exact (inv_pos.mpr (by exact_mod_cast hH)).le
  have hweightSum : ∑ h, uniformWeight h = 1 := by
    dsimp [uniformWeight]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast hH.ne')
  let score : (Fin n → Bool) → ℝ :=
    fun bits ↦ signedLabel f bits * (c + ∑ h, (phi h).eval bits)
  have hscorePos (bits : Fin n → Bool) : 0 < score bits := by
    change 0 < signedLabel f bits * (c + ∑ h, (phi h).eval bits)
    cases hfb : f bits with
    | false =>
        rw [signedLabel_of_false hfb]
        have hs := hstrict bits
        simp only [hfb, Bool.false_eq_true, if_false] at hs
        linarith
    | true =>
        rw [signedLabel_of_true hfb, one_mul]
        have hs := hstrict bits
        simpa [hfb] using hs
  let margin : ℝ :=
    (Finset.univ : Finset (Fin n → Bool)).inf'
      Finset.univ_nonempty score
  have hmarginPos : 0 < margin := by
    dsimp [margin]
    rw [Finset.lt_inf'_iff]
    intro bits _
    exact hscorePos bits
  refine Nonempty.intro
    { termCount := H
      termCount_pos := hH
      atom := normalizedAtom
      weight := uniformWeight
      weight_nonneg := hweightNonneg
      weight_sum_one := hweightSum
      normalized := hnormalized
      bias := c
      scale := (H : ℝ) * M
      margin := margin
      scale_pos := mul_pos (by exact_mod_cast hH) hMpos
      margin_pos := hmarginPos
      separates := ?_ }
  intro bits
  have hrecover : ((H : ℝ) * M) *
      (∑ h : Fin H, uniformWeight h * (normalizedAtom h).eval bits) =
      ∑ h : Fin H, (phi h).eval bits := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    dsimp [uniformWeight, normalizedAtom]
    rw [FracAtom.scale_eval]
    field_simp [show (H : ℝ) ≠ 0 by exact_mod_cast hH.ne', hMpos.ne']
  rw [hrecover]
  exact Finset.inf'_le _ (Finset.mem_univ bits)

end FiniteAtomicMarginCertificate

/-- All condition ratios realized by finite convex combinations of normalized
genuine one-head output vectors. -/
def atomicConditionRatios (f : (Fin n → Bool) → Bool) : Set ℝ :=
  {r | ∃ C : FiniteAtomicMarginCertificate f,
    r = C.scale / C.margin}

/-- The output-normalized atomic condition number from theorem 195. -/
noncomputable def atomicConditionNumber
    (f : (Fin n → Bool) → Bool) : ℝ :=
  sInf (atomicConditionRatios f)

theorem atomicConditionRatios_nonempty
    (f : (Fin n → Bool) → Bool)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    (atomicConditionRatios f).Nonempty := by
  obtain ⟨C⟩ := FiniteAtomicMarginCertificate.exists_of_nonconstant
    f hnonconstant
  exact ⟨C.scale / C.margin, C, rfl⟩

/-- The condition number of a nonconstant Boolean function is at least one. -/
theorem one_le_atomicConditionNumber
    (f : (Fin n → Bool) → Bool)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    1 ≤ atomicConditionNumber f := by
  unfold atomicConditionNumber
  apply le_csInf (atomicConditionRatios_nonempty f hnonconstant)
  intro r hr
  rcases hr with ⟨C, rfl⟩
  exact C.one_le_scale_div_margin hnonconstant

/-- **Theorem 195, literal infimum form.** The minimum head count is bounded
quadratically by the output-normalized atomic condition number. -/
theorem HStar_real_le_atomicConditionNumber
    (f : (Fin n → Bool) → Bool)
    (hnonconstant : ¬ ∀ x y, f x = f y) :
    (HStar n f : ℝ) ≤
      33 * (n + 1 : ℝ) * (atomicConditionNumber f) ^ 2 := by
  let K : ℝ := 33 * (n + 1 : ℝ)
  let q : ℝ := (HStar n f : ℝ) / K
  let a : ℝ := Real.sqrt q
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  have hqnonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have haNonneg : 0 ≤ a := Real.sqrt_nonneg q
  have hratios := atomicConditionRatios_nonempty f hnonconstant
  have halower : ∀ r ∈ atomicConditionRatios f, a ≤ r := by
    intro r hr
    rcases hr with ⟨C, rfl⟩
    apply Real.sqrt_le_iff.mpr
    refine ⟨(div_pos C.scale_pos C.margin_pos).le, ?_⟩
    apply (div_le_iff₀ hKpos).2
    have hC := C.HStar_real_le_atomicCondition
    dsimp [K, q] at hC ⊢
    nlinarith
  have hainf : a ≤ atomicConditionNumber f := by
    exact le_csInf hratios halower
  have hinfNonneg : 0 ≤ atomicConditionNumber f := haNonneg.trans hainf
  have hsquare : a ^ 2 ≤ (atomicConditionNumber f) ^ 2 :=
    (sq_le_sq₀ haNonneg hinfNonneg).2 hainf
  have haSquare : a ^ 2 = q := by
    dsimp [a]
    exact Real.sq_sqrt hqnonneg
  have hqle : q ≤ (atomicConditionNumber f) ^ 2 := by
    rwa [← haSquare]
  have hmul := (div_le_iff₀ hKpos).mp hqle
  dsimp [q, K] at hmul ⊢
  nlinarith

end HeadComplexity
