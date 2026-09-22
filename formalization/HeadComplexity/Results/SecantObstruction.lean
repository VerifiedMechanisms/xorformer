import HeadComplexity.Polynomial.OrientedSecantSymmetry
import HeadComplexity.Atoms.FracComputableMonotone
import HeadComplexity.Atoms.OrientedAtomTangent
import HeadComplexity.Results.LowComplexity

set_option linter.style.header false

/-!
# Secant obstruction bridge

This file isolates the checked part of the advertised obstruction bridge.  A
strict cleared tangent pattern is normalized without changing any sign, then
placed on the exceptional divisor `t = 0` of the signed blow-up.
-/

namespace HeadComplexity

open Finset Set
open scoped BigOperators

namespace SignedSecant

open PositiveSecant

/-- An unnormalized strict tangent sign pattern in one orientation branch. -/
def OrientedTangentFeasible {n H : ℕ}
    (f : (Fin n → Bool) → Bool) (sigma : Fin H → Bool) : Prop :=
  ∃ (theta v : Fin H → Option (Fin n) → ℝ) (a : ℝ),
    IsSimplexPoint theta ∧ (∀ h, ∑ j, v h j = 0) ∧
      ∀ x : Fin n → Bool, 0 < truthSign f x *
        (productDirectionalDerivative (orientedLiteralFamily sigma) theta v x +
          a * (productScore (orientedLiteralFamily sigma) theta x +
            productScore (orientedLiteralFamily sigma) theta x))

/-- A strict fractional certificate has canonical oriented simplex
denominators and centered numerator directions. -/
theorem orientedTangentFeasible_of_fracComputable {n H : ℕ}
    (f : (Fin n → Bool) → Bool) (hf : fracComputable n H f) :
    ∃ sigma : Fin H → Bool, OrientedTangentFeasible f sigma := by
  classical
  obtain ⟨phi, c, hstrict⟩ := exists_strict_fracCertificate hf
  refine ⟨(fun h ↦ FracAtom.tangentOrientation (phi h)),
    (fun h ↦ FracAtom.tangentTheta (phi h)),
    (fun h ↦ FracAtom.tangentV (phi h)),
    (c + ∑ h, FracAtom.tangentQ (phi h)) / 2,
    FracAtom.tangentTheta_isSimplexPoint phi,
    (fun h ↦ FracAtom.tangentV_sum (phi h)), ?_⟩
  intro x
  have hproduct : 0 < productScore
      (orientedLiteralFamily
        (fun h ↦ FracAtom.tangentOrientation (phi h)))
      (fun h ↦ FracAtom.tangentTheta (phi h)) x :=
    FracAtom.tangentTheta_productScore_pos phi x
  have hscore :
      productDirectionalDerivative
          (orientedLiteralFamily
            (fun h ↦ FracAtom.tangentOrientation (phi h)))
          (fun h ↦ FracAtom.tangentTheta (phi h))
          (fun h ↦ FracAtom.tangentV (phi h)) x +
        (c + ∑ h, FracAtom.tangentQ (phi h)) / 2 *
          (productScore
              (orientedLiteralFamily
                (fun h ↦ FracAtom.tangentOrientation (phi h)))
              (fun h ↦ FracAtom.tangentTheta (phi h)) x +
            productScore
              (orientedLiteralFamily
                (fun h ↦ FracAtom.tangentOrientation (phi h)))
              (fun h ↦ FracAtom.tangentTheta (phi h)) x) =
        productScore
            (orientedLiteralFamily
              (fun h ↦ FracAtom.tangentOrientation (phi h)))
            (fun h ↦ FracAtom.tangentTheta (phi h)) x *
          (c + ∑ h, (phi h).eval x) := by
    rw [FracAtom.tangentV_productDirectionalDerivative]
    ring
  rw [hscore]
  have hs := hstrict x
  cases hfx : f x with
  | false =>
      simp only [hfx, Bool.false_eq_true, ↓reduceIte] at hs
      have hneg := mul_neg_of_pos_of_neg hproduct hs
      simp only [truthSign, hfx, Bool.false_eq_true, if_false, neg_mul]
      simpa only [one_mul] using (neg_pos.mpr hneg)
  | true =>
      simp only [hfx, ↓reduceIte] at hs
      simp only [truthSign, hfx, if_true, one_mul]
      exact mul_pos hproduct hs

theorem orientedTangentFeasible_of_computableWithHeadsN {n H : ℕ}
    (f : (Fin n → Bool) → Bool) (hf : computableWithHeadsN n H f) :
    ∃ sigma : Fin H → Bool, OrientedTangentFeasible f sigma :=
  orientedTangentFeasible_of_fracComputable f (fracComputable_of_computable hf)

theorem productDirectionalDerivative_smul
    {I J X : Type*} [Fintype I] [Fintype J]
    (L : I → J → X → ℝ) (theta v : I → J → ℝ)
    (r : ℝ) (x : X) :
    productDirectionalDerivative L theta (r • v) x =
      r * productDirectionalDerivative L theta v x := by
  classical
  unfold productDirectionalDerivative directionFactor
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

private theorem orientedTangent_direction_ne_zero {n H : ℕ}
    (f : (Fin n → Bool) → Bool) (sigma : Fin H → Bool)
    {theta v : Fin H → Option (Fin n) → ℝ} {a : ℝ}
    (hstrict : ∀ x : Fin n → Bool, 0 < truthSign f x *
      (productDirectionalDerivative (orientedLiteralFamily sigma) theta v x +
        a * (productScore (orientedLiteralFamily sigma) theta x +
          productScore (orientedLiteralFamily sigma) theta x))) :
    (v, a) ≠ 0 := by
  intro hzero
  have hv : v = 0 := congrArg Prod.fst hzero
  have ha : a = 0 := congrArg Prod.snd hzero
  have hpos := hstrict default
  simp [hv, ha, productDirectionalDerivative, directionFactor] at hpos

/-- Every strict unnormalized tangent pattern gives a normalized feasible point
on the signed exceptional divisor. -/
theorem signedBlowupFeasible_of_orientedTangent {n H : ℕ}
    (f : (Fin n → Bool) → Bool) (sigma : Fin H → Bool)
    (htangent : OrientedTangentFeasible f sigma) :
    SignedBlowupFeasible (orientedLiteralFamily sigma) (truthSign f)
      Finset.univ := by
  classical
  rcases htangent with ⟨theta, v, a, htheta, hvsum, hstrict⟩
  let r : ℝ := ‖(v, a)‖
  let v' : Fin H → Option (Fin n) → ℝ := r⁻¹ • v
  let a' : ℝ := r⁻¹ * a
  have hne : (v, a) ≠ 0 :=
    orientedTangent_direction_ne_zero f sigma hstrict
  have hr : 0 < r := norm_pos_iff.mpr hne
  have hvsum' : ∀ h, ∑ j, v' h j = 0 := by
    intro h
    change ∑ j, r⁻¹ * v h j = 0
    rw [← Finset.mul_sum, hvsum h, mul_zero]
  have hnorm : IsNormalizedSignedDirection v' a' := by
    change ‖(v', a')‖ = 1
    have hscaled : (v', a') = r⁻¹ • (v, a) := by
      ext <;> rfl
    rw [hscaled, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    change r⁻¹ * r = 1
    exact inv_mul_cancel₀ hr.ne'
  refine ⟨theta, v', a', 0, htheta, hvsum', hnorm,
    ⟨le_rfl, zero_le_one⟩, by simpa, ?_⟩
  intro x _hx
  rw [dividedSignedRayPolynomial_eval_zero,
    productDirectionalDerivative_smul]
  change 0 < truthSign f x *
    (2⁻¹ * (r⁻¹ * productDirectionalDerivative
      (orientedLiteralFamily sigma) theta v x +
      (r⁻¹ * a) * (productScore (orientedLiteralFamily sigma) theta x +
        productScore (orientedLiteralFamily sigma) theta x)))
  have hscale : 0 < 2⁻¹ * r⁻¹ := mul_pos (by norm_num) (inv_pos.mpr hr)
  have hmul := mul_pos hscale (hstrict x)
  have heq : truthSign f x *
      (2⁻¹ * (r⁻¹ * productDirectionalDerivative
        (orientedLiteralFamily sigma) theta v x +
        (r⁻¹ * a) * (productScore (orientedLiteralFamily sigma) theta x +
          productScore (orientedLiteralFamily sigma) theta x))) =
      (2⁻¹ * r⁻¹) * (truthSign f x *
        (productDirectionalDerivative (orientedLiteralFamily sigma) theta v x +
          a * (productScore (orientedLiteralFamily sigma) theta x +
            productScore (orientedLiteralFamily sigma) theta x))) := by ring
  rw [heq]
  exact hmul

private theorem orientedProductScore_nonneg {n H : ℕ}
    (sigma : Fin H → Bool) (theta : Fin H → Option (Fin n) → ℝ)
    (htheta : IsSimplexPoint theta) (x : Fin n → Bool) :
    0 ≤ productScore (orientedLiteralFamily sigma) theta x := by
  classical
  apply Finset.prod_nonneg
  intro h _
  unfold factor orientedLiteralFamily orientedLiteral
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (htheta.1 h j)
  cases j with
  | none => norm_num
  | some i =>
      cases hsigma : sigma h <;> cases hxi : x i <;>
        simp [boolToReal, hxi]

/-- A signed secant that strictly classifies a nonconstant Boolean function
also separates every positive-negative pair by the positive pair-gap system. -/
theorem positiveSecantFeasible_of_signedSecantFeasible {n H : ℕ}
    (f : (Fin n → Bool) → Bool) (sigma : Fin H → Bool)
    (hsigned : SignedSecantFeasible (orientedLiteralFamily sigma)
      (truthSign f) Finset.univ) :
    SecantFeasible (orientedLiteralFamily sigma)
      (positiveInputs f) (negativeInputs f) := by
  classical
  rcases hsigned with
    ⟨theta₀, theta₁, s, htheta₀, htheta₁, hs, hstrict⟩
  refine ⟨theta₀, theta₁, htheta₀, htheta₁, ?_⟩
  intro p hp q hq
  have hfp : f p = true := (mem_positiveInputs f p).mp hp
  have hfq : f q = false := (mem_negativeInputs f q).mp hq
  have hpstrict := hstrict p (Finset.mem_univ p)
  have hqstrict := hstrict q (Finset.mem_univ q)
  simp only [truthSign, hfp, if_true, one_mul] at hpstrict
  simp only [truthSign, hfq, Bool.false_eq_true, if_false, neg_mul,
    neg_pos] at hqstrict
  let A := productScore (orientedLiteralFamily sigma) theta₁ p
  let B := productScore (orientedLiteralFamily sigma) theta₀ p
  let C := productScore (orientedLiteralFamily sigma) theta₁ q
  let D := productScore (orientedLiteralFamily sigma) theta₀ q
  have hA0 : 0 ≤ A := orientedProductScore_nonneg sigma theta₁ htheta₁ p
  have hB0 : 0 ≤ B := orientedProductScore_nonneg sigma theta₀ htheta₀ p
  have hC0 : 0 ≤ C := orientedProductScore_nonneg sigma theta₁ htheta₁ q
  have hD0 : 0 ≤ D := orientedProductScore_nonneg sigma theta₀ htheta₀ q
  have hspos : 0 < s := by
    by_contra h
    have hsnonpos : s ≤ 0 := le_of_not_gt h
    dsimp [A, B] at hA0 hB0
    dsimp [secantScore] at hpstrict
    nlinarith
  have hsone : s < 1 := by
    by_contra h
    have hone : 1 ≤ s := le_of_not_gt h
    dsimp [C, D] at hC0 hD0
    dsimp [secantScore] at hqstrict
    nlinarith
  have hpos : (1 - s) * B < s * A := by
    dsimp [A, B, secantScore] at hpstrict ⊢
    linarith
  have hneg : s * C < (1 - s) * D := by
    dsimp [C, D, secantScore] at hqstrict ⊢
    linarith
  have hA : 0 < A := by
    have : 0 < s * A := lt_of_le_of_lt
      (mul_nonneg (sub_nonneg.mpr hs.2) hB0) hpos
    by_contra h
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hspos.le
      (le_of_not_gt h))) this
  have hleft : (1 - s) * (B * C) ≤ s * (A * C) := by
    have := mul_le_mul_of_nonneg_right hpos.le hC0
    nlinarith
  have hright : s * (A * C) < (1 - s) * (A * D) := by
    have := mul_lt_mul_of_pos_right hneg hA
    nlinarith
  have hpair : B * C < A * D := by
    exact lt_of_mul_lt_mul_left (hleft.trans_lt hright)
      (sub_pos.mpr hsone).le
  unfold pairGap
  dsimp [A, B, C, D] at hpair
  linarith

/-- Every exact `H`-head model of a nonconstant function supplies a feasible
branch of the theorem-193 positive blow-up system. -/
theorem positiveBlowupFeasible_of_computableWithHeadsN {n H : ℕ}
    (hH : 0 < H) (f : (Fin n → Bool) → Bool)
    (hf : ¬ ∀ x y, f x = f y) (hcomp : computableWithHeadsN n H f) :
    ∃ sigma : Fin H → Bool,
      BlowupFeasible (orientedLiteralFamily sigma)
        (positiveInputs f) (negativeInputs f) := by
  obtain ⟨sigma, htangent⟩ :=
    orientedTangentFeasible_of_computableWithHeadsN f hcomp
  have hsignedBlowup :=
    signedBlowupFeasible_of_orientedTangent f sigma htangent
  have hsignedSecant :=
    (orientedSignedSecantFeasible_iff_signedBlowupFeasible hH f sigma).2
      hsignedBlowup
  have hpositiveSecant :=
    positiveSecantFeasible_of_signedSecantFeasible f sigma hsignedSecant
  exact ⟨sigma,
    (orientedSecantFeasible_iff_blowupFeasible hH f hf sigma).1
      hpositiveSecant⟩

/-- **Theorem 193 head lower bound.** If every orientation branch of the
positive blow-up system is infeasible, then `H < HStar n f`. -/
theorem H_lt_HStar_of_no_positiveBlowup {n H : ℕ}
    (hH : 0 < H) (f : (Fin n → Bool) → Bool)
    (hf : ¬ ∀ x y, f x = f y)
    (hobs : ∀ sigma : Fin H → Bool,
      ¬ BlowupFeasible (orientedLiteralFamily sigma)
        (positiveInputs f) (negativeInputs f)) :
    H < HStar n f := by
  by_contra hnot
  have hle : HStar n f ≤ H := Nat.le_of_not_gt hnot
  obtain ⟨sigma, hfeasible⟩ := positiveBlowupFeasible_of_computableWithHeadsN
    hH f hf (computableWithHeadsN_mono hle (HStar_computable f))
  exact hobs sigma hfeasible

/-- Infeasibility of every orientation branch rules out every strict cleared
tangent pattern with `H` heads. -/
theorem no_orientedTangent_of_no_signedBlowup {n H : ℕ}
    (f : (Fin n → Bool) → Bool)
    (hobs : ∀ sigma : Fin H → Bool,
      ¬ SignedBlowupFeasible (orientedLiteralFamily sigma)
        (truthSign f) Finset.univ) :
    ∀ sigma : Fin H → Bool, ¬ OrientedTangentFeasible f sigma := by
  intro sigma htangent
  exact hobs sigma (signedBlowupFeasible_of_orientedTangent f sigma htangent)

/-- Once a model-to-oriented-tangent bridge is supplied, branch infeasibility
immediately rules out an exact `H`-head representation. -/
theorem not_computableWithHeadsN_of_no_signedBlowup_of_bridge
    {n H : ℕ} (f : (Fin n → Bool) → Bool)
    (toTangent : computableWithHeadsN n H f →
      ∃ sigma : Fin H → Bool, OrientedTangentFeasible f sigma)
    (hobs : ∀ sigma : Fin H → Bool,
      ¬ SignedBlowupFeasible (orientedLiteralFamily sigma)
        (truthSign f) Finset.univ) :
    ¬ computableWithHeadsN n H f := by
  intro hcomp
  obtain ⟨sigma, htangent⟩ := toTangent hcomp
  exact hobs sigma (signedBlowupFeasible_of_orientedTangent f sigma htangent)

/-- Infeasibility of all orientation branches is a checked lower-bound
certificate against an exact `H`-head model. -/
theorem not_computableWithHeadsN_of_no_signedBlowup
    {n H : ℕ} (f : (Fin n → Bool) → Bool)
    (hobs : ∀ sigma : Fin H → Bool,
      ¬ SignedBlowupFeasible (orientedLiteralFamily sigma)
        (truthSign f) Finset.univ) :
    ¬ computableWithHeadsN n H f :=
  not_computableWithHeadsN_of_no_signedBlowup_of_bridge f
    (orientedTangentFeasible_of_computableWithHeadsN f) hobs

/-- Infeasibility of every orientation branch at size `H` proves the strict
head-complexity lower bound `H < HStar`. -/
theorem H_lt_HStar_of_no_signedBlowup
    {n H : ℕ} (f : (Fin n → Bool) → Bool)
    (hobs : ∀ sigma : Fin H → Bool,
      ¬ SignedBlowupFeasible (orientedLiteralFamily sigma)
        (truthSign f) Finset.univ) :
    H < HStar n f := by
  by_contra hnot
  have hle : HStar n f ≤ H := Nat.le_of_not_gt hnot
  exact (not_computableWithHeadsN_of_no_signedBlowup f hobs)
    (computableWithHeadsN_mono hle (HStar_computable f))

/-- The same strict lower bound needs only the `H + 1` canonical
orientation-count branches. -/
theorem H_lt_HStar_of_no_signedBlowup_countBranches
    {n H : ℕ} (hH : 0 < H) (f : (Fin n → Bool) → Bool)
    (hobs : ∀ k : Fin (H + 1),
      ¬ SignedBlowupFeasible
        (orientedLiteralFamily (canonicalOrientation H k))
        (truthSign f) Finset.univ) :
    H < HStar n f := by
  apply H_lt_HStar_of_no_signedBlowup f
  exact (all_orientedSignedBlowup_infeasible_iff_all_countBranches hH f).2 hobs

/-- Fully finite theorem-194 obstruction: refuting every normalization chart
in each of the `H + 1` canonical orientation-count branches proves
`H < HStar`. -/
theorem H_lt_HStar_of_no_signedBlowup_countBranchCharts
    {n H : ℕ} (hH : 0 < H) (f : (Fin n → Bool) → Bool)
    (hobs : ∀ (k : Fin (H + 1))
      (c : SignedNormalizationChart (Fin H) (Option (Fin n))),
      ¬ SignedBlowupChartFeasible
        (orientedLiteralFamily (canonicalOrientation H k))
        (truthSign f) Finset.univ c) :
    H < HStar n f := by
  apply H_lt_HStar_of_no_signedBlowup f
  exact
    (all_orientedSignedBlowup_infeasible_iff_all_countBranchCharts hH f).2 hobs

/-- The symmetry-reduced theorem-194 obstruction.  It suffices to refute the
available members of a fixed `4 * (n + 1) + 2` chart-type family in each of
the `H + 1` canonical orientation-count branches. -/
theorem H_lt_HStar_of_no_signedBlowup_countBranchChartTypes
    {n H : ℕ} (hH : 0 < H) (f : (Fin n → Bool) → Bool)
    (hobs : ∀ (k : Fin (H + 1))
      (q : OrientedSignedNormalizationChartType n)
      (hq : q.IsAvailable (canonicalOrientation H k)),
      ¬ SignedBlowupChartFeasible
        (orientedLiteralFamily (canonicalOrientation H k))
        (truthSign f) Finset.univ
        (orientedSignedNormalizationChartRepresentative
          (canonicalOrientation H k) q hq)) :
    H < HStar n f := by
  apply H_lt_HStar_of_no_signedBlowup f
  exact
    (all_orientedSignedBlowup_infeasible_iff_all_countBranchChartTypes hH f).2
      hobs

/-- If the signed blow-up obstruction is checked at every size through `H`,
then the true head complexity is strictly larger than `H`. -/
theorem H_lt_HStar_of_no_signedBlowup_upto
    {n H : ℕ} (f : (Fin n → Bool) → Bool)
    (hobs : ∀ K, K ≤ H → ∀ sigma : Fin K → Bool,
      ¬ SignedBlowupFeasible (orientedLiteralFamily sigma)
        (truthSign f) Finset.univ) :
    H < HStar n f := by
  by_contra hnot
  have hle : HStar n f ≤ H := Nat.le_of_not_gt hnot
  exact (not_computableWithHeadsN_of_no_signedBlowup f
    (hobs (HStar n f) hle)) (HStar_computable f)

end SignedSecant

end HeadComplexity
