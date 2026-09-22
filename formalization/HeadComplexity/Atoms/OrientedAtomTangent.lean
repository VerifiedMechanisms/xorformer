import HeadComplexity.Atoms.ClearedNormalForm
import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Polynomial.SignedSecantBlowup

set_option linter.style.header false

/-!
# Oriented tangent coordinates for fractional atoms

The denominator of a fractional atom has one common coefficient orientation.
This file rewrites it as a positive scale times a simplex combination of the
constant literal and either all positive or all negative coordinate literals.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

namespace FracAtom

open PositiveSecant
open SignedSecant

variable {n : ℕ}

/-- Coefficients of an affine function in either the positive literal basis
`(1,x_i)` or the negative literal basis `(1,1-x_i)`. -/
noncomputable def orientedAffineWeights (sigma : Bool) (c : ℝ)
    (cs : Fin n → ℝ) : Option (Fin n) → ℝ :=
  if sigma then
    fun j ↦ match j with
      | none => c
      | some i => cs i
  else
    fun j ↦ match j with
      | none => c + ∑ i, cs i
      | some i => -cs i

theorem orientedAffineWeights_eval (sigma : Bool) (c : ℝ)
    (cs : Fin n → ℝ) (x : Fin n → Bool) :
    ∑ j, orientedAffineWeights sigma c cs j * orientedLiteral sigma j x =
      affineValue c cs x := by
  classical
  cases sigma with
  | false =>
      simp only [orientedAffineWeights, Bool.false_eq_true, if_false,
        orientedLiteral, affineValue]
      simp only [univ_option, Finset.sum_insertNone]
      simp_rw [neg_mul, mul_sub, mul_one, neg_sub]
      rw [Finset.sum_sub_distrib]
      ring
  | true =>
      simp [orientedAffineWeights, orientedLiteral, affineValue]

/-- Constant coefficient of the atom denominator in the raw-bit basis. -/
noncomputable def tangentDenConst (phi : FracAtom n) : ℝ :=
  phi.γ + ∑ i, phi.ρ i

/-- Variable coefficients of the atom denominator in the raw-bit basis. -/
noncomputable def tangentDenCoeff (phi : FracAtom n) (i : Fin n) : ℝ :=
  phi.ρ i * (phi.α - 1)

/-- Positive literal orientation when `alpha ≥ 1`, negative otherwise. -/
noncomputable def tangentOrientation (phi : FracAtom n) : Bool :=
  if 1 ≤ phi.α then true else false

/-- Positive scale removed from an atom denominator. -/
noncomputable def tangentDenScale (phi : FracAtom n) : ℝ :=
  if 1 ≤ phi.α then phi.γ + phi.α * ∑ i, phi.ρ i
  else phi.γ + ∑ i, phi.ρ i

/-- Barycentric coordinates of the normalized atom denominator. -/
noncomputable def tangentTheta (phi : FracAtom n) : Option (Fin n) → ℝ :=
  if _ha : 1 ≤ phi.α then
    fun j ↦ match j with
      | none => (phi.γ + ∑ i, phi.ρ i) / tangentDenScale phi
      | some i => phi.ρ i * (phi.α - 1) / tangentDenScale phi
  else
    fun j ↦ match j with
      | none => (phi.γ + phi.α * ∑ i, phi.ρ i) / tangentDenScale phi
      | some i => phi.ρ i * (1 - phi.α) / tangentDenScale phi

theorem tangentDenScale_pos (phi : FracAtom n) : 0 < tangentDenScale phi := by
  classical
  by_cases ha : 1 ≤ phi.α
  · rw [tangentDenScale, if_pos ha]
    have hsum : 0 ≤ ∑ i, phi.ρ i :=
      Finset.sum_nonneg fun i _ ↦ (phi.hρ i).le
    exact add_pos_of_pos_of_nonneg phi.hγ
      (mul_nonneg (zero_le_one.trans ha) hsum)
  · rw [tangentDenScale, if_neg ha]
    exact add_pos_of_pos_of_nonneg phi.hγ
      (Finset.sum_nonneg fun i _ ↦ (phi.hρ i).le)

theorem tangentTheta_nonneg (phi : FracAtom n) (j : Option (Fin n)) :
    0 ≤ tangentTheta phi j := by
  classical
  by_cases ha : 1 ≤ phi.α
  · rw [tangentTheta, dif_pos ha]
    cases j with
    | none =>
        exact div_nonneg
          (add_nonneg phi.hγ.le
            (Finset.sum_nonneg fun i _ ↦ (phi.hρ i).le))
          (tangentDenScale_pos phi).le
    | some i =>
        exact div_nonneg (mul_nonneg (phi.hρ i).le (sub_nonneg.mpr ha))
          (tangentDenScale_pos phi).le
  · rw [tangentTheta, dif_neg ha]
    have halt : phi.α < 1 := lt_of_not_ge ha
    cases j with
    | none =>
        exact div_nonneg
          (add_nonneg phi.hγ.le
            (mul_nonneg phi.hα.le
              (Finset.sum_nonneg fun i _ ↦ (phi.hρ i).le)))
          (tangentDenScale_pos phi).le
    | some i =>
        exact div_nonneg (mul_nonneg (phi.hρ i).le (sub_nonneg.mpr halt.le))
          (tangentDenScale_pos phi).le

theorem tangentTheta_sum (phi : FracAtom n) :
    ∑ j, tangentTheta phi j = 1 := by
  classical
  by_cases ha : 1 ≤ phi.α
  · rw [show (∑ j, tangentTheta phi j) =
        (phi.γ + ∑ i, phi.ρ i) / tangentDenScale phi +
          ∑ i, phi.ρ i * (phi.α - 1) / tangentDenScale phi by
      simp [tangentTheta, ha]]
    rw [← Finset.sum_div]
    rw [← add_div]
    have hs := (tangentDenScale_pos phi).ne'
    rw [div_eq_one_iff_eq hs]
    rw [tangentDenScale, if_pos ha]
    rw [← Finset.sum_mul]
    ring
  · rw [show (∑ j, tangentTheta phi j) =
        (phi.γ + phi.α * ∑ i, phi.ρ i) / tangentDenScale phi +
          ∑ i, phi.ρ i * (1 - phi.α) / tangentDenScale phi by
      simp [tangentTheta, ha]]
    rw [← Finset.sum_div]
    rw [← add_div]
    have hs := (tangentDenScale_pos phi).ne'
    rw [div_eq_one_iff_eq hs]
    rw [tangentDenScale, if_neg ha]
    rw [← Finset.sum_mul]
    ring

theorem tangentTheta_isSimplexPoint {H : ℕ} (phi : Fin H → FracAtom n) :
    IsSimplexPoint (fun h ↦ tangentTheta (phi h)) :=
  ⟨fun h j ↦ tangentTheta_nonneg (phi h) j,
    fun h ↦ tangentTheta_sum (phi h)⟩

theorem tangentTheta_eq_orientedAffineWeights_div (phi : FracAtom n) :
    tangentTheta phi = fun j ↦
      orientedAffineWeights (tangentOrientation phi) (tangentDenConst phi)
        (tangentDenCoeff phi) j / tangentDenScale phi := by
  classical
  funext j
  by_cases ha : 1 ≤ phi.α
  · rw [tangentTheta, dif_pos ha]
    simp only [tangentOrientation, if_pos ha, orientedAffineWeights,
      if_true]
    cases j <;> rfl
  · rw [tangentTheta, dif_neg ha]
    simp only [tangentOrientation, if_neg ha, orientedAffineWeights,
      Bool.false_eq_true, if_false]
    cases j with
    | none =>
        dsimp [tangentDenConst, tangentDenCoeff]
        rw [← Finset.sum_mul]
        congr 1
        ring
    | some i =>
        dsimp [tangentDenCoeff]
        congr 1
        ring

theorem tangentDen_affineValue (phi : FracAtom n) (x : Fin n → Bool) :
    affineValue (tangentDenConst phi) (tangentDenCoeff phi) x =
      phi.γ + ∑ i, phi.wt x i := by
  classical
  unfold affineValue tangentDenConst tangentDenCoeff
  have hwt : (∑ i, phi.wt x i) =
      ∑ i, (phi.ρ i + phi.ρ i * (phi.α - 1) * boolToReal (x i)) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold wt
    cases hxi : x i with
    | false => simp [boolToReal]
    | true =>
        simp [boolToReal]
        ring
  rw [hwt]
  rw [Finset.sum_add_distrib]
  ring

/-- The atom denominator is its positive scale times the oriented simplex
factor. -/
theorem tangentTheta_factor (phi : FracAtom n) (x : Fin n → Bool) :
    ∑ j, tangentTheta phi j * orientedLiteral (tangentOrientation phi) j x =
      (phi.γ + ∑ i, phi.wt x i) / tangentDenScale phi := by
  classical
  rw [tangentTheta_eq_orientedAffineWeights_div]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [orientedAffineWeights_eval, tangentDen_affineValue]

theorem tangentTheta_family_factor {H : ℕ} (phi : Fin H → FracAtom n)
    (h : Fin H) (x : Fin n → Bool) :
    factor (orientedLiteralFamily (fun g ↦ tangentOrientation (phi g)))
      (fun g ↦ tangentTheta (phi g)) h x =
      ((phi h).γ + ∑ i, (phi h).wt x i) / tangentDenScale (phi h) := by
  exact tangentTheta_factor (phi h) x

/-! ## Numerator directions in the same oriented basis -/

/-- Constant coefficient of the atom numerator in the raw-bit basis. -/
noncomputable def tangentNumConst (phi : FracAtom n) : ℝ :=
  phi.η + ∑ i, phi.ρ i * phi.m i

/-- Variable coefficients of the atom numerator in the raw-bit basis. -/
noncomputable def tangentNumCoeff (phi : FracAtom n) (i : Fin n) : ℝ :=
  phi.ρ i * (phi.α * (phi.m i + phi.δ) - phi.m i)

/-- Coefficients of the normalized atom numerator in the denominator's
oriented literal basis. -/
noncomputable def tangentNumWeights (phi : FracAtom n) :
    Option (Fin n) → ℝ :=
  fun j ↦ orientedAffineWeights (tangentOrientation phi)
    (tangentNumConst phi) (tangentNumCoeff phi) j / tangentDenScale phi

/-- Total barycentric mass of the normalized numerator coefficients. -/
noncomputable def tangentQ (phi : FracAtom n) : ℝ :=
  ∑ j, tangentNumWeights phi j

/-- Centered numerator direction.  Subtracting `q * theta` makes the
coefficient sum zero without changing the represented ratio after the global
mixture correction. -/
noncomputable def tangentV (phi : FracAtom n) : Option (Fin n) → ℝ :=
  fun j ↦ tangentNumWeights phi j - tangentQ phi * tangentTheta phi j

theorem tangentNum_affineValue (phi : FracAtom n) (x : Fin n → Bool) :
    affineValue (tangentNumConst phi) (tangentNumCoeff phi) x =
      phi.η + ∑ i, phi.wt x i *
        (phi.m i + if x i then phi.δ else 0) := by
  classical
  unfold affineValue tangentNumConst tangentNumCoeff
  have hterm : ∀ i : Fin n,
      phi.wt x i * (phi.m i + if x i then phi.δ else 0) =
        phi.ρ i * phi.m i +
          phi.ρ i * (phi.α * (phi.m i + phi.δ) - phi.m i) *
            boolToReal (x i) := by
    intro i
    unfold wt
    cases hxi : x i with
    | false => simp [boolToReal]
    | true =>
        simp [boolToReal]
        ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  ring

theorem tangentNumWeights_factor (phi : FracAtom n) (x : Fin n → Bool) :
    ∑ j, tangentNumWeights phi j *
        orientedLiteral (tangentOrientation phi) j x =
      (phi.η + ∑ i, phi.wt x i *
        (phi.m i + if x i then phi.δ else 0)) / tangentDenScale phi := by
  classical
  unfold tangentNumWeights
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [orientedAffineWeights_eval, tangentNum_affineValue]

theorem tangentV_sum (phi : FracAtom n) : ∑ j, tangentV phi j = 0 := by
  classical
  unfold tangentV tangentQ
  rw [Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  rw [tangentTheta_sum]
  ring

theorem tangentV_directionFactor (phi : FracAtom n) (x : Fin n → Bool) :
    ∑ j, tangentV phi j * orientedLiteral (tangentOrientation phi) j x =
      (phi.η + ∑ i, phi.wt x i *
        (phi.m i + if x i then phi.δ else 0)) / tangentDenScale phi -
        tangentQ phi *
          ((phi.γ + ∑ i, phi.wt x i) / tangentDenScale phi) := by
  classical
  unfold tangentV
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, tangentNumWeights_factor]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, tangentTheta_factor]

/-- The centered direction is the normalized denominator factor times the
atom value minus its centering mass. -/
theorem tangentV_directionFactor_eq_factor_mul
    (phi : FracAtom n) (x : Fin n → Bool) :
    ∑ j, tangentV phi j * orientedLiteral (tangentOrientation phi) j x =
      ((phi.γ + ∑ i, phi.wt x i) / tangentDenScale phi) *
        (phi.eval x - tangentQ phi) := by
  rw [tangentV_directionFactor]
  unfold eval
  have hden := (phi.denom_pos x).ne'
  have hscale := (tangentDenScale_pos phi).ne'
  field_simp

theorem tangentV_family_directionFactor {H : ℕ}
    (phi : Fin H → FracAtom n) (h : Fin H) (x : Fin n → Bool) :
    directionFactor
        (orientedLiteralFamily (fun g ↦ tangentOrientation (phi g)))
        (fun g ↦ tangentV (phi g)) h x =
      factor
        (orientedLiteralFamily (fun g ↦ tangentOrientation (phi g)))
        (fun g ↦ tangentTheta (phi g)) h x *
          ((phi h).eval x - tangentQ (phi h)) := by
  change (∑ j, tangentV (phi h) j *
      orientedLiteral (tangentOrientation (phi h)) j x) =
    (∑ j, tangentTheta (phi h) j *
      orientedLiteral (tangentOrientation (phi h)) j x) *
        ((phi h).eval x - tangentQ (phi h))
  rw [tangentV_directionFactor_eq_factor_mul, tangentTheta_factor]

theorem tangentTheta_family_factor_pos {H : ℕ}
    (phi : Fin H → FracAtom n) (h : Fin H) (x : Fin n → Bool) :
    0 < factor
      (orientedLiteralFamily (fun g ↦ tangentOrientation (phi g)))
      (fun g ↦ tangentTheta (phi g)) h x := by
  rw [tangentTheta_family_factor]
  exact div_pos ((phi h).denom_pos x) (tangentDenScale_pos (phi h))

theorem tangentTheta_productScore_pos {H : ℕ}
    (phi : Fin H → FracAtom n) (x : Fin n → Bool) :
    0 < productScore
      (orientedLiteralFamily (fun g ↦ tangentOrientation (phi g)))
      (fun g ↦ tangentTheta (phi g)) x := by
  classical
  unfold productScore
  exact Finset.prod_pos fun h _ ↦ tangentTheta_family_factor_pos phi h x

/-- The product directional derivative of the centered atom numerators is the
positive common denominator factor times the centered fractional score. -/
theorem tangentV_productDirectionalDerivative {H : ℕ}
    (phi : Fin H → FracAtom n) (x : Fin n → Bool) :
    productDirectionalDerivative
        (orientedLiteralFamily (fun g ↦ tangentOrientation (phi g)))
        (fun g ↦ tangentTheta (phi g)) (fun g ↦ tangentV (phi g)) x =
      productScore
          (orientedLiteralFamily (fun g ↦ tangentOrientation (phi g)))
          (fun g ↦ tangentTheta (phi g)) x *
        ((∑ h, (phi h).eval x) - ∑ h, tangentQ (phi h)) := by
  classical
  letI : DecidableEq (Fin H) := Classical.decEq _
  unfold productDirectionalDerivative
  simp_rw [tangentV_family_directionFactor]
  have hprod : ∀ h : Fin H,
      factor
          (orientedLiteralFamily (fun g ↦ tangentOrientation (phi g)))
          (fun g ↦ tangentTheta (phi g)) h x *
        ∏ g ∈ Finset.univ.erase h,
          factor
            (orientedLiteralFamily (fun k ↦ tangentOrientation (phi k)))
            (fun k ↦ tangentTheta (phi k)) g x =
      productScore
        (orientedLiteralFamily (fun g ↦ tangentOrientation (phi g)))
        (fun g ↦ tangentTheta (phi g)) x := by
    intro h
    unfold productScore
    exact Finset.mul_prod_erase Finset.univ
      (fun g ↦ factor
        (orientedLiteralFamily (fun k ↦ tangentOrientation (phi k)))
        (fun k ↦ tangentTheta (phi k)) g x) (Finset.mem_univ h)
  calc
    _ = ∑ h, productScore
          (orientedLiteralFamily (fun g ↦ tangentOrientation (phi g)))
          (fun g ↦ tangentTheta (phi g)) x *
        ((phi h).eval x - tangentQ (phi h)) := by
      apply Finset.sum_congr rfl
      intro h _
      calc
        _ = (factor
              (orientedLiteralFamily (fun g ↦ tangentOrientation (phi g)))
              (fun g ↦ tangentTheta (phi g)) h x *
            ∏ g ∈ Finset.univ.erase h,
              factor
                (orientedLiteralFamily (fun k ↦ tangentOrientation (phi k)))
                (fun k ↦ tangentTheta (phi k)) g x) *
              ((phi h).eval x - tangentQ (phi h)) := by ring_nf
        _ = _ := by rw [hprod h]
    _ = productScore
          (orientedLiteralFamily (fun g ↦ tangentOrientation (phi g)))
          (fun g ↦ tangentTheta (phi g)) x *
        (∑ h, ((phi h).eval x - tangentQ (phi h))) := by
      rw [Finset.mul_sum]
    _ = _ := by rw [Finset.sum_sub_distrib]

end FracAtom

end HeadComplexity
