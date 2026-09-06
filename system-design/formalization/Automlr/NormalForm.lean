import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The positive linear-fractional normal form

This file formalizes the algebraic core of `answer.md`.  A scalar attention
head is expanded into a quotient of affine functions on the Boolean cube.
Conversely, every affine fraction with an attention-positive denominator is
realized exactly by a scalar head with no bit-dependent value increment.

The theorem `strictScalarRep_iff_strictLFRep` packages these two constructions
at fixed width.  Its scalar-head side excludes the degenerate ratio `t = 1`;
the finite-margin perturbation that removes such heads from a classifier is
described, but not yet formalized, in `formalization/README.md`.
-/

set_option autoImplicit false
set_option linter.style.header false

namespace Automlr

open Finset
open scoped BigOperators

variable {n H : ℕ}

/-- The `n`-dimensional Boolean cube. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- A Boolean bit regarded as a real number. -/
def bitReal (b : Bool) : ℝ := if b then 1 else 0

@[simp] theorem bitReal_false : bitReal false = 0 := rfl
@[simp] theorem bitReal_true : bitReal true = 1 := rfl

/-- An affine real-valued function on the Boolean cube. -/
@[ext]
structure Affine (n : ℕ) where
  const : ℝ
  coeff : Fin n → ℝ

namespace Affine

/-- Evaluation of an affine form on a cube vertex. -/
noncomputable def eval (A : Affine n) (x : Cube n) : ℝ :=
  A.const + ∑ i, A.coeff i * bitReal (x i)

/-- All nonconstant coefficients have one strict orientation. -/
def Coherent (A : Affine n) : Prop :=
  (∀ i, 0 < A.coeff i) ∨ (∀ i, A.coeff i < 0)

/-- Exactly the affine denominators admitted in equation (1) of `answer.md`. -/
def AttentionPositive (A : Affine n) : Prop :=
  A.Coherent ∧ ∀ x, 0 < A.eval x

theorem coeff_ne_of_attentionPositive {A : Affine n}
    (hA : A.AttentionPositive) (i : Fin n) : A.coeff i ≠ 0 := by
  rcases hA.1 with hpos | hneg
  · exact (hpos i).ne'
  · exact (hneg i).ne

end Affine

/-- The scalar normal form of one head after composing its output with the
final linear readout.  The fields correspond to `(q, a_i, t, c_=, c_i, δ)` in
equation (7) of `answer.md`. -/
structure ScalarHead (n : ℕ) where
  queryMass : ℝ
  mass : Fin n → ℝ
  ratio : ℝ
  queryValue : ℝ
  baseValue : Fin n → ℝ
  delta : ℝ
  queryMass_pos : 0 < queryMass
  mass_pos : ∀ i, 0 < mass i
  ratio_pos : 0 < ratio

namespace ScalarHead

/-- The unnormalized attention weight at a bit position. -/
noncomputable def weight (h : ScalarHead n) (x : Cube n) (i : Fin n) : ℝ :=
  h.mass i * if x i then h.ratio else 1

/-- The softmax denominator before normalization. -/
noncomputable def denom (h : ScalarHead n) (x : Cube n) : ℝ :=
  h.queryMass + ∑ i, h.weight x i

/-- The scalar numerator before softmax normalization. -/
noncomputable def numer (h : ScalarHead n) (x : Cube n) : ℝ :=
  h.queryMass * h.queryValue +
    ∑ i, h.weight x i * (h.baseValue i + if x i then h.delta else 0)

/-- The scalar output of a head. -/
noncomputable def eval (h : ScalarHead n) (x : Cube n) : ℝ :=
  h.numer x / h.denom x

theorem weight_pos (h : ScalarHead n) (x : Cube n) (i : Fin n) :
    0 < h.weight x i := by
  cases hx : x i with
  | false => simpa [weight, hx] using h.mass_pos i
  | true => simpa [weight, hx] using mul_pos (h.mass_pos i) h.ratio_pos

theorem denom_pos (h : ScalarHead n) (x : Cube n) : 0 < h.denom x := by
  unfold denom
  exact add_pos_of_pos_of_nonneg h.queryMass_pos
    (Finset.sum_nonneg fun i _ ↦ (h.weight_pos x i).le)

/-- The affine denominator obtained by expanding `t^{x_i}` on Boolean bits. -/
noncomputable def denAffine (h : ScalarHead n) : Affine n where
  const := h.queryMass + ∑ i, h.mass i
  coeff := fun i ↦ (h.ratio - 1) * h.mass i

/-- The affine numerator obtained by expanding the bit-dependent values. -/
noncomputable def numAffine (h : ScalarHead n) : Affine n where
  const := h.queryMass * h.queryValue + ∑ i, h.mass i * h.baseValue i
  coeff := fun i ↦
    h.mass i * (h.ratio * (h.baseValue i + h.delta) - h.baseValue i)

theorem denom_eq_denAffine_eval (h : ScalarHead n) (x : Cube n) :
    h.denom x = h.denAffine.eval x := by
  have hterm : ∀ i : Fin n,
      h.weight x i = h.mass i +
        ((h.ratio - 1) * h.mass i) * bitReal (x i) := by
    intro i
    cases hx : x i with
    | false => simp [weight, bitReal, hx]
    | true => simp [weight, bitReal, hx]; ring
  simp only [denom, Affine.eval, denAffine, hterm]
  rw [Finset.sum_add_distrib]
  ring

theorem numer_eq_numAffine_eval (h : ScalarHead n) (x : Cube n) :
    h.numer x = h.numAffine.eval x := by
  have hterm : ∀ i : Fin n,
      h.weight x i * (h.baseValue i + if x i then h.delta else 0) =
        h.mass i * h.baseValue i +
          (h.mass i *
            (h.ratio * (h.baseValue i + h.delta) - h.baseValue i)) *
              bitReal (x i) := by
    intro i
    cases hx : x i with
    | false => simp [weight, bitReal, hx]
    | true => simp [weight, bitReal, hx]; ring
  simp only [numer, Affine.eval, numAffine, hterm]
  rw [Finset.sum_add_distrib]
  ring

theorem eval_eq_affineFraction (h : ScalarHead n) (x : Cube n) :
    h.eval x = h.numAffine.eval x / h.denAffine.eval x := by
  rw [eval, numer_eq_numAffine_eval, denom_eq_denAffine_eval]

theorem denAffine_coherent (h : ScalarHead n) (hratio : h.ratio ≠ 1) :
    h.denAffine.Coherent := by
  rcases lt_or_gt_of_ne hratio with hlt | hgt
  · right
    intro i
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hlt) (h.mass_pos i)
  · left
    intro i
    exact mul_pos (sub_pos.mpr hgt) (h.mass_pos i)

theorem denAffine_attentionPositive (h : ScalarHead n) (hratio : h.ratio ≠ 1) :
    h.denAffine.AttentionPositive := by
  refine ⟨h.denAffine_coherent hratio, fun x ↦ ?_⟩
  rw [← h.denom_eq_denAffine_eval]
  exact h.denom_pos x

end ScalarHead

/-! ## Exact converse: affine fractions give scalar heads -/

/-- Positive masses and a nondegenerate attention ratio which reproduce a
given attention-positive affine denominator. -/
structure DenominatorParameters (D : Affine n) where
  ratio : ℝ
  queryMass : ℝ
  mass : Fin n → ℝ
  ratio_pos : 0 < ratio
  ratio_ne_one : ratio ≠ 1
  queryMass_pos : 0 < queryMass
  mass_pos : ∀ i, 0 < mass i
  const_eq : queryMass + ∑ i, mass i = D.const
  coeff_eq : ∀ i, (ratio - 1) * mass i = D.coeff i

private def zeroVertex : Cube n := fun _ ↦ false
private def oneVertex : Cube n := fun _ ↦ true

/-- The quantitative content of equations (9) and (10): every
attention-positive affine form is exactly a scalar attention denominator. -/
theorem exists_denominatorParameters (D : Affine n)
    (hD : D.AttentionPositive) : Nonempty (DenominatorParameters D) := by
  have hd0 : 0 < D.const := by
    simpa [Affine.eval, zeroVertex, bitReal] using hD.2 zeroVertex
  rcases hD.1 with hcoeff | hcoeff
  · let s : ℝ := ∑ i, D.coeff i
    let t : ℝ := 2 + s / D.const
    have hs : 0 ≤ s := Finset.sum_nonneg fun i _ ↦ (hcoeff i).le
    have ht : 1 < t := by
      dsimp [t]
      have : 0 ≤ s / D.const := div_nonneg hs hd0.le
      linarith
    have htm1 : 0 < t - 1 := sub_pos.mpr ht
    let mass : Fin n → ℝ := fun i ↦ D.coeff i / (t - 1)
    have hmass : ∀ i, 0 < mass i := fun i ↦ div_pos (hcoeff i) htm1
    have hsum : (∑ i, mass i) = s / (t - 1) := by
      simp only [mass, s, Finset.sum_div]
    have hfrac : s / (t - 1) < D.const := by
      rw [div_lt_iff₀ htm1]
      dsimp [t]
      field_simp [hd0.ne']
      nlinarith
    let q : ℝ := D.const - ∑ i, mass i
    have hq : 0 < q := by
      dsimp [q]
      rw [hsum]
      linarith
    refine ⟨{
      ratio := t
      queryMass := q
      mass := mass
      ratio_pos := lt_trans zero_lt_one ht
      ratio_ne_one := ht.ne'
      queryMass_pos := hq
      mass_pos := hmass
      const_eq := by dsimp [q]; ring
      coeff_eq := fun i ↦ by
        dsimp [mass]
        field_simp [htm1.ne']
    }⟩
  · let s : ℝ := ∑ i, -D.coeff i
    have hs : 0 ≤ s := Finset.sum_nonneg fun i _ ↦ (neg_pos.mpr (hcoeff i)).le
    have hall : 0 < D.const + ∑ i, D.coeff i := by
      simpa [Affine.eval, oneVertex, bitReal] using hD.2 oneVertex
    have hslt : s < D.const := by
      dsimp [s]
      rw [Finset.sum_neg_distrib]
      linarith
    let t : ℝ := (D.const - s) / (2 * D.const)
    have htpos : 0 < t := by
      dsimp [t]
      exact div_pos (sub_pos.mpr hslt) (mul_pos zero_lt_two hd0)
    have htlt : t < 1 := by
      dsimp [t]
      rw [div_lt_one (mul_pos zero_lt_two hd0)]
      linarith
    have htm1 : t - 1 < 0 := sub_neg.mpr htlt
    let mass : Fin n → ℝ := fun i ↦ D.coeff i / (t - 1)
    have hmass : ∀ i, 0 < mass i :=
      fun i ↦ div_pos_of_neg_of_neg (hcoeff i) htm1
    have hsum : (∑ i, mass i) = (-s) / (t - 1) := by
      rw [show -s = ∑ i, D.coeff i by
        dsimp [s]
        rw [Finset.sum_neg_distrib, neg_neg]]
      simp only [mass, Finset.sum_div]
    have hfrac : (-s) / (t - 1) < D.const := by
      rw [div_lt_iff_of_neg htm1]
      dsimp [t]
      field_simp [hd0.ne']
      nlinarith
    let q : ℝ := D.const - ∑ i, mass i
    have hq : 0 < q := by
      dsimp [q]
      rw [hsum]
      linarith
    refine ⟨{
      ratio := t
      queryMass := q
      mass := mass
      ratio_pos := htpos
      ratio_ne_one := htlt.ne
      queryMass_pos := hq
      mass_pos := hmass
      const_eq := by dsimp [q]; ring
      coeff_eq := fun i ↦ by
        dsimp [mass]
        field_simp [htm1.ne]
    }⟩

/-- Every admissible affine numerator-denominator pair is realized exactly by
one nondegenerate scalar head, with `delta = 0`. -/
theorem exists_scalarHead_of_attentionPositive (N D : Affine n)
    (hD : D.AttentionPositive) :
    ∃ h : ScalarHead n,
      h.ratio ≠ 1 ∧ h.delta = 0 ∧ h.numAffine = N ∧ h.denAffine = D := by
  classical
  let p : DenominatorParameters D := Classical.choice (exists_denominatorParameters D hD)
  let base : Fin n → ℝ := fun i ↦ N.coeff i / D.coeff i
  let queryValue : ℝ :=
    (N.const - ∑ i, p.mass i * base i) / p.queryMass
  let h : ScalarHead n := {
    queryMass := p.queryMass
    mass := p.mass
    ratio := p.ratio
    queryValue := queryValue
    baseValue := base
    delta := 0
    queryMass_pos := p.queryMass_pos
    mass_pos := p.mass_pos
    ratio_pos := p.ratio_pos
  }
  refine ⟨h, p.ratio_ne_one, rfl, ?_, ?_⟩
  · apply Affine.ext
    · change p.queryMass * queryValue + ∑ i, p.mass i * base i = N.const
      dsimp [queryValue]
      field_simp [p.queryMass_pos.ne']
      ring
    · funext i
      change p.mass i * (p.ratio * (base i + 0) - base i) = N.coeff i
      have hdne : D.coeff i ≠ 0 := Affine.coeff_ne_of_attentionPositive hD i
      rw [show p.ratio * (base i + 0) - base i =
          (p.ratio - 1) * base i by ring]
      rw [show p.mass i * ((p.ratio - 1) * base i) =
          ((p.ratio - 1) * p.mass i) * base i by ring, p.coeff_eq i]
      dsimp [base]
      exact mul_div_cancel₀ (N.coeff i) hdne
  · apply Affine.ext
    · exact p.const_eq
    · funext i
      exact p.coeff_eq i

/-! ## Fixed-width classifier equivalence -/

/-- Strict sign representation of a Boolean function. -/
def StrictlyRepresents (score : Cube n → ℝ) (f : Cube n → Bool) : Prop :=
  ∀ x, if f x then 0 < score x else score x < 0

/-- A strict width-`H` certificate by nondegenerate scalar heads. -/
def StrictScalarRep (n H : ℕ) (f : Cube n → Bool) : Prop :=
  ∃ head : Fin H → ScalarHead n,
    (∀ h, (head h).ratio ≠ 1) ∧
      StrictlyRepresents (fun x ↦ ∑ h, (head h).eval x) f

/-- A strict width-`H` positive linear-fractional certificate (equation (1)). -/
def StrictLFRep (n H : ℕ) (f : Cube n → Bool) : Prop :=
  ∃ (num den : Fin H → Affine n),
    (∀ h, (den h).AttentionPositive) ∧
      StrictlyRepresents (fun x ↦ ∑ h, (num h).eval x / (den h).eval x) f

/-- The machine-checked scalar normal-form theorem, at every fixed width. -/
theorem strictScalarRep_iff_strictLFRep (n H : ℕ) (f : Cube n → Bool) :
    StrictScalarRep n H f ↔ StrictLFRep n H f := by
  constructor
  · rintro ⟨head, hratio, hrep⟩
    refine ⟨fun h ↦ (head h).numAffine, fun h ↦ (head h).denAffine,
      fun h ↦ (head h).denAffine_attentionPositive (hratio h), ?_⟩
    intro x
    simpa only [ScalarHead.eval_eq_affineFraction] using hrep x
  · rintro ⟨num, den, hden, hrep⟩
    classical
    have hex : ∀ i, ∃ h : ScalarHead n,
        h.ratio ≠ 1 ∧ h.delta = 0 ∧ h.numAffine = num i ∧ h.denAffine = den i :=
      fun i ↦ exists_scalarHead_of_attentionPositive (num i) (den i) (hden i)
    choose head hratio hdelta hnum hdeneq using hex
    refine ⟨head, hratio, ?_⟩
    intro x
    have heval : ∀ i, (head i).eval x = (num i).eval x / (den i).eval x := by
      intro i
      rw [ScalarHead.eval_eq_affineFraction, hnum i, hdeneq i]
    simpa only [heval] using hrep x

/-! ## Clearing the positive denominators -/

/-- The product of all denominators at a cube point. -/
noncomputable def denominatorProduct (den : Fin H → Affine n) (x : Cube n) : ℝ :=
  ∏ h, (den h).eval x

/-- The shared-factor expression in equation (3), evaluated on the cube. -/
noncomputable def clearedScore (num den : Fin H → Affine n) (x : Cube n) : ℝ :=
  ∑ h, (num h).eval x *
    ∏ k ∈ Finset.univ.erase h, (den k).eval x

/-- Exact denominator-clearing identity. -/
theorem clearedScore_eq_product_mul_score
    (num den : Fin H → Affine n) (x : Cube n)
    (hden : ∀ h, (den h).eval x ≠ 0) :
    clearedScore num den x = denominatorProduct den x *
      ∑ h, (num h).eval x / (den h).eval x := by
  classical
  rw [denominatorProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun h _ ↦ ?_)
  rw [← Finset.mul_prod_erase Finset.univ
    (fun k ↦ (den k).eval x) (Finset.mem_univ h)]
  field_simp [hden h]

theorem denominatorProduct_pos (den : Fin H → Affine n)
    (hden : ∀ h, (den h).AttentionPositive) (x : Cube n) :
    0 < denominatorProduct den x := by
  unfold denominatorProduct
  exact Finset.prod_pos fun h _ ↦ (hden h).2 x

/-- Clearing admissible denominators preserves the strict sign pointwise. -/
theorem clearedScore_pos_iff_fractionalScore_pos
    (num den : Fin H → Affine n)
    (hden : ∀ h, (den h).AttentionPositive) (x : Cube n) :
    0 < clearedScore num den x ↔
      0 < ∑ h, (num h).eval x / (den h).eval x := by
  rw [clearedScore_eq_product_mul_score num den x
    (fun h ↦ ((hden h).2 x).ne')]
  exact mul_pos_iff_of_pos_left (denominatorProduct_pos den hden x)

/-- With one positive denominator, the quotient has exactly the numerator's
sign.  This is the algebraic content of the one-head/LTF criterion. -/
theorem oneFraction_pos_iff_numerator_pos (N D : Affine n)
    (hD : D.AttentionPositive) (x : Cube n) :
    0 < N.eval x / D.eval x ↔ 0 < N.eval x := by
  exact div_pos_iff_of_pos_right ((hD.2 x))

theorem oneFraction_neg_iff_numerator_neg (N D : Affine n)
    (hD : D.AttentionPositive) (x : Cube n) :
    N.eval x / D.eval x < 0 ↔ N.eval x < 0 := by
  constructor
  · intro hneg
    rcases div_neg_iff.mp hneg with hbad | hgood
    · exact (not_lt_of_ge (hD.2 x).le hbad.2).elim
    · exact hgood.1
  · intro hneg
    exact div_neg_of_neg_of_pos hneg (hD.2 x)

/-- A fixed attention-positive denominator used to embed any strict affine
threshold certificate into the one-fraction class. -/
noncomputable def canonicalDenominator (n : ℕ) : Affine n where
  const := 1
  coeff := fun _ ↦ 1

theorem canonicalDenominator_attentionPositive (n : ℕ) :
    (canonicalDenominator n).AttentionPositive := by
  refine ⟨Or.inl (fun _ ↦ zero_lt_one), fun x ↦ ?_⟩
  simp only [canonicalDenominator, Affine.eval, one_mul]
  have hsum : 0 ≤ ∑ i, bitReal (x i) := by
    apply Finset.sum_nonneg
    intro i _
    cases x i <;> simp [bitReal]
  linarith

/-- Strict affine-threshold representation. -/
def StrictLTFRep (n : ℕ) (f : Cube n → Bool) : Prop :=
  ∃ N : Affine n, StrictlyRepresents N.eval f

/-- A width-one positive linear-fractional certificate is exactly a strict
linear threshold certificate. -/
theorem strictLFRep_one_iff_strictLTFRep (n : ℕ) (f : Cube n → Bool) :
    StrictLFRep n 1 f ↔ StrictLTFRep n f := by
  constructor
  · rintro ⟨num, den, hden, hrep⟩
    refine ⟨num 0, fun x ↦ ?_⟩
    have hx := hrep x
    cases hfx : f x with
    | false =>
        simp only [hfx, Bool.false_eq_true, ↓reduceIte, Fin.sum_univ_one] at hx ⊢
        exact (oneFraction_neg_iff_numerator_neg (num 0) (den 0) (hden 0) x).mp hx
    | true =>
        simp only [hfx, ↓reduceIte, Fin.sum_univ_one] at hx ⊢
        exact (oneFraction_pos_iff_numerator_pos (num 0) (den 0) (hden 0) x).mp hx
  · rintro ⟨N, hrep⟩
    refine ⟨fun _ ↦ N, fun _ ↦ canonicalDenominator n,
      fun _ ↦ canonicalDenominator_attentionPositive n, fun x ↦ ?_⟩
    have hx := hrep x
    cases hfx : f x with
    | false =>
        simp only [hfx, Bool.false_eq_true, ↓reduceIte, Fin.sum_univ_one] at hx ⊢
        exact (oneFraction_neg_iff_numerator_neg N (canonicalDenominator n)
          (canonicalDenominator_attentionPositive n) x).mpr hx
    | true =>
        simp only [hfx, ↓reduceIte, Fin.sum_univ_one] at hx ⊢
        exact (oneFraction_pos_iff_numerator_pos N (canonicalDenominator n)
          (canonicalDenominator_attentionPositive n) x).mpr hx

end Automlr
