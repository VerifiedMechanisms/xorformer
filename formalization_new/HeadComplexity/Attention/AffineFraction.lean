module

public import HeadComplexity.Attention.Basic
public import HeadComplexity.Data.Bool.Cube
public import HeadComplexity.LinearAlgebra.AffineSpace.Coordinates
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Affine fractions for one-layer attention

The positive softmax weights turn the score into a sum of affine fractions on the cube.
Admissibility describes the exact image of the coefficient map for one head.
-/

@[expose] public section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace HeadComplexity.Attention

/-- The logits and scalar readout values of a single head on the all-zero input,
together with their increments on changing an input bit to `true`. -/
structure ScalarHeadProfile (n : ℕ) where
  baseLogit : Option (Fin n) → ℝ
  baseValue : Option (Fin n) → ℝ
  logitIncrement : ℝ
  valueIncrement : ℝ

namespace ScalarHeadProfile

variable {n H d m : ℕ} (p : ScalarHeadProfile n)

/-- The logit at a position for the given input. -/
def logit (x : Fin n → Bool) (j : Option (Fin n)) : ℝ :=
  p.baseLogit j + if (j.map x).getD false then p.logitIncrement else 0

/-- The value at a position after the output map and scalar readout. -/
def value (x : Fin n → Bool) (j : Option (Fin n)) : ℝ :=
  p.baseValue j + if (j.map x).getD false then p.valueIncrement else 0

/-- At the query position, the profile logit is its baseline value and does not depend on the
input. -/
@[simp] theorem logit_none (x : Fin n → Bool) : p.logit x none = p.baseLogit none := by
  simp [logit]

/-- At an input position, a true bit adds the common logit increment to that position's
baseline. -/
@[simp] theorem logit_some (x : Fin n → Bool) (i : Fin n) :
    p.logit x (some i) = p.baseLogit (some i) + if x i then p.logitIncrement else 0 := rfl

/-- The scalar readout value at the query is its baseline value for every input. -/
@[simp] theorem value_none (x : Fin n → Bool) : p.value x none = p.baseValue none := by
  simp [value]

/-- At an input position, a true bit adds the common value increment to that position's
baseline. -/
@[simp] theorem value_some (x : Fin n → Bool) (i : Fin n) :
    p.value x (some i) = p.baseValue (some i) + if x i then p.valueIncrement else 0 := rfl

/-- The unnormalized attention weight of a profile. -/
def weight (x : Fin n → Bool) (j : Option (Fin n)) : ℝ := Real.exp (p.logit x j)

/-- The scalar contribution of a head profile to the score. -/
def eval (x : Fin n → Bool) : ℝ := (∑ j, p.weight x j * p.value x j) / ∑ j, p.weight x j

end ScalarHeadProfile

/-- An affine numerator and denominator with their individual coefficients retained. -/
@[ext] structure AffineFraction (n : ℕ) where
  numerator : (Fin n → ℝ) →ᵃ[ℝ] ℝ
  denominator : (Fin n → ℝ) →ᵃ[ℝ] ℝ

namespace AffineFraction

variable {n : ℕ} (r : AffineFraction n)

/-- Evaluate the fraction on a Boolean vertex. -/
def eval (x : Fin n → Bool) : ℝ :=
  r.numerator (Bool.cubePoint ℝ x) / r.denominator (Bool.cubePoint ℝ x)

/-- The exact coefficient constraints of the softmax parameterization. -/
def Admissible : Prop :=
  (∀ x, 0 < r.denominator (Bool.cubePoint ℝ x)) ∧
    ((∀ i, 0 < r.denominator.coeff i) ∨ (∀ i, r.denominator.coeff i < 0) ∨
      (r.denominator.coeff = 0 ∧
        ((∀ i, 0 < r.numerator.coeff i) ∨ (∀ i, r.numerator.coeff i < 0) ∨
          r.numerator.coeff = 0)))

/-- An admissible affine fraction has a strictly positive denominator at every Boolean vertex. -/
theorem Admissible.denominator_pos {r : AffineFraction n} (hr : r.Admissible)
    (x : Fin n → Bool) : 0 < r.denominator (Bool.cubePoint ℝ x) :=
  hr.1 x

end AffineFraction

variable {n : ℕ}

private structure WeightValues (n : ℕ) where
  ρ : Fin n → ℝ
  m : Fin n → ℝ
  α : ℝ
  δ : ℝ
  γ : ℝ
  η : ℝ
  ρ_pos : ∀ i, 0 < ρ i
  α_pos : 0 < α
  γ_pos : 0 < γ

namespace WeightValues

private def weight (p : WeightValues n) (x : Fin n → Bool) (i : Fin n) : ℝ :=
  p.ρ i * if x i then p.α else 1

private def toAffineFraction (p : WeightValues n) : AffineFraction n :=
  let e := (AffineMap.constCoeffEquiv ℝ (Fin n)).symm
  ⟨e (p.η + ∑ i, p.ρ i * p.m i, fun i ↦ p.ρ i * ((p.α - 1) * p.m i + p.α * p.δ)),
    e (p.γ + ∑ i, p.ρ i, fun i ↦ p.ρ i * (p.α - 1))⟩

/-- Evaluating the affine denominator gives the query weight plus the sum of the input weights. -/
private theorem denominator_apply (p : WeightValues n) (x : Fin n → Bool) :
    p.toAffineFraction.denominator (Bool.cubePoint ℝ x) =
      p.γ + ∑ i, p.weight x i := by
  simp only [toAffineFraction, AffineMap.constCoeffEquiv_symm_apply, dotProduct,
    add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases hx : x i <;> simp [weight, hx]
  ring

/-- Evaluating the affine numerator gives the weighted query value plus the sum of the weighted
input values. -/
private theorem numerator_apply (p : WeightValues n) (x : Fin n → Bool) :
    p.toAffineFraction.numerator (Bool.cubePoint ℝ x) =
      p.η + ∑ i, p.weight x i * (p.m i + if x i then p.δ else 0) := by
  simp only [toAffineFraction, AffineMap.constCoeffEquiv_symm_apply, dotProduct,
    add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases hx : x i <;> simp [weight, hx]
  ring

/-- The weights and scalar values of a head give an affine numerator and denominator satisfying
the admissibility conditions. -/
private theorem admissible (p : WeightValues n) : p.toAffineFraction.Admissible := by
  refine ⟨fun x ↦ ?_, ?_⟩
  · rw [denominator_apply]
    refine add_pos_of_pos_of_nonneg p.γ_pos (Finset.sum_nonneg fun i _ ↦ ?_)
    apply mul_nonneg (p.ρ_pos i).le
    split
    · exact p.α_pos.le
    · exact zero_le_one
  have hC (i : Fin n) :
      p.toAffineFraction.denominator.coeff i = p.ρ i * (p.α - 1) := by
    simp [toAffineFraction]
  rcases lt_trichotomy p.α 1 with h | h | h
  · refine Or.inr (Or.inl fun i ↦ ?_)
    rw [hC]
    exact mul_neg_of_pos_of_neg (p.ρ_pos i) (sub_neg.mpr h)
  · refine Or.inr (Or.inr ⟨funext fun i ↦ by simp [hC, h], ?_⟩)
    have hA (i : Fin n) : p.toAffineFraction.numerator.coeff i = p.ρ i * p.δ := by
      simp [toAffineFraction, h]
    rcases lt_trichotomy p.δ 0 with hδ | hδ | hδ
    · exact Or.inr (Or.inl fun i ↦ by rw [hA]; exact mul_neg_of_pos_of_neg (p.ρ_pos i) hδ)
    · exact Or.inr (Or.inr (funext fun i ↦ by simp [hA, hδ]))
    · exact Or.inl fun i ↦ by rw [hA]; exact mul_pos (p.ρ_pos i) hδ
  · exact Or.inl fun i ↦ by rw [hC]; exact mul_pos (p.ρ_pos i) (sub_pos.mpr h)

/-- Once the input weights fit the slopes and their sum is below the denominator constant, the
query parameters can supply the remaining constants. -/
private theorem realize (r : AffineFraction n) (ρ m : Fin n → ℝ) (α δ : ℝ)
    (hρ : ∀ i, 0 < ρ i) (hα : 0 < α) (hs : ∑ i, ρ i < r.denominator 0)
    (hA : ∀ i, ρ i * ((α - 1) * m i + α * δ) = r.numerator.coeff i)
    (hC : ∀ i, ρ i * (α - 1) = r.denominator.coeff i) :
    ∃ p : WeightValues n, p.toAffineFraction = r := by
  let p : WeightValues n :=
    ⟨ρ, m, α, δ, r.denominator 0 - ∑ i, ρ i, r.numerator 0 - ∑ i, ρ i * m i,
      hρ, hα, sub_pos.mpr hs⟩
  refine ⟨p, AffineFraction.ext ?_ ?_⟩
  · apply (AffineMap.constCoeffEquiv ℝ (Fin n)).injective
    simp [toAffineFraction, p, Prod.ext_iff, funext hA]
  · apply (AffineMap.constCoeffEquiv ℝ (Fin n)).injective
    simp [toAffineFraction, p, Prod.ext_iff, funext hC]

/-- A finite family of positive weights can be divided by a common positive number so that its
sum is below any prescribed positive bound. -/
private theorem exists_small_weights (w : Fin n → ℝ) {d : ℝ}
    (hw : ∀ i, 0 < w i) (hd : 0 < d) :
    ∃ q : ℝ, 0 < q ∧ ∑ i, w i / q < d := by
  let S := ∑ i, w i
  have hq : 0 < 1 + S / d :=
    add_pos_of_pos_of_nonneg one_pos (div_nonneg (Finset.sum_nonneg fun i _ ↦ (hw i).le) hd.le)
  refine ⟨_, hq, ?_⟩
  rw [← Finset.sum_div, div_lt_iff₀ hq]
  change S < d * (1 + S / d)
  rw [mul_add, mul_one, ← mul_div_assoc, mul_div_cancel_left₀ _ hd.ne']
  exact lt_add_of_pos_left S hd

/-- For a constant denominator, weights that fit its constant and reproduce the numerator slopes
with one common increment give an exact realization. -/
private theorem realize_of_zero_denom_coeff (r : AffineFraction n)
    (hC : r.denominator.coeff = 0) (ρ : Fin n → ℝ) (δ : ℝ)
    (hρ : ∀ i, 0 < ρ i) (hs : ∑ i, ρ i < r.denominator 0)
    (hA : ∀ i, ρ i * δ = r.numerator.coeff i) :
    ∃ p : WeightValues n, p.toAffineFraction = r :=
  realize r ρ 0 1 δ hρ one_pos hs (by simpa using hA) (by simp [hC])

/-- Denominator slopes of one strict sign give an exact realization when the denominator is
positive at the all-zero and all-one inputs. -/
private theorem realize_of_ne_zero_denom_coeff (r : AffineFraction n)
    (hd : 0 < r.denominator 0) (hd' : 0 < r.denominator 0 + ∑ i, r.denominator.coeff i)
    (hC : (∀ i, 0 < r.denominator.coeff i) ∨ (∀ i, r.denominator.coeff i < 0))
    [Nonempty (Fin n)] :
    ∃ p : WeightValues n, p.toAffineFraction = r := by
  let C := r.denominator.coeff
  let S := ∑ i, C i
  let d := r.denominator 0
  let γ := min d (d + S) / 2
  have hγd : γ < d := (half_lt_self (lt_min hd hd')).trans_le (min_le_left ..)
  have hγd' : γ < d + S := (half_lt_self (lt_min hd hd')).trans_le (min_le_right ..)
  let u := d - γ
  have hu : 0 < u := sub_pos.mpr hγd
  let t := S / u
  have ht : (∀ i, 0 < C i / t) ∧ t ≠ 0 := by
    rcases hC with h | h
    · have hS : 0 < S := Finset.sum_pos (fun i _ ↦ h i) Finset.univ_nonempty
      exact ⟨fun i ↦ div_pos (h i) (div_pos hS hu), (div_pos hS hu).ne'⟩
    · have hS : S < 0 := Finset.sum_neg (fun i _ ↦ h i) Finset.univ_nonempty
      exact ⟨fun i ↦ div_pos_of_neg_of_neg (h i) (div_neg_of_neg_of_pos hS hu),
        (div_neg_of_neg_of_pos hS hu).ne⟩
  have hα : 0 < 1 + t := by
    change 0 < 1 + S / u
    rw [one_add_div hu.ne']
    exact div_pos (by simpa only [u, sub_add_eq_add_sub] using sub_pos.mpr hγd') hu
  have hs : ∑ i, C i / t < d := by
    rw [← Finset.sum_div]
    change S / (S / u) < d
    rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ (fun hS ↦ ht.2 (by simp [t, hS]))]
    exact sub_lt_self _ (half_pos (lt_min hd hd'))
  refine realize r (fun i ↦ C i / t) (fun i ↦ r.numerator.coeff i / C i) (1 + t) 0
    ht.1 hα hs (fun i ↦ ?_) (fun i ↦ ?_)
  · rw [add_sub_cancel_left, mul_zero, add_zero, ← mul_assoc, div_mul_cancel₀ _ ht.2,
      ← mul_div_assoc, mul_div_cancel_left₀ _ (hC.elim (fun h ↦ (h i).ne') (fun h ↦ (h i).ne))]
  · rw [add_sub_cancel_left, div_mul_cancel₀ _ ht.2]

/-- Every admissible affine fraction arises from positive head weights and scalar values with
exactly the given coefficients. -/
private theorem exists_of_admissible (r : AffineFraction n) (hr : r.Admissible) :
    ∃ p : WeightValues n, p.toAffineFraction = r := by
  have hd : 0 < r.denominator 0 := by
    simpa [show Bool.cubePoint ℝ (fun _ : Fin n ↦ false) = 0 by ext i; simp] using
      hr.denominator_pos (fun _ ↦ false)
  have hd' : 0 < r.denominator 0 + ∑ i, r.denominator.coeff i := by
    rw [← dotProduct_one, ← AffineMap.apply_eq_add_dotProduct]
    simpa [show Bool.cubePoint ℝ (fun _ : Fin n ↦ true) = 1 by ext i; simp] using
      hr.denominator_pos (fun _ ↦ true)
  cases isEmpty_or_nonempty (Fin n)
  · exact realize r 0 0 1 0 (fun i ↦ isEmptyElim i) one_pos (by simpa using hd)
      (fun i ↦ isEmptyElim i) (fun i ↦ isEmptyElim i)
  rcases hr.2 with h | h | ⟨hC, hA⟩
  · exact realize_of_ne_zero_denom_coeff r hd hd' (Or.inl h)
  · exact realize_of_ne_zero_denom_coeff r hd hd' (Or.inr h)
  rcases hA with h | h | h
  · obtain ⟨q, hq, hsum⟩ := exists_small_weights r.numerator.coeff h hd
    exact realize_of_zero_denom_coeff r hC _ q (fun i ↦ div_pos (h i) hq) hsum
      (fun i ↦ div_mul_cancel₀ _ hq.ne')
  · obtain ⟨q, hq, hsum⟩ := exists_small_weights (-r.numerator.coeff) (fun i ↦ neg_pos.mpr (h i)) hd
    exact realize_of_zero_denom_coeff r hC _ (-q) (fun i ↦ div_pos (neg_pos.mpr (h i)) hq) hsum
      (fun i ↦ by simp [hq.ne'])
  · obtain ⟨q, hq, hsum⟩ := exists_small_weights (fun _ : Fin n ↦ 1) (fun _ ↦ one_pos) hd
    exact realize_of_zero_denom_coeff r hC _ 0 (fun _ ↦ div_pos one_pos hq) hsum
      (by simp [h])

end WeightValues

namespace ScalarHeadProfile

private def weightValues (p : ScalarHeadProfile n) : WeightValues n where
  ρ i := Real.exp (p.baseLogit (some i))
  m i := p.baseValue (some i)
  α := Real.exp p.logitIncrement
  δ := p.valueIncrement
  γ := Real.exp (p.baseLogit none)
  η := Real.exp (p.baseLogit none) * p.baseValue none
  ρ_pos i := Real.exp_pos (p.baseLogit (some i))
  α_pos := Real.exp_pos _
  γ_pos := Real.exp_pos _

/-- The numerator and denominator of a head profile, with their exact affine coefficients. -/
@[no_expose]
def toAffineFraction (p : ScalarHeadProfile n) : AffineFraction n :=
  p.weightValues.toAffineFraction

/-- The constant of the affine numerator is the sum of the weighted baseline values at the query
and input positions. -/
theorem toAffineFraction_numerator_apply_zero (p : ScalarHeadProfile n) :
    p.toAffineFraction.numerator 0 =
      Real.exp (p.baseLogit none) * p.baseValue none +
        ∑ i, Real.exp (p.baseLogit (some i)) * p.baseValue (some i) := by
  simp [toAffineFraction, WeightValues.toAffineFraction, weightValues]

/-- The constant of the affine denominator is the sum of the baseline weights at the query and
input positions. -/
theorem toAffineFraction_denominator_apply_zero (p : ScalarHeadProfile n) :
    p.toAffineFraction.denominator 0 =
      Real.exp (p.baseLogit none) + ∑ i, Real.exp (p.baseLogit (some i)) := by
  simp [toAffineFraction, WeightValues.toAffineFraction, weightValues]

/-- The numerator slope at a position is the change in its weighted scalar value when its bit
switches from false to true. -/
theorem toAffineFraction_numerator_coeff (p : ScalarHeadProfile n) (i : Fin n) :
    p.toAffineFraction.numerator.coeff i =
      Real.exp (p.baseLogit (some i)) * ((Real.exp p.logitIncrement - 1) *
        p.baseValue (some i) + Real.exp p.logitIncrement * p.valueIncrement) := by
  simp [toAffineFraction, WeightValues.toAffineFraction, weightValues]

/-- The denominator slope at a position is the change in its softmax weight when its bit
switches from false to true. -/
theorem toAffineFraction_denominator_coeff (p : ScalarHeadProfile n) (i : Fin n) :
    p.toAffineFraction.denominator.coeff i =
      Real.exp (p.baseLogit (some i)) * (Real.exp p.logitIncrement - 1) := by
  simp [toAffineFraction, WeightValues.toAffineFraction, weightValues]

/-- The affine numerator and denominator obtained from a scalar head profile satisfy the
admissibility conditions. -/
theorem toAffineFraction_admissible (p : ScalarHeadProfile n) : p.toAffineFraction.Admissible :=
  p.weightValues.admissible

/-- A scalar head profile and its affine fraction give the same score on every Boolean input. -/
theorem eval_eq_eval_toAffineFraction (p : ScalarHeadProfile n) (x : Fin n → Bool) :
    p.eval x = p.toAffineFraction.eval x := by
  have hw (i : Fin n) : p.weight x (some i) = p.weightValues.weight x i := by
    cases hx : x i <;> simp [weight, WeightValues.weight, weightValues, hx, Real.exp_add]
  have hw0 : p.weight x none = Real.exp (p.baseLogit none) := by simp [weight]
  simp only [eval, AffineFraction.eval, toAffineFraction, WeightValues.numerator_apply,
    WeightValues.denominator_apply, Fintype.sum_option, hw, hw0, value_some, value_none,
    weightValues]

end ScalarHeadProfile

private def WeightValues.toScalarHeadProfile (p : WeightValues n) : ScalarHeadProfile n where
  baseLogit i := i.elim (Real.log p.γ) fun j ↦ Real.log (p.ρ j)
  baseValue i := i.elim (p.η / p.γ) p.m
  logitIncrement := Real.log p.α
  valueIncrement := p.δ

/-- Taking logarithms of the weights to form a scalar head profile and then extracting its
weights recovers the original data. -/
private theorem WeightValues.weightValues_toScalarHeadProfile (p : WeightValues n) :
    p.toScalarHeadProfile.weightValues = p := by
  cases p with
  | mk ρ m α δ γ η hρ hα hγ =>
    simp [toScalarHeadProfile, ScalarHeadProfile.weightValues, Real.exp_log, hρ, hα, hγ,
      ← mul_div_assoc, hγ.ne']

/-- Admissibility is the exact image of the head coefficient map. -/
theorem AffineFraction.realizable_iff (r : AffineFraction n) :
    (∃ p : ScalarHeadProfile n, p.toAffineFraction = r) ↔ r.Admissible := by
  constructor
  · rintro ⟨p, rfl⟩
    exact p.toAffineFraction_admissible
  · intro hr
    obtain ⟨p, hp⟩ := WeightValues.exists_of_admissible r hr
    exact ⟨p.toScalarHeadProfile, by
      rw [ScalarHeadProfile.toAffineFraction, p.weightValues_toScalarHeadProfile, hp]⟩

namespace ScalarHeadProfile

variable {n H d m : ℕ}

private def ofModel (M : Model n H d m) (w : EuclideanSpace ℝ (Fin d)) (h : Fin H) :
    ScalarHeadProfile n where
  baseLogit := M.logit h (fun _ ↦ false)
  baseValue j := ⟪w, M.out h (M.value h (M.embed (fun _ ↦ false) j))⟫_ℝ
  logitIncrement := ⟪M.query h (M.embed (fun _ ↦ false) none),
    M.key h (M.tokenEmbed (some true) - M.tokenEmbed (some false))⟫_ℝ
  valueIncrement :=
    ⟪w, M.out h (M.value h (M.tokenEmbed (some true) - M.tokenEmbed (some false)))⟫_ℝ

/-- The scalar profile extracted from a model gives the original head logit at every position. -/
private theorem ofModel_logit (M : Model n H d m) (w : EuclideanSpace ℝ (Fin d)) (h : Fin H)
    (x : Fin n → Bool) (j : Option (Fin n)) :
    (ofModel M w h).logit x j = M.logit h x j := by
  cases j with
  | none => simp [ofModel, Model.logit]
  | some i =>
    cases hx : x i
    · simp [ofModel, Model.logit, hx]
    · simp [ofModel, Model.logit, hx, map_add, map_sub, inner_add_right, inner_sub_right]
      abel

/-- The scalar profile extracted from a model gives the original value after the head output map
and scalar readout. -/
private theorem ofModel_value (M : Model n H d m) (w : EuclideanSpace ℝ (Fin d)) (h : Fin H)
    (x : Fin n → Bool) (j : Option (Fin n)) :
    (ofModel M w h).value x j = ⟪w, M.out h (M.value h (M.embed x j))⟫_ℝ := by
  cases j with
  | none => simp [ofModel]
  | some i =>
    cases hx : x i
    · simp [ofModel, hx]
    · simp [ofModel, hx, map_add, map_sub, inner_add_right, inner_sub_right]
      abel

end ScalarHeadProfile

/-- Any family of scalar head profiles is realized simultaneously with shared embeddings of
width `n + 2` and one-dimensional head spaces. -/
private theorem exists_model_of_scalarHeadProfile {n H : ℕ} (p : Fin H → ScalarHeadProfile n) :
    ∃ (M : Model n H (n + 2) 1) (w : EuclideanSpace ℝ (Fin (n + 2))),
      (∀ h x j, M.logit h x j = (p h).logit x j) ∧
      (∀ h x j, ⟪w, M.out h (M.value h (M.embed x j))⟫_ℝ = (p h).value x j) := by
  let B := EuclideanSpace.basisFun (Fin (n + 2)) ℝ
  let F := EuclideanSpace.basisFun (Fin 1) ℝ
  let b := Fin.natAdd n (0 : Fin 2)
  let q := Fin.natAdd n (1 : Fin 2)
  let w := B.toBasis q
  let e := F.toBasis 0
  let token : Option Bool → EuclideanSpace ℝ (Fin (n + 2))
    | none => w
    | some x => if x then B.toBasis b else 0
  let position : Option (Fin n) → EuclideanSpace ℝ (Fin (n + 2))
    | none => 0
    | some i => B.toBasis (Fin.castAdd 2 i)
  let read (a : Option (Fin n) → ℝ) (t : ℝ) : EuclideanSpace ℝ (Fin (n + 2)) →ₗ[ℝ] ℝ :=
    B.toBasis.constr ℝ (Fin.addCases (fun i ↦ a (some i)) ![t, a none])
  let M : Model n H (n + 2) 1 :=
    { tokenEmbed := token
      posEmbed := position
      query := fun _ ↦ (read (fun _ ↦ 1) 0).smulRight e
      key := fun h ↦ (read (p h).baseLogit (p h).logitIncrement).smulRight e
      value := fun h ↦ (read (p h).baseValue (p h).valueIncrement).smulRight e
      out := fun _ ↦ (F.toBasis.constr ℝ (fun _ ↦ (1 : ℝ))).smulRight w }
  have read_basis (a : Option (Fin n) → ℝ) (t : ℝ) (j : Fin (n + 2)) :
      read a t (B.toBasis j) = Fin.addCases (fun i ↦ a (some i)) ![t, a none] j :=
    B.toBasis.constr_basis ℝ _ j
  have read_embed (a : Option (Fin n) → ℝ) (t : ℝ) (x : Fin n → Bool) (j : Option (Fin n)) :
      read a t (M.embed x j) = a j + if (j.map x).getD false then t else 0 := by
    cases j with
    | none =>
      change read a t (B.toBasis q + 0) = a none + 0
      rw [add_zero, add_zero, read_basis]
      simp [q, Fin.addCases_right]
    | some i =>
      change read a t ((if x i then B.toBasis b else 0) + B.toBasis (Fin.castAdd 2 i)) =
        a (some i) + if x i then t else 0
      rw [map_add, read_basis, Fin.addCases_left]
      cases x i
      · simp
      · simp only [↓reduceIte, read_basis, b, Fin.addCases_right]
        simp [add_comm]
  have he : ⟪e, e⟫_ℝ = 1 := F.inner_eq_one 0
  have hw : ⟪w, w⟫_ℝ = 1 := B.inner_eq_one q
  refine ⟨M, w, ?_, ?_⟩
  · intro h x j
    change ⟪(read (fun _ ↦ 1) 0).smulRight e (M.embed x none),
      (read (p h).baseLogit (p h).logitIncrement).smulRight e (M.embed x j)⟫_ℝ = _
    simp only [LinearMap.smulRight_apply, read_embed, Option.map_none, Option.getD_none,
      Bool.false_eq_true, if_false, add_zero, one_smul, real_inner_smul_right, he, mul_one,
      ScalarHeadProfile.logit]
  · intro h x j
    change ⟪w, (F.toBasis.constr ℝ (fun _ ↦ (1 : ℝ))).smulRight w
      ((read (p h).baseValue (p h).valueIncrement).smulRight e (M.embed x j))⟫_ℝ = _
    simp only [LinearMap.smulRight_apply, map_smul, e, Module.Basis.constr_basis, mul_one,
      real_inner_smul_right, hw, read_embed, ScalarHeadProfile.value]

/-- Exact scores with a fixed head budget are precisely a constant plus a sum of
scalar head profiles. -/
theorem hasHeadScore_iff_exists_scalarHeadProfile {n H : ℕ} {s : (Fin n → Bool) → ℝ} :
    HasHeadScore s H ↔ ∃ (c : ℝ) (p : Fin H → ScalarHeadProfile n),
      ∀ x, s x = c + ∑ h, (p h).eval x := by
  constructor
  · rintro ⟨d, m, M, w, τ, rfl⟩
    refine ⟨⟪w, M.tokenEmbed none + M.posEmbed none⟫_ℝ - τ,
      ScalarHeadProfile.ofModel M w, fun x ↦ ?_⟩
    simp only [M.score_eq_const_add_sum_div, ScalarHeadProfile.eval, ScalarHeadProfile.weight,
      ScalarHeadProfile.ofModel_logit, ScalarHeadProfile.ofModel_value,
      Model.denominator, Model.weight]
  · rintro ⟨c, p, hp⟩
    obtain ⟨M, w, hlogit, hvalue⟩ := exists_model_of_scalarHeadProfile p
    refine ⟨n + 1, 0, M, w, ⟪w, M.tokenEmbed none + M.posEmbed none⟫_ℝ - c, ?_⟩
    funext x
    rw [hp x, M.score_eq_const_add_sum_div]
    simp only [sub_sub_cancel, Model.denominator, Model.weight, hlogit, hvalue,
      ScalarHeadProfile.eval, ScalarHeadProfile.weight]

end HeadComplexity.Attention

namespace HeadComplexity

open Attention

variable {n H : ℕ} {s : (Fin n → Bool) → ℝ} {f : (Fin n → Bool) → Bool}

/-- Exact shared scores are constants plus one admissible affine fraction per head. -/
theorem hasHeadScore_iff_exists_affineFractions :
    HasHeadScore s H ↔ ∃ (c : ℝ) (r : Fin H → Attention.AffineFraction n),
      (∀ h, (r h).Admissible) ∧ ∀ x, s x = c + ∑ h, (r h).eval x := by
  rw [Attention.hasHeadScore_iff_exists_scalarHeadProfile]
  constructor
  · rintro ⟨c, p, hp⟩
    refine ⟨c, fun h ↦ (p h).toAffineFraction, fun h ↦ (p h).toAffineFraction_admissible, ?_⟩
    simpa only [← ScalarHeadProfile.eval_eq_eval_toAffineFraction] using hp
  · rintro ⟨c, r, hr, hs⟩
    choose p hp using fun h ↦ (r h).realizable_iff.mpr (hr h)
    refine ⟨c, p, ?_⟩
    simpa only [ScalarHeadProfile.eval_eq_eval_toAffineFraction, hp] using hs

/-- Boolean feasibility is sign representation by a sum of admissible affine fractions. -/
theorem computableWithHeads_iff_exists_affineFractions :
    ComputableWithHeads f H ↔ ∃ (c : ℝ) (r : Fin H → Attention.AffineFraction n),
      (∀ h, (r h).Admissible) ∧ Function.SignRepresents (fun x ↦ c + ∑ h, (r h).eval x) f := by
  constructor
  · rintro ⟨s, hs, hf⟩
    obtain ⟨c, r, hr, hs'⟩ := hasHeadScore_iff_exists_affineFractions.mp hs
    refine ⟨c, r, hr, fun x ↦ ?_⟩
    change 0 < c + ∑ h, (r h).eval x ↔ _
    rw [← hs' x]
    exact hf x
  · rintro ⟨c, r, hr, hf⟩
    exact (hasHeadScore_iff_exists_affineFractions.mpr
      ⟨c, r, hr, fun _ ↦ rfl⟩).computableWithHeads hf

end HeadComplexity
