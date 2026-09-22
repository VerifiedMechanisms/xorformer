import HeadComplexity.Results.AffineCylinderThreshold
import HeadComplexity.Results.LowAffineCylinderCost
import HeadComplexity.Results.OneBitGateThresholdDegree
import HeadComplexity.BooleanCube.Symmetry

set_option linter.style.header false

/-!
# Split affine-cylinder certificates

This module packages the first-coordinate form of affine-cylinder cofactor
interpolation.  A split datum records a shared cylinder block and a change
block.  The change block may be gated by either the positive or the negative
fresh literal.  This representation is flexible enough both to align shared
polynomial terms exactly and to obtain a coarse recursion from arbitrary
cofactor certificates.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

noncomputable local instance splitAffineCylinderPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {m : ℕ}

/-- Join two Boolean cofactors along a fresh first coordinate. -/
def joinCofactors (f₀ f₁ : (Fin m → Bool) → Bool) :
    (Fin (m + 1) → Bool) → Bool :=
  fun x ↦ if x 0 then f₁ (tailBits x) else f₀ (tailBits x)

@[simp] theorem joinCofactors_consBit
    (f₀ f₁ : (Fin m → Bool) → Bool) (z : Bool) (y : Fin m → Bool) :
    joinCofactors f₀ f₁ (consBit z y) = if z then f₁ y else f₀ y := by
  cases z <;> simp [joinCofactors]

/-- Lift a tail cylinder without constraining the fresh coordinate. -/
def CubeCylinder.liftTail (C : CubeCylinder m) : CubeCylinder (m + 1) where
  positive := C.positive.image (Fin.succEmb m)
  negative := C.negative.image (Fin.succEmb m)
  disjoint := Finset.disjoint_left.mpr fun i hi₀ hi₁ ↦ by
    rw [Finset.mem_image] at hi₀ hi₁
    obtain ⟨j₀, hj₀, rfl⟩ := hi₀
    obtain ⟨j₁, hj₁, heq⟩ := hi₁
    have : j₀ = j₁ := (Fin.succEmb m).injective heq.symm
    subst j₁
    exact (Finset.disjoint_left.mp C.disjoint hj₀ hj₁).elim

/-- Gate a tail cylinder by the positive fresh literal. -/
def CubeCylinder.liftPositiveFresh (C : CubeCylinder m) :
    CubeCylinder (m + 1) where
  positive := insert 0 (C.positive.image (Fin.succEmb m))
  negative := C.negative.image (Fin.succEmb m)
  disjoint := Finset.disjoint_left.mpr fun i hi₀ hi₁ ↦ by
    rw [Finset.mem_insert] at hi₀
    rcases hi₀ with rfl | hi₀
    · rw [Finset.mem_image] at hi₁
      obtain ⟨j, _, hj⟩ := hi₁
      exact Fin.succ_ne_zero j hj
    · exact (Finset.disjoint_left.mp (CubeCylinder.liftTail C).disjoint)
        hi₀ hi₁

/-- Gate a tail cylinder by the negative fresh literal. -/
def CubeCylinder.liftNegativeFresh (C : CubeCylinder m) :
    CubeCylinder (m + 1) where
  positive := C.positive.image (Fin.succEmb m)
  negative := insert 0 (C.negative.image (Fin.succEmb m))
  disjoint := Finset.disjoint_left.mpr fun i hi₀ hi₁ ↦ by
    rw [Finset.mem_insert] at hi₁
    rcases hi₁ with rfl | hi₁
    · rw [Finset.mem_image] at hi₀
      obtain ⟨j, _, hj⟩ := hi₀
      exact Fin.succ_ne_zero j hj
    · exact (Finset.disjoint_left.mp (CubeCylinder.liftTail C).disjoint)
        hi₀ hi₁

@[simp] theorem CubeCylinder.liftTail_eval_consBit
    (C : CubeCylinder m) (z : Bool) (y : Fin m → Bool) :
    C.liftTail.eval (consBit z y) = C.eval y := by
  unfold CubeCylinder.liftTail CubeCylinder.eval
  change (∏ i ∈ C.positive.image (Fin.succEmb m),
      boolToReal (consBit z y i)) *
      ∏ i ∈ C.negative.image (Fin.succEmb m),
        (1 - boolToReal (consBit z y i)) = _
  rw [Finset.prod_image (Fin.succEmb m).injective.injOn,
    Finset.prod_image (Fin.succEmb m).injective.injOn]
  rfl

@[simp] theorem CubeCylinder.liftPositiveFresh_eval_consBit
    (C : CubeCylinder m) (z : Bool) (y : Fin m → Bool) :
    C.liftPositiveFresh.eval (consBit z y) =
      boolToReal z * C.eval y := by
  unfold CubeCylinder.liftPositiveFresh CubeCylinder.eval
  have hzero : (0 : Fin (m + 1)) ∉ C.positive.image (Fin.succEmb m) := by
    simp
  change (∏ i ∈ insert 0 (C.positive.image (Fin.succEmb m)),
      boolToReal (consBit z y i)) *
      ∏ i ∈ C.negative.image (Fin.succEmb m),
        (1 - boolToReal (consBit z y i)) = _
  rw [Finset.prod_insert hzero,
    Finset.prod_image (Fin.succEmb m).injective.injOn,
    Finset.prod_image (Fin.succEmb m).injective.injOn]
  simp only [consBit_zero]
  have hsucc : ∀ i : Fin m,
      consBit z y ((Fin.succEmb m) i) = y i := consBit_succ z y
  simp_rw [hsucc]
  ring

@[simp] theorem CubeCylinder.liftNegativeFresh_eval_consBit
    (C : CubeCylinder m) (z : Bool) (y : Fin m → Bool) :
    C.liftNegativeFresh.eval (consBit z y) =
      (1 - boolToReal z) * C.eval y := by
  unfold CubeCylinder.liftNegativeFresh CubeCylinder.eval
  have hzero : (0 : Fin (m + 1)) ∉ C.negative.image (Fin.succEmb m) := by
    simp
  change (∏ i ∈ C.positive.image (Fin.succEmb m),
      boolToReal (consBit z y i)) *
      ∏ i ∈ insert 0 (C.negative.image (Fin.succEmb m)),
        (1 - boolToReal (consBit z y i)) = _
  rw [Finset.prod_image (Fin.succEmb m).injective.injOn,
    Finset.prod_insert hzero,
    Finset.prod_image (Fin.succEmb m).injective.injOn]
  simp only [consBit_zero]
  have hsucc : ∀ i : Fin m,
      consBit z y ((Fin.succEmb m) i) = y i := consBit_succ z y
  simp_rw [hsucc]
  ring

theorem CubeCylinder.liftTail_cost (C : CubeCylinder m) :
    C.liftTail.cost = C.cost := by
  unfold CubeCylinder.cost
  change (if C.positive.image (Fin.succEmb m) = ∅ ∧
      C.negative.image (Fin.succEmb m) = ∅ then 0
    else min (2 ^ (C.positive.image (Fin.succEmb m)).card)
      (2 ^ (C.negative.image (Fin.succEmb m)).card)) = _
  simp only [Finset.image_eq_empty,
    Finset.card_image_of_injective _ (Fin.succEmb m).injective,
    Finset.card_image_of_injective _ (Fin.succEmb m).injective]

private theorem min_double_left_le (a b : ℕ) :
    min (2 * a) b ≤ 2 * min a b := by
  by_cases h : a ≤ b
  · rw [Nat.min_eq_left h]
    exact Nat.min_le_left _ _
  · have hba : b ≤ a := Nat.le_of_not_ge h
    rw [Nat.min_eq_right hba]
    exact (Nat.min_le_right _ _).trans (by omega)

private theorem min_double_right_le (a b : ℕ) :
    min a (2 * b) ≤ 2 * min a b := by
  by_cases h : a ≤ b
  · rw [Nat.min_eq_left h]
    exact (Nat.min_le_left _ _).trans (by omega)
  · have hba : b ≤ a := Nat.le_of_not_ge h
    rw [Nat.min_eq_right hba]
    exact Nat.min_le_right _ _

theorem CubeCylinder.liftPositiveFresh_cost_le (C : CubeCylinder m)
    (hnv : ¬ (C.positive = ∅ ∧ C.negative = ∅)) :
    C.liftPositiveFresh.cost ≤ 2 * C.cost := by
  have hfresh : (0 : Fin (m + 1)) ∉ C.positive.image (Fin.succEmb m) := by
    simp
  unfold CubeCylinder.cost
  change (if insert 0 (C.positive.image (Fin.succEmb m)) = ∅ ∧
      C.negative.image (Fin.succEmb m) = ∅ then 0
    else min (2 ^ (insert 0 (C.positive.image (Fin.succEmb m))).card)
      (2 ^ (C.negative.image (Fin.succEmb m)).card)) ≤
      2 * (if C.positive = ∅ ∧ C.negative = ∅ then 0
        else min (2 ^ C.positive.card) (2 ^ C.negative.card))
  rw [if_neg (by simp), if_neg hnv, Finset.card_insert_of_notMem hfresh,
    Finset.card_image_of_injective _ (Fin.succEmb m).injective,
    Finset.card_image_of_injective _ (Fin.succEmb m).injective, pow_succ]
  simpa [Nat.mul_comm] using
    min_double_left_le (2 ^ C.positive.card) (2 ^ C.negative.card)

theorem CubeCylinder.liftNegativeFresh_cost_le (C : CubeCylinder m)
    (hnv : ¬ (C.positive = ∅ ∧ C.negative = ∅)) :
    C.liftNegativeFresh.cost ≤ 2 * C.cost := by
  have hfresh : (0 : Fin (m + 1)) ∉ C.negative.image (Fin.succEmb m) := by
    simp
  unfold CubeCylinder.cost
  change (if C.positive.image (Fin.succEmb m) = ∅ ∧
      insert 0 (C.negative.image (Fin.succEmb m)) = ∅ then 0
    else min (2 ^ (C.positive.image (Fin.succEmb m)).card)
      (2 ^ (insert 0 (C.negative.image (Fin.succEmb m))).card)) ≤
      2 * (if C.positive = ∅ ∧ C.negative = ∅ then 0
        else min (2 ^ C.positive.card) (2 ^ C.negative.card))
  rw [if_neg (by simp), if_neg hnv,
    Finset.card_image_of_injective _ (Fin.succEmb m).injective,
    Finset.card_insert_of_notMem hfresh,
    Finset.card_image_of_injective _ (Fin.succEmb m).injective, pow_succ]
  simpa [Nat.mul_comm] using
    min_double_right_le (2 ^ C.positive.card) (2 ^ C.negative.card)

/-- The positive cylinder for the product of the fresh bit and one tail bit. -/
def freshSlopeCylinder (i : Fin m) : CubeCylinder (m + 1) :=
  CubeCylinder.positiveMonomial {0, i.succ}

@[simp] theorem freshSlopeCylinder_eval_consBit
    (i : Fin m) (z : Bool) (y : Fin m → Bool) :
    (freshSlopeCylinder i).eval (consBit z y) =
      boolToReal z * boolToReal (y i) := by
  change (CubeCylinder.positiveMonomial {0, i.succ}).eval (consBit z y) = _
  rw [CubeCylinder.eval_positiveMonomial]
  unfold squarefreeMonomial
  rw [Finset.prod_pair (Ne.symm (Fin.succ_ne_zero i))]
  simp

@[simp] theorem freshSlopeCylinder_cost (i : Fin m) :
    (freshSlopeCylinder i).cost = 1 := by
  apply CubeCylinder.cost_positiveMonomial
  simp

/-- Affine coefficients after interpolating the two cofactor constants while
keeping the zero-slice tail slopes in the free affine block. -/
def splitAffineCoeff (a₀ a₁ : ℝ) (α₀ : Fin m → ℝ) :
    Fin (m + 1) → ℝ :=
  Fin.cases (a₁ - a₀) α₀

theorem splitAffineValue_consBit
    (a₀ a₁ : ℝ) (α₀ : Fin m → ℝ) (z : Bool) (y : Fin m → Bool) :
    affineValue a₀ (splitAffineCoeff a₀ a₁ α₀) (consBit z y) =
      if z then affineValue a₁ α₀ y else affineValue a₀ α₀ y := by
  cases z <;> simp [affineValue, splitAffineCoeff, Fin.sum_univ_succ, boolToReal] <;>
    ring

/-- A positive-oriented split presentation.  The zero slice uses the shared
base block, while the one slice adds the change block. -/
structure PositiveSplitData
    (f₀ f₁ : (Fin m → Bool) → Bool) where
  affineConst₀ : ℝ
  affineCoeff₀ : Fin m → ℝ
  affineConst₁ : ℝ
  affineCoeff₁ : Fin m → ℝ
  baseCount : ℕ
  baseCylinder : Fin baseCount → CubeCylinder m
  baseCoefficient : Fin baseCount → ℝ
  baseCoefficient_ne_zero : ∀ j, baseCoefficient j ≠ 0
  baseCylinder_nonvacuous : ∀ j,
    ¬ ((baseCylinder j).positive = ∅ ∧ (baseCylinder j).negative = ∅)
  changeCount : ℕ
  changeCylinder : Fin changeCount → CubeCylinder m
  changeCoefficient : Fin changeCount → ℝ
  changeCoefficient_ne_zero : ∀ j, changeCoefficient j ≠ 0
  changeCylinder_nonvacuous : ∀ j,
    ¬ ((changeCylinder j).positive = ∅ ∧ (changeCylinder j).negative = ∅)
  represents₀ : StrictSignRepresentsScore
    (fun y ↦ affineValue affineConst₀ affineCoeff₀ y +
      ∑ j, baseCoefficient j * (baseCylinder j).eval y) f₀
  represents₁ : StrictSignRepresentsScore
    (fun y ↦ affineValue affineConst₁ affineCoeff₁ y +
      ∑ j, baseCoefficient j * (baseCylinder j).eval y +
      ∑ j, changeCoefficient j * (changeCylinder j).eval y) f₁

namespace PositiveSplitData

variable {f₀ f₁ : (Fin m → Bool) → Bool}

/-- Tail slopes that change across the split. -/
noncomputable def changedLinearSupport (D : PositiveSplitData f₀ f₁) :
    Finset (Fin m) :=
  Finset.univ.filter fun i ↦ D.affineCoeff₁ i ≠ D.affineCoeff₀ i

/-- Labels of all ambient cylinder terms: changed slopes, base cylinders, and
positive-fresh-gated change cylinders. -/
abbrev Label (D : PositiveSplitData f₀ f₁) : Type :=
  {i // i ∈ D.changedLinearSupport} ⊕ (Fin D.baseCount ⊕ Fin D.changeCount)

noncomputable def termCylinder (D : PositiveSplitData f₀ f₁) :
    D.Label → CubeCylinder (m + 1)
  | Sum.inl i => freshSlopeCylinder i.1
  | Sum.inr (Sum.inl j) => (D.baseCylinder j).liftTail
  | Sum.inr (Sum.inr j) => (D.changeCylinder j).liftPositiveFresh

noncomputable def termCoefficient (D : PositiveSplitData f₀ f₁) :
    D.Label → ℝ
  | Sum.inl i => D.affineCoeff₁ i.1 - D.affineCoeff₀ i.1
  | Sum.inr (Sum.inl j) => D.baseCoefficient j
  | Sum.inr (Sum.inr j) => D.changeCoefficient j

theorem termCoefficient_ne_zero (D : PositiveSplitData f₀ f₁) :
    ∀ j, D.termCoefficient j ≠ 0 := by
  intro j
  rcases j with i | j
  · exact sub_ne_zero.mpr (Finset.mem_filter.mp i.2).2
  · rcases j with j | j
    · exact D.baseCoefficient_ne_zero j
    · exact D.changeCoefficient_ne_zero j

private theorem sum_changedLinearSupport (D : PositiveSplitData f₀ f₁)
    (y : Fin m → Bool) :
    (∑ i : {i // i ∈ D.changedLinearSupport},
        (D.affineCoeff₁ i.1 - D.affineCoeff₀ i.1) * boolToReal (y i.1)) =
      ∑ i, (D.affineCoeff₁ i - D.affineCoeff₀ i) * boolToReal (y i) := by
  classical
  calc
    (∑ i : {i // i ∈ D.changedLinearSupport},
        (D.affineCoeff₁ i.1 - D.affineCoeff₀ i.1) * boolToReal (y i.1)) =
        ∑ i ∈ D.changedLinearSupport,
          (D.affineCoeff₁ i - D.affineCoeff₀ i) * boolToReal (y i) := by
      simpa only [Finset.attach_eq_univ] using
        D.changedLinearSupport.sum_attach (fun i ↦
          (D.affineCoeff₁ i - D.affineCoeff₀ i) * boolToReal (y i))
    _ = ∑ i,
        (D.affineCoeff₁ i - D.affineCoeff₀ i) * boolToReal (y i) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have heq : D.affineCoeff₁ i = D.affineCoeff₀ i := by
        by_contra hne
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
      simp [heq]

private theorem affine_add_changed_eq (D : PositiveSplitData f₀ f₁)
    (y : Fin m → Bool) :
    affineValue D.affineConst₁ D.affineCoeff₀ y +
        ∑ i : {i // i ∈ D.changedLinearSupport},
          (D.affineCoeff₁ i.1 - D.affineCoeff₀ i.1) * boolToReal (y i.1) =
      affineValue D.affineConst₁ D.affineCoeff₁ y := by
  rw [D.sum_changedLinearSupport y]
  unfold affineValue
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

private theorem termSum_consBit (D : PositiveSplitData f₀ f₁)
    (z : Bool) (y : Fin m → Bool) :
    (∑ j, D.termCoefficient j * (D.termCylinder j).eval (consBit z y)) =
      if z then
        (∑ i : {i // i ∈ D.changedLinearSupport},
            (D.affineCoeff₁ i.1 - D.affineCoeff₀ i.1) * boolToReal (y i.1)) +
          (∑ j, D.baseCoefficient j * (D.baseCylinder j).eval y) +
          ∑ j, D.changeCoefficient j * (D.changeCylinder j).eval y
      else ∑ j, D.baseCoefficient j * (D.baseCylinder j).eval y := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  cases z <;> simp [termCoefficient, termCylinder, boolToReal] <;> ring

noncomputable def ambientCertificate
    (D : PositiveSplitData f₀ f₁) :
    AffineCylinderThresholdCertificate (m + 1) (joinCofactors f₀ f₁) := by
  let e : D.Label ≃ Fin (Fintype.card D.Label) := Fintype.equivFin _
  refine
    { affineConst := D.affineConst₀
      affineCoeff := splitAffineCoeff D.affineConst₀ D.affineConst₁
        D.affineCoeff₀
      termCount := Fintype.card D.Label
      cylinder := fun j ↦ D.termCylinder (e.symm j)
      coefficient := fun j ↦ D.termCoefficient (e.symm j)
      coefficient_ne_zero := fun j ↦ D.termCoefficient_ne_zero (e.symm j)
      represents := ?_ }
  intro x
  rw [← consBit_head_tail x]
  let z := x 0
  let y := tailBits x
  have hsum :
      (∑ j : Fin (Fintype.card D.Label),
          D.termCoefficient (e.symm j) *
            (D.termCylinder (e.symm j)).eval (consBit z y)) =
        ∑ j : D.Label,
          D.termCoefficient j * (D.termCylinder j).eval (consBit z y) := by
    simpa using e.symm.sum_comp (fun j ↦
      D.termCoefficient j * (D.termCylinder j).eval (consBit z y))
  change ((0 < affineValue D.affineConst₀
      (splitAffineCoeff D.affineConst₀ D.affineConst₁ D.affineCoeff₀)
        (consBit z y) +
        ∑ j : Fin (Fintype.card D.Label),
          D.termCoefficient (e.symm j) *
            (D.termCylinder (e.symm j)).eval (consBit z y) ↔
      joinCofactors f₀ f₁ (consBit z y) = true) ∧
    affineValue D.affineConst₀
      (splitAffineCoeff D.affineConst₀ D.affineConst₁ D.affineCoeff₀)
        (consBit z y) +
        ∑ j : Fin (Fintype.card D.Label),
          D.termCoefficient (e.symm j) *
            (D.termCylinder (e.symm j)).eval (consBit z y) ≠ 0)
  rw [hsum, D.termSum_consBit z y, splitAffineValue_consBit,
    joinCofactors_consBit]
  cases z
  · simpa using D.represents₀ y
  · simp only [if_true]
    have hscore :
        affineValue D.affineConst₁ D.affineCoeff₀ y +
            ((∑ i : {i // i ∈ D.changedLinearSupport},
                (D.affineCoeff₁ i.1 - D.affineCoeff₀ i.1) *
                  boolToReal (y i.1)) +
              (∑ j, D.baseCoefficient j * (D.baseCylinder j).eval y) +
              ∑ j, D.changeCoefficient j * (D.changeCylinder j).eval y) =
          affineValue D.affineConst₁ D.affineCoeff₁ y +
            ∑ j, D.baseCoefficient j * (D.baseCylinder j).eval y +
            ∑ j, D.changeCoefficient j * (D.changeCylinder j).eval y := by
      calc
        _ = (affineValue D.affineConst₁ D.affineCoeff₀ y +
              ∑ i : {i // i ∈ D.changedLinearSupport},
                (D.affineCoeff₁ i.1 - D.affineCoeff₀ i.1) *
                  boolToReal (y i.1)) +
              (∑ j, D.baseCoefficient j * (D.baseCylinder j).eval y) +
              ∑ j, D.changeCoefficient j * (D.changeCylinder j).eval y := by
            ring
        _ = _ := by rw [D.affine_add_changed_eq y]
    rw [hscore]
    exact D.represents₁ y

/-- Cost of positive-oriented cofactor interpolation. -/
noncomputable def cost (D : PositiveSplitData f₀ f₁) : ℕ :=
  (if ∃ i, splitAffineCoeff D.affineConst₀ D.affineConst₁
      D.affineCoeff₀ i ≠ 0 then 1 else 0) +
    D.changedLinearSupport.card +
    ∑ j, (D.baseCylinder j).cost +
    ∑ j, (D.changeCylinder j).liftPositiveFresh.cost

theorem ambientCertificate_cost (D : PositiveSplitData f₀ f₁) :
    D.ambientCertificate.cost = D.cost := by
  classical
  let e : D.Label ≃ Fin (Fintype.card D.Label) := Fintype.equivFin _
  have hsum :
      (∑ j : Fin (Fintype.card D.Label),
          (D.termCylinder (e.symm j)).cost) =
        ∑ j : D.Label, (D.termCylinder j).cost := by
    simpa using e.symm.sum_comp (fun j ↦ (D.termCylinder j).cost)
  unfold AffineCylinderThresholdCertificate.cost
    AffineCylinderThresholdCertificate.HasLinearPart cost ambientCertificate
  dsimp only
  by_cases hlin : ∃ i, splitAffineCoeff D.affineConst₀ D.affineConst₁
      D.affineCoeff₀ i ≠ 0
  · simp only [if_pos hlin]
    rw [hsum, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [termCylinder]
    simp_rw [CubeCylinder.liftTail_cost]
    omega

  · simp only [if_neg hlin]
    rw [hsum, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [termCylinder]
    simp_rw [CubeCylinder.liftTail_cost]
    omega

theorem minimumCost_join_le_cost (D : PositiveSplitData f₀ f₁) :
    AffineCylinderThresholdCertificate.minimumCost (joinCofactors f₀ f₁) ≤
      D.cost := by
  rw [← D.ambientCertificate_cost]
  exact AffineCylinderThresholdCertificate.minimumCost_le D.ambientCertificate

theorem HStar_join_le_cost (D : PositiveSplitData f₀ f₁) :
    HStar (m + 1) (joinCofactors f₀ f₁) ≤ D.cost := by
  exact (AffineCylinderThresholdCertificate.HStar_le_minimumCost _).trans
    D.minimumCost_join_le_cost

end PositiveSplitData

/-- A negative-oriented split presentation.  The one slice uses the shared
base block, while the zero slice adds the change block gated by `1 - z`. -/
structure NegativeSplitData
    (f₀ f₁ : (Fin m → Bool) → Bool) where
  affineConst₀ : ℝ
  affineCoeff₀ : Fin m → ℝ
  affineConst₁ : ℝ
  affineCoeff₁ : Fin m → ℝ
  baseCount : ℕ
  baseCylinder : Fin baseCount → CubeCylinder m
  baseCoefficient : Fin baseCount → ℝ
  baseCoefficient_ne_zero : ∀ j, baseCoefficient j ≠ 0
  baseCylinder_nonvacuous : ∀ j,
    ¬ ((baseCylinder j).positive = ∅ ∧ (baseCylinder j).negative = ∅)
  changeCount : ℕ
  changeCylinder : Fin changeCount → CubeCylinder m
  changeCoefficient : Fin changeCount → ℝ
  changeCoefficient_ne_zero : ∀ j, changeCoefficient j ≠ 0
  changeCylinder_nonvacuous : ∀ j,
    ¬ ((changeCylinder j).positive = ∅ ∧ (changeCylinder j).negative = ∅)
  represents₀ : StrictSignRepresentsScore
    (fun y ↦ affineValue affineConst₀ affineCoeff₀ y +
      ∑ j, baseCoefficient j * (baseCylinder j).eval y +
      ∑ j, changeCoefficient j * (changeCylinder j).eval y) f₀
  represents₁ : StrictSignRepresentsScore
    (fun y ↦ affineValue affineConst₁ affineCoeff₁ y +
      ∑ j, baseCoefficient j * (baseCylinder j).eval y) f₁

namespace NegativeSplitData

variable {f₀ f₁ : (Fin m → Bool) → Bool}

noncomputable def changedLinearSupport (D : NegativeSplitData f₀ f₁) :
    Finset (Fin m) :=
  Finset.univ.filter fun i ↦ D.affineCoeff₁ i ≠ D.affineCoeff₀ i

abbrev Label (D : NegativeSplitData f₀ f₁) : Type :=
  {i // i ∈ D.changedLinearSupport} ⊕ (Fin D.baseCount ⊕ Fin D.changeCount)

noncomputable def termCylinder (D : NegativeSplitData f₀ f₁) :
    D.Label → CubeCylinder (m + 1)
  | Sum.inl i => freshSlopeCylinder i.1
  | Sum.inr (Sum.inl j) => (D.baseCylinder j).liftTail
  | Sum.inr (Sum.inr j) => (D.changeCylinder j).liftNegativeFresh

noncomputable def termCoefficient (D : NegativeSplitData f₀ f₁) :
    D.Label → ℝ
  | Sum.inl i => D.affineCoeff₁ i.1 - D.affineCoeff₀ i.1
  | Sum.inr (Sum.inl j) => D.baseCoefficient j
  | Sum.inr (Sum.inr j) => D.changeCoefficient j

theorem termCoefficient_ne_zero (D : NegativeSplitData f₀ f₁) :
    ∀ j, D.termCoefficient j ≠ 0 := by
  intro j
  rcases j with i | j
  · exact sub_ne_zero.mpr (Finset.mem_filter.mp i.2).2
  · rcases j with j | j
    · exact D.baseCoefficient_ne_zero j
    · exact D.changeCoefficient_ne_zero j

private theorem sum_changedLinearSupport (D : NegativeSplitData f₀ f₁)
    (y : Fin m → Bool) :
    (∑ i : {i // i ∈ D.changedLinearSupport},
        (D.affineCoeff₁ i.1 - D.affineCoeff₀ i.1) * boolToReal (y i.1)) =
      ∑ i, (D.affineCoeff₁ i - D.affineCoeff₀ i) * boolToReal (y i) := by
  classical
  calc
    _ = ∑ i ∈ D.changedLinearSupport,
          (D.affineCoeff₁ i - D.affineCoeff₀ i) * boolToReal (y i) := by
      simpa only [Finset.attach_eq_univ] using
        D.changedLinearSupport.sum_attach (fun i ↦
          (D.affineCoeff₁ i - D.affineCoeff₀ i) * boolToReal (y i))
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have heq : D.affineCoeff₁ i = D.affineCoeff₀ i := by
        by_contra hne
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
      simp [heq]

private theorem affine_add_changed_eq (D : NegativeSplitData f₀ f₁)
    (y : Fin m → Bool) :
    affineValue D.affineConst₁ D.affineCoeff₀ y +
        ∑ i : {i // i ∈ D.changedLinearSupport},
          (D.affineCoeff₁ i.1 - D.affineCoeff₀ i.1) * boolToReal (y i.1) =
      affineValue D.affineConst₁ D.affineCoeff₁ y := by
  rw [D.sum_changedLinearSupport y]
  unfold affineValue
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

private theorem termSum_consBit (D : NegativeSplitData f₀ f₁)
    (z : Bool) (y : Fin m → Bool) :
    (∑ j, D.termCoefficient j * (D.termCylinder j).eval (consBit z y)) =
      if z then
        (∑ i : {i // i ∈ D.changedLinearSupport},
            (D.affineCoeff₁ i.1 - D.affineCoeff₀ i.1) * boolToReal (y i.1)) +
          ∑ j, D.baseCoefficient j * (D.baseCylinder j).eval y
      else
        (∑ j, D.baseCoefficient j * (D.baseCylinder j).eval y) +
          ∑ j, D.changeCoefficient j * (D.changeCylinder j).eval y := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  cases z <;> simp [termCoefficient, termCylinder, boolToReal] <;> ring

noncomputable def ambientCertificate
    (D : NegativeSplitData f₀ f₁) :
    AffineCylinderThresholdCertificate (m + 1) (joinCofactors f₀ f₁) := by
  let e : D.Label ≃ Fin (Fintype.card D.Label) := Fintype.equivFin _
  refine
    { affineConst := D.affineConst₀
      affineCoeff := splitAffineCoeff D.affineConst₀ D.affineConst₁
        D.affineCoeff₀
      termCount := Fintype.card D.Label
      cylinder := fun j ↦ D.termCylinder (e.symm j)
      coefficient := fun j ↦ D.termCoefficient (e.symm j)
      coefficient_ne_zero := fun j ↦ D.termCoefficient_ne_zero (e.symm j)
      represents := ?_ }
  intro x
  rw [← consBit_head_tail x]
  let z := x 0
  let y := tailBits x
  have hsum :
      (∑ j : Fin (Fintype.card D.Label),
          D.termCoefficient (e.symm j) *
            (D.termCylinder (e.symm j)).eval (consBit z y)) =
        ∑ j : D.Label,
          D.termCoefficient j * (D.termCylinder j).eval (consBit z y) := by
    simpa using e.symm.sum_comp (fun j ↦
      D.termCoefficient j * (D.termCylinder j).eval (consBit z y))
  change ((0 < affineValue D.affineConst₀
      (splitAffineCoeff D.affineConst₀ D.affineConst₁ D.affineCoeff₀)
        (consBit z y) +
        ∑ j : Fin (Fintype.card D.Label),
          D.termCoefficient (e.symm j) *
            (D.termCylinder (e.symm j)).eval (consBit z y) ↔
      joinCofactors f₀ f₁ (consBit z y) = true) ∧
    affineValue D.affineConst₀
      (splitAffineCoeff D.affineConst₀ D.affineConst₁ D.affineCoeff₀)
        (consBit z y) +
        ∑ j : Fin (Fintype.card D.Label),
          D.termCoefficient (e.symm j) *
            (D.termCylinder (e.symm j)).eval (consBit z y) ≠ 0)
  rw [hsum, D.termSum_consBit z y, splitAffineValue_consBit,
    joinCofactors_consBit]
  cases z
  · simpa [add_assoc] using D.represents₀ y
  · simp only [if_true]
    have hscore :
        affineValue D.affineConst₁ D.affineCoeff₀ y +
            ((∑ i : {i // i ∈ D.changedLinearSupport},
                (D.affineCoeff₁ i.1 - D.affineCoeff₀ i.1) *
                  boolToReal (y i.1)) +
              ∑ j, D.baseCoefficient j * (D.baseCylinder j).eval y) =
          affineValue D.affineConst₁ D.affineCoeff₁ y +
            ∑ j, D.baseCoefficient j * (D.baseCylinder j).eval y := by
      calc
        _ = (affineValue D.affineConst₁ D.affineCoeff₀ y +
              ∑ i : {i // i ∈ D.changedLinearSupport},
                (D.affineCoeff₁ i.1 - D.affineCoeff₀ i.1) *
                  boolToReal (y i.1)) +
              ∑ j, D.baseCoefficient j * (D.baseCylinder j).eval y := by ring
        _ = _ := by rw [D.affine_add_changed_eq y]
    rw [hscore]
    exact D.represents₁ y

noncomputable def cost (D : NegativeSplitData f₀ f₁) : ℕ :=
  (if ∃ i, splitAffineCoeff D.affineConst₀ D.affineConst₁
      D.affineCoeff₀ i ≠ 0 then 1 else 0) +
    D.changedLinearSupport.card +
    ∑ j, (D.baseCylinder j).cost +
    ∑ j, (D.changeCylinder j).liftNegativeFresh.cost

theorem ambientCertificate_cost (D : NegativeSplitData f₀ f₁) :
    D.ambientCertificate.cost = D.cost := by
  classical
  let e : D.Label ≃ Fin (Fintype.card D.Label) := Fintype.equivFin _
  have hsum :
      (∑ j : Fin (Fintype.card D.Label),
          (D.termCylinder (e.symm j)).cost) =
        ∑ j : D.Label, (D.termCylinder j).cost := by
    simpa using e.symm.sum_comp (fun j ↦ (D.termCylinder j).cost)
  unfold AffineCylinderThresholdCertificate.cost
    AffineCylinderThresholdCertificate.HasLinearPart cost ambientCertificate
  dsimp only
  by_cases hlin : ∃ i, splitAffineCoeff D.affineConst₀ D.affineConst₁
      D.affineCoeff₀ i ≠ 0
  · simp only [if_pos hlin]
    rw [hsum, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [termCylinder]
    simp_rw [CubeCylinder.liftTail_cost]
    omega

  · simp only [if_neg hlin]
    rw [hsum, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [termCylinder]
    simp_rw [CubeCylinder.liftTail_cost]
    omega

theorem minimumCost_join_le_cost (D : NegativeSplitData f₀ f₁) :
    AffineCylinderThresholdCertificate.minimumCost (joinCofactors f₀ f₁) ≤
      D.cost := by
  rw [← D.ambientCertificate_cost]
  exact AffineCylinderThresholdCertificate.minimumCost_le D.ambientCertificate

theorem HStar_join_le_cost (D : NegativeSplitData f₀ f₁) :
    HStar (m + 1) (joinCofactors f₀ f₁) ≤ D.cost := by
  exact (AffineCylinderThresholdCertificate.HStar_le_minimumCost _).trans
    D.minimumCost_join_le_cost

end NegativeSplitData

namespace AffineCylinderThresholdCertificate

variable {f : (Fin m → Bool) → Bool}

/-- Terms whose cylinders impose at least one literal. -/
noncomputable def nonvacuousSupport
    (C : AffineCylinderThresholdCertificate m f) : Finset (Fin C.termCount) :=
  Finset.univ.filter fun j ↦
    ¬ ((C.cylinder j).positive = ∅ ∧ (C.cylinder j).negative = ∅)

/-- Terms whose cylinders are the constant-one cylinder. -/
noncomputable def vacuousSupport
    (C : AffineCylinderThresholdCertificate m f) : Finset (Fin C.termCount) :=
  Finset.univ.filter fun j ↦
    (C.cylinder j).positive = ∅ ∧ (C.cylinder j).negative = ∅

private theorem sum_noncacuous_add_vacuous
    {M : Type*} [AddCommMonoid M]
    (C : AffineCylinderThresholdCertificate m f) (g : Fin C.termCount → M) :
    (∑ j ∈ C.nonvacuousSupport, g j) +
        ∑ j ∈ C.vacuousSupport, g j = ∑ j, g j := by
  classical
  have h := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j ↦ ¬ ((C.cylinder j).positive = ∅ ∧
      (C.cylinder j).negative = ∅)) g
  simpa [nonvacuousSupport, vacuousSupport] using h

private theorem eval_eq_one_of_mem_vacuousSupport
    (C : AffineCylinderThresholdCertificate m f) {j : Fin C.termCount}
    (hj : j ∈ C.vacuousSupport) (y : Fin m → Bool) :
    (C.cylinder j).eval y = 1 := by
  have hv := (Finset.mem_filter.mp hj).2
  simp [CubeCylinder.eval, hv.1, hv.2]

/-- Absorb every cost-zero vacuous cylinder into the affine constant. -/
noncomputable def removeVacuous
    (C : AffineCylinderThresholdCertificate m f) :
    AffineCylinderThresholdCertificate m f := by
  let e : {j // j ∈ C.nonvacuousSupport} ≃
      Fin C.nonvacuousSupport.card := C.nonvacuousSupport.equivFin
  refine
    { affineConst := C.affineConst + ∑ j ∈ C.vacuousSupport, C.coefficient j
      affineCoeff := C.affineCoeff
      termCount := C.nonvacuousSupport.card
      cylinder := fun k ↦ C.cylinder (e.symm k).1
      coefficient := fun k ↦ C.coefficient (e.symm k).1
      coefficient_ne_zero := fun k ↦ C.coefficient_ne_zero (e.symm k).1
      represents := ?_ }
  intro y
  have hactive :
      (∑ k : Fin C.nonvacuousSupport.card,
          C.coefficient (e.symm k).1 * (C.cylinder (e.symm k).1).eval y) =
        ∑ j ∈ C.nonvacuousSupport,
          C.coefficient j * (C.cylinder j).eval y := by
    rw [← C.nonvacuousSupport.sum_attach, Finset.attach_eq_univ,
      ← e.symm.sum_comp]
  have hvac :
      (∑ j ∈ C.vacuousSupport,
          C.coefficient j * (C.cylinder j).eval y) =
        ∑ j ∈ C.vacuousSupport, C.coefficient j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [C.eval_eq_one_of_mem_vacuousSupport hj, mul_one]
  have hall := C.sum_noncacuous_add_vacuous
    (fun j ↦ C.coefficient j * (C.cylinder j).eval y)
  change ((0 < affineValue
      (C.affineConst + ∑ j ∈ C.vacuousSupport, C.coefficient j)
      C.affineCoeff y +
      ∑ k : Fin C.nonvacuousSupport.card,
        C.coefficient (e.symm k).1 * (C.cylinder (e.symm k).1).eval y ↔
      f y = true) ∧
    affineValue
      (C.affineConst + ∑ j ∈ C.vacuousSupport, C.coefficient j)
      C.affineCoeff y +
      ∑ k : Fin C.nonvacuousSupport.card,
        C.coefficient (e.symm k).1 * (C.cylinder (e.symm k).1).eval y ≠ 0)
  have hscore :
      affineValue
          (C.affineConst + ∑ j ∈ C.vacuousSupport, C.coefficient j)
          C.affineCoeff y +
          ∑ k : Fin C.nonvacuousSupport.card,
            C.coefficient (e.symm k).1 * (C.cylinder (e.symm k).1).eval y =
        affineValue C.affineConst C.affineCoeff y +
          ∑ j, C.coefficient j * (C.cylinder j).eval y := by
    rw [hactive]
    unfold affineValue
    rw [← hall, hvac]
    ring
  rw [hscore]
  exact C.represents y

theorem removeVacuous_cylinder_nonvacuous
    (C : AffineCylinderThresholdCertificate m f)
    (j : Fin C.removeVacuous.termCount) :
    ¬ (((C.removeVacuous.cylinder j).positive = ∅) ∧
      (C.removeVacuous.cylinder j).negative = ∅) := by
  classical
  unfold removeVacuous at j ⊢
  exact (Finset.mem_filter.mp
    ((C.nonvacuousSupport.equivFin).symm j).2).2

theorem removeVacuous_cost
    (C : AffineCylinderThresholdCertificate m f) :
    C.removeVacuous.cost = C.cost := by
  classical
  let e : {j // j ∈ C.nonvacuousSupport} ≃
      Fin C.nonvacuousSupport.card := C.nonvacuousSupport.equivFin
  have hactive :
      (∑ k : Fin C.nonvacuousSupport.card,
          (C.cylinder (e.symm k).1).cost) =
        ∑ j ∈ C.nonvacuousSupport, (C.cylinder j).cost := by
    rw [← C.nonvacuousSupport.sum_attach, Finset.attach_eq_univ,
      ← e.symm.sum_comp]
  have hvac : ∑ j ∈ C.vacuousSupport, (C.cylinder j).cost = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    simp [CubeCylinder.cost, h.1, h.2]
  have hall := C.sum_noncacuous_add_vacuous
    (fun j ↦ (C.cylinder j).cost)
  unfold cost HasLinearPart removeVacuous
  dsimp only
  rw [hactive, ← hall, hvac]
  simp

end AffineCylinderThresholdCertificate

/-- Positive-oriented interpolation from arbitrary cofactor certificates.
Vacuous terms are first absorbed into the affine constants. -/
noncomputable def positiveSplitDataOfCertificates
    {f₀ f₁ : (Fin m → Bool) → Bool}
    (C₀ : AffineCylinderThresholdCertificate m f₀)
    (C₁ : AffineCylinderThresholdCertificate m f₁) :
    PositiveSplitData f₀ f₁ := by
  let D₀ := C₀.removeVacuous
  let D₁ := C₁.removeVacuous
  let changeCylinder : Fin (D₀.termCount + D₁.termCount) →
      CubeCylinder m := Fin.addCases D₀.cylinder D₁.cylinder
  let changeCoefficient : Fin (D₀.termCount + D₁.termCount) → ℝ :=
    Fin.addCases (fun j ↦ -D₀.coefficient j) D₁.coefficient
  refine
    { affineConst₀ := D₀.affineConst
      affineCoeff₀ := D₀.affineCoeff
      affineConst₁ := D₁.affineConst
      affineCoeff₁ := D₁.affineCoeff
      baseCount := D₀.termCount
      baseCylinder := D₀.cylinder
      baseCoefficient := D₀.coefficient
      baseCoefficient_ne_zero := D₀.coefficient_ne_zero
      baseCylinder_nonvacuous := C₀.removeVacuous_cylinder_nonvacuous
      changeCount := D₀.termCount + D₁.termCount
      changeCylinder := changeCylinder
      changeCoefficient := changeCoefficient
      changeCoefficient_ne_zero := ?_
      changeCylinder_nonvacuous := ?_
      represents₀ := D₀.represents
      represents₁ := ?_ }
  · intro j
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · simpa [changeCoefficient] using
        neg_ne_zero.mpr (D₀.coefficient_ne_zero i)
    · simpa [changeCoefficient] using D₁.coefficient_ne_zero i
  · intro j
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · simpa [changeCylinder] using
        C₀.removeVacuous_cylinder_nonvacuous i
    · simpa [changeCylinder] using
        C₁.removeVacuous_cylinder_nonvacuous i
  · intro y
    have hchange :
        (∑ j : Fin (D₀.termCount + D₁.termCount),
          changeCoefficient j * (changeCylinder j).eval y) =
          -(∑ j, D₀.coefficient j * (D₀.cylinder j).eval y) +
            ∑ j, D₁.coefficient j * (D₁.cylinder j).eval y := by
      rw [Fin.sum_univ_add]
      simp only [changeCoefficient, changeCylinder, Fin.addCases_left,
        Fin.addCases_right, neg_mul,
        Finset.sum_neg_distrib]
    change ((0 < affineValue D₁.affineConst D₁.affineCoeff y +
        (∑ j, D₀.coefficient j * (D₀.cylinder j).eval y) +
        ∑ j : Fin (D₀.termCount + D₁.termCount),
          changeCoefficient j * (changeCylinder j).eval y ↔
          f₁ y = true) ∧
        affineValue D₁.affineConst D₁.affineCoeff y +
          (∑ j, D₀.coefficient j * (D₀.cylinder j).eval y) +
          ∑ j : Fin (D₀.termCount + D₁.termCount),
            changeCoefficient j * (changeCylinder j).eval y ≠ 0)
    rw [hchange]
    have hscore :
        affineValue D₁.affineConst D₁.affineCoeff y +
            (∑ j, D₀.coefficient j * (D₀.cylinder j).eval y) +
            (-(∑ j, D₀.coefficient j * (D₀.cylinder j).eval y) +
              ∑ j, D₁.coefficient j * (D₁.cylinder j).eval y) =
          affineValue D₁.affineConst D₁.affineCoeff y +
            ∑ j, D₁.coefficient j * (D₁.cylinder j).eval y := by ring
    rw [hscore]
    exact D₁.represents y

/-- Negative-oriented interpolation from arbitrary cofactor certificates. -/
noncomputable def negativeSplitDataOfCertificates
    {f₀ f₁ : (Fin m → Bool) → Bool}
    (C₀ : AffineCylinderThresholdCertificate m f₀)
    (C₁ : AffineCylinderThresholdCertificate m f₁) :
    NegativeSplitData f₀ f₁ := by
  let D₀ := C₀.removeVacuous
  let D₁ := C₁.removeVacuous
  let changeCylinder : Fin (D₀.termCount + D₁.termCount) →
      CubeCylinder m := Fin.addCases D₀.cylinder D₁.cylinder
  let changeCoefficient : Fin (D₀.termCount + D₁.termCount) → ℝ :=
    Fin.addCases D₀.coefficient (fun j ↦ -D₁.coefficient j)
  refine
    { affineConst₀ := D₀.affineConst
      affineCoeff₀ := D₀.affineCoeff
      affineConst₁ := D₁.affineConst
      affineCoeff₁ := D₁.affineCoeff
      baseCount := D₁.termCount
      baseCylinder := D₁.cylinder
      baseCoefficient := D₁.coefficient
      baseCoefficient_ne_zero := D₁.coefficient_ne_zero
      baseCylinder_nonvacuous := C₁.removeVacuous_cylinder_nonvacuous
      changeCount := D₀.termCount + D₁.termCount
      changeCylinder := changeCylinder
      changeCoefficient := changeCoefficient
      changeCoefficient_ne_zero := ?_
      changeCylinder_nonvacuous := ?_
      represents₀ := ?_
      represents₁ := D₁.represents }
  · intro j
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · simpa [changeCoefficient] using D₀.coefficient_ne_zero i
    · simpa [changeCoefficient] using
        neg_ne_zero.mpr (D₁.coefficient_ne_zero i)
  · intro j
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · simpa [changeCylinder] using
        C₀.removeVacuous_cylinder_nonvacuous i
    · simpa [changeCylinder] using
        C₁.removeVacuous_cylinder_nonvacuous i
  · intro y
    have hchange :
        (∑ j : Fin (D₀.termCount + D₁.termCount),
          changeCoefficient j * (changeCylinder j).eval y) =
          (∑ j, D₀.coefficient j * (D₀.cylinder j).eval y) -
            ∑ j, D₁.coefficient j * (D₁.cylinder j).eval y := by
      rw [Fin.sum_univ_add]
      simp only [changeCoefficient, changeCylinder, Fin.addCases_left,
        Fin.addCases_right, neg_mul,
        Finset.sum_neg_distrib]
      ring
    change ((0 < affineValue D₀.affineConst D₀.affineCoeff y +
        (∑ j, D₁.coefficient j * (D₁.cylinder j).eval y) +
        ∑ j : Fin (D₀.termCount + D₁.termCount),
          changeCoefficient j * (changeCylinder j).eval y ↔
          f₀ y = true) ∧
        affineValue D₀.affineConst D₀.affineCoeff y +
          (∑ j, D₁.coefficient j * (D₁.cylinder j).eval y) +
          ∑ j : Fin (D₀.termCount + D₁.termCount),
            changeCoefficient j * (changeCylinder j).eval y ≠ 0)
    rw [hchange]
    have hscore :
        affineValue D₀.affineConst D₀.affineCoeff y +
            (∑ j, D₁.coefficient j * (D₁.cylinder j).eval y) +
            ((∑ j, D₀.coefficient j * (D₀.cylinder j).eval y) -
              ∑ j, D₁.coefficient j * (D₁.cylinder j).eval y) =
          affineValue D₀.affineConst D₀.affineCoeff y +
            ∑ j, D₀.coefficient j * (D₀.cylinder j).eval y := by ring
    rw [hscore]
    exact D₀.represents y

/-! ## Coordinate-permutation transport -/

/-- Relabel a cylinder support by a coordinate permutation. -/
def CubeCylinder.permute (C : CubeCylinder m)
    (sigma : Equiv.Perm (Fin m)) : CubeCylinder m where
  positive := C.positive.image sigma
  negative := C.negative.image sigma
  disjoint := Finset.disjoint_left.mpr fun k hk₀ hk₁ ↦ by
    rw [Finset.mem_image] at hk₀ hk₁
    obtain ⟨i₀, hi₀, rfl⟩ := hk₀
    obtain ⟨i₁, hi₁, heq⟩ := hk₁
    have : i₀ = i₁ := sigma.injective heq.symm
    subst i₁
    exact (Finset.disjoint_left.mp C.disjoint hi₀ hi₁).elim

@[simp] theorem CubeCylinder.permute_eval
    (C : CubeCylinder m) (sigma : Equiv.Perm (Fin m))
    (x : Fin m → Bool) :
    (C.permute sigma).eval x = C.eval (permuteBits sigma x) := by
  unfold CubeCylinder.permute CubeCylinder.eval
  rw [Finset.prod_image sigma.injective.injOn,
    Finset.prod_image sigma.injective.injOn]
  rfl

@[simp] theorem CubeCylinder.permute_cost
    (C : CubeCylinder m) (sigma : Equiv.Perm (Fin m)) :
    (C.permute sigma).cost = C.cost := by
  unfold CubeCylinder.permute CubeCylinder.cost
  simp only [Finset.image_eq_empty,
    Finset.card_image_of_injective _ sigma.injective]

private theorem affineValue_permute
    (a : ℝ) (alpha : Fin m → ℝ) (sigma : Equiv.Perm (Fin m))
    (x : Fin m → Bool) :
    affineValue a (fun j ↦ alpha (sigma.symm j)) x =
      affineValue a alpha (permuteBits sigma x) := by
  unfold affineValue
  congr 1
  symm
  apply Fintype.sum_equiv sigma
    (fun i ↦ alpha i * boolToReal (x (sigma i)))
    (fun j ↦ alpha (sigma.symm j) * boolToReal (x j))
  intro i
  simp

namespace AffineCylinderThresholdCertificate

variable {f : (Fin m → Bool) → Bool}

/-- Relabel an affine-cylinder certificate by a coordinate permutation. -/
noncomputable def permute
    (C : AffineCylinderThresholdCertificate m f)
    (sigma : Equiv.Perm (Fin m)) :
    AffineCylinderThresholdCertificate m
      (fun x ↦ f (permuteBits sigma x)) where
  affineConst := C.affineConst
  affineCoeff := fun j ↦ C.affineCoeff (sigma.symm j)
  termCount := C.termCount
  cylinder := fun j ↦ (C.cylinder j).permute sigma
  coefficient := C.coefficient
  coefficient_ne_zero := C.coefficient_ne_zero
  represents := by
    intro x
    have hscore :
        affineValue C.affineConst (fun j ↦ C.affineCoeff (sigma.symm j)) x +
            ∑ j, C.coefficient j * ((C.cylinder j).permute sigma).eval x =
          affineValue C.affineConst C.affineCoeff (permuteBits sigma x) +
            ∑ j, C.coefficient j *
              (C.cylinder j).eval (permuteBits sigma x) := by
      rw [affineValue_permute]
      simp
    change ((0 <
        affineValue C.affineConst (fun j ↦ C.affineCoeff (sigma.symm j)) x +
          ∑ j, C.coefficient j * ((C.cylinder j).permute sigma).eval x ↔
        f (permuteBits sigma x) = true) ∧
      affineValue C.affineConst (fun j ↦ C.affineCoeff (sigma.symm j)) x +
        ∑ j, C.coefficient j * ((C.cylinder j).permute sigma).eval x ≠ 0)
    rw [hscore]
    exact C.represents (permuteBits sigma x)

theorem permute_cost
    (C : AffineCylinderThresholdCertificate m f)
    (sigma : Equiv.Perm (Fin m)) :
    (C.permute sigma).cost = C.cost := by
  have hlinear :
      (C.permute sigma).HasLinearPart ↔ C.HasLinearPart := by
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨sigma.symm j, hj⟩
    · rintro ⟨i, hi⟩
      exact ⟨sigma i, by simpa [permute] using hi⟩
  unfold cost
  rw [if_congr hlinear rfl rfl]
  simp [permute]
  rfl

/-- Permuting coordinates cannot increase minimum affine-cylinder cost. -/
theorem minimumCost_permute_le
    (sigma : Equiv.Perm (Fin m)) (f : (Fin m → Bool) → Bool) :
    minimumCost (fun x ↦ f (permuteBits sigma x)) ≤ minimumCost f := by
  obtain ⟨C, hC⟩ := minimumCost_spec f
  calc
    minimumCost (fun x ↦ f (permuteBits sigma x)) ≤
        (C.permute sigma).cost := minimumCost_le _
    _ = C.cost := C.permute_cost sigma
    _ = minimumCost f := hC

/-- Minimum affine-cylinder cost is invariant under coordinate
permutations. -/
theorem minimumCost_permute
    (sigma : Equiv.Perm (Fin m)) (f : (Fin m → Bool) → Bool) :
    minimumCost (fun x ↦ f (permuteBits sigma x)) = minimumCost f := by
  apply Nat.le_antisymm
  · exact minimumCost_permute_le sigma f
  · have h := minimumCost_permute_le sigma.symm
        (fun x ↦ f (permuteBits sigma x))
    have hfun :
        (fun x ↦ f (permuteBits sigma (permuteBits sigma.symm x))) = f := by
      funext x
      exact congrArg f (by
        simpa only [Equiv.symm_symm] using
          (permuteBits_symm (sigma := sigma.symm) x))
    rwa [hfun] at h

end AffineCylinderThresholdCertificate

end HeadComplexity
