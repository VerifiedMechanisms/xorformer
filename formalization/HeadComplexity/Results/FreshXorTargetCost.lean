import HeadComplexity.Results.SplitAffineCylinder
import HeadComplexity.Results.StructuralInvariances

set_option linter.style.header false

/-!
# Fresh-bit XOR target cost

The invariant below minimizes the exact cost obtained by interpolating a
strict affine-cylinder score with its negation.  Certificates are first put
in the canonical form with no vacuous cylinders, which is necessary because
the local cylinder cost assigns cost zero to the constant-one cylinder.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

noncomputable local instance freshXorTargetCostPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {m : ℕ}

private theorem strictSignRepresentsScore_neg
    {f : (Fin m → Bool) → Bool} {score : (Fin m → Bool) → ℝ}
    (h : StrictSignRepresentsScore score f) :
    StrictSignRepresentsScore (fun y ↦ -score y) (complementFn f) := by
  intro y
  have hy := h y
  cases hfy : f y
  · have hnpos : ¬ 0 < score y := by
      intro hpos
      exact Bool.false_ne_true (hfy.symm.trans (hy.1.mp hpos))
    have hneg : score y < 0 := lt_of_le_of_ne (le_of_not_gt hnpos)
      hy.2
    constructor
    · simp [complementFn, hfy]
      linarith
    · linarith
  · have hpos : 0 < score y := hy.1.mpr hfy
    constructor
    · simp [complementFn, hfy]
      linarith
    · linarith

/-- Indicator for a nonconstant affine block. -/
noncomputable def xorAffineIndicator {f : (Fin m → Bool) → Bool}
    (C : AffineCylinderThresholdCertificate m f) : ℕ :=
  if C.affineConst ≠ 0 ∨ ∃ i, C.affineCoeff i ≠ 0 then 1 else 0

/-- Nonzero affine slopes of a certificate. -/
noncomputable def affineLinearSupport {f : (Fin m → Bool) → Bool}
    (C : AffineCylinderThresholdCertificate m f) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ C.affineCoeff i ≠ 0

/-- Cost of a normalized certificate as a target for fresh-bit XOR. -/
noncomputable def xorTargetCostOf {f : (Fin m → Bool) → Bool}
    (C : AffineCylinderThresholdCertificate m f) : ℕ :=
  let D := C.removeVacuous
  xorAffineIndicator D + (affineLinearSupport D).card +
    (∑ j, (D.cylinder j).cost) +
      min (∑ j, (D.cylinder j).liftPositiveFresh.cost)
        (∑ j, (D.cylinder j).liftNegativeFresh.cost)

private theorem splitAffineIndicator_eq
    {f : (Fin m → Bool) → Bool}
    (C : AffineCylinderThresholdCertificate m f) :
    (if ∃ i, splitAffineCoeff C.affineConst (-C.affineConst)
          C.affineCoeff i ≠ 0 then 1 else 0) = xorAffineIndicator C := by
  have hex :
      (∃ i, splitAffineCoeff C.affineConst (-C.affineConst)
          C.affineCoeff i ≠ 0) ↔
        C.affineConst ≠ 0 ∨ ∃ i, C.affineCoeff i ≠ 0 := by
    constructor
    · rintro ⟨i, hi⟩
      induction i using Fin.cases with
      | zero =>
        left
        intro ha
        simp [splitAffineCoeff, ha] at hi
      | succ j =>
        right
        exact ⟨j, by simpa [splitAffineCoeff] using hi⟩
    · rintro (ha | ⟨i, hi⟩)
      · refine ⟨0, ?_⟩
        simp only [splitAffineCoeff, Fin.cases_zero]
        intro heq
        apply ha
        linarith
      · exact ⟨i.succ, by simpa [splitAffineCoeff] using hi⟩
  unfold xorAffineIndicator
  by_cases h : ∃ i, splitAffineCoeff C.affineConst (-C.affineConst)
      C.affineCoeff i ≠ 0
  · rw [if_pos h, if_pos (hex.mp h)]
  · rw [if_neg h, if_neg (fun h' ↦ h (hex.mpr h'))]

private theorem flippedLinearSupport_eq
    {f : (Fin m → Bool) → Bool}
    (C : AffineCylinderThresholdCertificate m f) :
    (Finset.univ.filter fun i ↦ -C.affineCoeff i ≠ C.affineCoeff i) =
      affineLinearSupport C := by
  ext i
  simp only [affineLinearSupport, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor <;> intro h
  · intro hz
    exact h (by rw [hz]; norm_num)
  · intro heq
    apply h
    linarith

/-- Positive-fresh interpolation of a score and its negation. -/
noncomputable def xorPositiveData
    {f : (Fin m → Bool) → Bool}
    (C : AffineCylinderThresholdCertificate m f)
    (hnv : ∀ j, ¬ ((C.cylinder j).positive = ∅ ∧
      (C.cylinder j).negative = ∅)) :
    PositiveSplitData f (complementFn f) := by
  refine
    { affineConst₀ := C.affineConst
      affineCoeff₀ := C.affineCoeff
      affineConst₁ := -C.affineConst
      affineCoeff₁ := fun i ↦ -C.affineCoeff i
      baseCount := C.termCount
      baseCylinder := C.cylinder
      baseCoefficient := C.coefficient
      baseCoefficient_ne_zero := C.coefficient_ne_zero
      baseCylinder_nonvacuous := hnv
      changeCount := C.termCount
      changeCylinder := C.cylinder
      changeCoefficient := fun j ↦ -2 * C.coefficient j
      changeCoefficient_ne_zero := ?_
      changeCylinder_nonvacuous := hnv
      represents₀ := C.represents
      represents₁ := ?_ }
  · intro j
    exact mul_ne_zero (by norm_num) (C.coefficient_ne_zero j)
  · have hneg := strictSignRepresentsScore_neg C.represents
    convert hneg using 1
    funext y
    have hchange :
        (∑ j, (-2 * C.coefficient j) * (C.cylinder j).eval y) =
          -2 * ∑ j, C.coefficient j * (C.cylinder j).eval y := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
    rw [hchange]
    unfold affineValue
    simp_rw [neg_mul]
    rw [Finset.sum_neg_distrib]
    ring

/-- Negative-fresh interpolation of a score and its negation. -/
noncomputable def xorNegativeData
    {f : (Fin m → Bool) → Bool}
    (C : AffineCylinderThresholdCertificate m f)
    (hnv : ∀ j, ¬ ((C.cylinder j).positive = ∅ ∧
      (C.cylinder j).negative = ∅)) :
    NegativeSplitData f (complementFn f) := by
  refine
    { affineConst₀ := C.affineConst
      affineCoeff₀ := C.affineCoeff
      affineConst₁ := -C.affineConst
      affineCoeff₁ := fun i ↦ -C.affineCoeff i
      baseCount := C.termCount
      baseCylinder := C.cylinder
      baseCoefficient := fun j ↦ -C.coefficient j
      baseCoefficient_ne_zero := fun j ↦
        neg_ne_zero.mpr (C.coefficient_ne_zero j)
      baseCylinder_nonvacuous := hnv
      changeCount := C.termCount
      changeCylinder := C.cylinder
      changeCoefficient := fun j ↦ 2 * C.coefficient j
      changeCoefficient_ne_zero := fun j ↦
        mul_ne_zero (by norm_num) (C.coefficient_ne_zero j)
      changeCylinder_nonvacuous := hnv
      represents₀ := ?_
      represents₁ := ?_ }
  · convert C.represents using 1
    funext y
    have hbase :
        (∑ j, (-C.coefficient j) * (C.cylinder j).eval y) =
          -(∑ j, C.coefficient j * (C.cylinder j).eval y) := by
      simp_rw [neg_mul]
      rw [Finset.sum_neg_distrib]
    have hchange :
        (∑ j, (2 * C.coefficient j) * (C.cylinder j).eval y) =
          2 * ∑ j, C.coefficient j * (C.cylinder j).eval y := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
    rw [hbase, hchange]
    ring
  · have hneg := strictSignRepresentsScore_neg C.represents
    convert hneg using 1
    funext y
    have hbase :
        (∑ j, (-C.coefficient j) * (C.cylinder j).eval y) =
          -(∑ j, C.coefficient j * (C.cylinder j).eval y) := by
      simp_rw [neg_mul]
      rw [Finset.sum_neg_distrib]
    rw [hbase]
    unfold affineValue
    simp_rw [neg_mul]
    rw [Finset.sum_neg_distrib]
    ring

private theorem xorPositiveData_cost
    {f : (Fin m → Bool) → Bool}
    (C : AffineCylinderThresholdCertificate m f)
    (hnv : ∀ j, ¬ ((C.cylinder j).positive = ∅ ∧
      (C.cylinder j).negative = ∅)) :
    (xorPositiveData C hnv).cost =
      xorAffineIndicator C + (affineLinearSupport C).card +
        (∑ j, (C.cylinder j).cost) +
          ∑ j, (C.cylinder j).liftPositiveFresh.cost := by
  unfold PositiveSplitData.cost PositiveSplitData.changedLinearSupport
    xorPositiveData
  dsimp only
  rw [splitAffineIndicator_eq C, flippedLinearSupport_eq C]

private theorem xorNegativeData_cost
    {f : (Fin m → Bool) → Bool}
    (C : AffineCylinderThresholdCertificate m f)
    (hnv : ∀ j, ¬ ((C.cylinder j).positive = ∅ ∧
      (C.cylinder j).negative = ∅)) :
    (xorNegativeData C hnv).cost =
      xorAffineIndicator C + (affineLinearSupport C).card +
        (∑ j, (C.cylinder j).cost) +
          ∑ j, (C.cylinder j).liftNegativeFresh.cost := by
  unfold NegativeSplitData.cost NegativeSplitData.changedLinearSupport
    xorNegativeData
  dsimp only
  rw [splitAffineIndicator_eq C, flippedLinearSupport_eq C]

theorem freshXor_eq_joinCofactors
    (f : (Fin m → Bool) → Bool) :
    freshXor f = joinCofactors f (complementFn f) := by
  funext x
  rw [← consBit_head_tail x]
  cases x 0 <;> simp [freshXor, joinCofactors, complementFn]

theorem HStar_freshXor_le_xorTargetCostOf
    {f : (Fin m → Bool) → Bool}
    (C : AffineCylinderThresholdCertificate m f) :
    HStar (m + 1) (freshXor f) ≤ xorTargetCostOf C := by
  let D := C.removeVacuous
  let hp := ∑ j, (D.cylinder j).liftPositiveFresh.cost
  let hn := ∑ j, (D.cylinder j).liftNegativeFresh.cost
  rw [freshXor_eq_joinCofactors]
  by_cases h : hp ≤ hn
  · have hub := (xorPositiveData D
        C.removeVacuous_cylinder_nonvacuous).HStar_join_le_cost
    rw [xorPositiveData_cost] at hub
    unfold xorTargetCostOf
    dsimp only [D, hp, hn] at h ⊢
    rw [Nat.min_eq_left h]
    exact hub
  · have h' := Nat.le_of_not_ge h
    have hub := (xorNegativeData D
        C.removeVacuous_cylinder_nonvacuous).HStar_join_le_cost
    rw [xorNegativeData_cost] at hub
    unfold xorTargetCostOf
    dsimp only [D, hp, hn] at h' ⊢
    rw [Nat.min_eq_right h']
    exact hub

def XorTargetCostValue
    (f : (Fin m → Bool) → Bool) (K : ℕ) : Prop :=
  ∃ C : AffineCylinderThresholdCertificate m f, xorTargetCostOf C = K

theorem exists_xorTargetCostValue
    (f : (Fin m → Bool) → Bool) :
    ∃ K, XorTargetCostValue f K := by
  obtain ⟨C, _⟩ :=
    AffineCylinderThresholdCertificate.minimumCost_spec f
  exact ⟨xorTargetCostOf C, C, rfl⟩

/-- Minimum normalized affine-cylinder target cost for fresh-bit XOR. -/
noncomputable def xorTargetCost
    (f : (Fin m → Bool) → Bool) : ℕ :=
  Nat.find (exists_xorTargetCostValue f)

theorem xorTargetCost_spec
    (f : (Fin m → Bool) → Bool) :
    XorTargetCostValue f (xorTargetCost f) :=
  Nat.find_spec (exists_xorTargetCostValue f)

theorem xorTargetCost_le
    {f : (Fin m → Bool) → Bool}
    (C : AffineCylinderThresholdCertificate m f) :
    xorTargetCost f ≤ xorTargetCostOf C :=
  Nat.find_min' (exists_xorTargetCostValue f) ⟨C, rfl⟩

theorem HStar_freshXor_le_xorTargetCost
    (f : (Fin m → Bool) → Bool) :
    HStar (m + 1) (freshXor f) ≤ xorTargetCost f := by
  obtain ⟨C, hC⟩ := xorTargetCost_spec f
  rw [← hC]
  exact HStar_freshXor_le_xorTargetCostOf C

theorem thresholdDeg_succ_le_HStar_freshXor
    (f : (Fin m → Bool) → Bool) :
    thresholdDeg f + 1 ≤ HStar (m + 1) (freshXor f) := by
  rw [← thresholdDeg_freshXor]
  exact thresholdDeg_le_HStar _

theorem freshXor_target_bounds
    (f : (Fin m → Bool) → Bool) :
    thresholdDeg f + 1 ≤ HStar (m + 1) (freshXor f) ∧
      HStar (m + 1) (freshXor f) ≤ xorTargetCost f :=
  ⟨thresholdDeg_succ_le_HStar_freshXor f,
    HStar_freshXor_le_xorTargetCost f⟩

theorem freshXnor_target_bounds
    (f : (Fin m → Bool) → Bool) :
    thresholdDeg f + 1 ≤
        HStar (m + 1) (complementFn (freshXor f)) ∧
      HStar (m + 1) (complementFn (freshXor f)) ≤ xorTargetCost f := by
  have hc : HStar (m + 1) (complementFn (freshXor f)) =
      HStar (m + 1) (freshXor f) := by
    change HStar (m + 1) (fun x ↦ !(freshXor f x)) =
      HStar (m + 1) (freshXor f)
    exact HStar_complement (freshXor f)
  rw [hc]
  exact freshXor_target_bounds f

theorem HStar_freshXor_eq_of_target_eq
    (f : (Fin m → Bool) → Bool)
    (h : xorTargetCost f = thresholdDeg f + 1) :
    HStar (m + 1) (freshXor f) = thresholdDeg f + 1 := by
  have hb := freshXor_target_bounds f
  omega

theorem HStar_freshXnor_eq_of_target_eq
    (f : (Fin m → Bool) → Bool)
    (h : xorTargetCost f = thresholdDeg f + 1) :
    HStar (m + 1) (complementFn (freshXor f)) = thresholdDeg f + 1 := by
  have hc : HStar (m + 1) (complementFn (freshXor f)) =
      HStar (m + 1) (freshXor f) := by
    change HStar (m + 1) (fun x ↦ !(freshXor f x)) =
      HStar (m + 1) (freshXor f)
    exact HStar_complement (freshXor f)
  rw [hc]
  exact HStar_freshXor_eq_of_target_eq f h

private theorem cylinderCostSum_le_cost
    {f : (Fin m → Bool) → Bool}
    (C : AffineCylinderThresholdCertificate m f) :
    (∑ j, (C.cylinder j).cost) ≤ C.cost := by
  unfold AffineCylinderThresholdCertificate.cost
  omega

theorem xorTargetCost_le_actc
    (f : (Fin m → Bool) → Bool) :
    xorTargetCost f ≤
      1 + m + 3 * AffineCylinderThresholdCertificate.minimumCost f := by
  obtain ⟨C, hC⟩ :=
    AffineCylinderThresholdCertificate.minimumCost_spec f
  let D := C.removeVacuous
  have heta : xorAffineIndicator D ≤ 1 := by
    unfold xorAffineIndicator
    split <;> omega
  have hlinear : (affineLinearSupport D).card ≤ m := by
    simpa using Finset.card_le_univ (s := affineLinearSupport D)
  have hbase : (∑ j, (D.cylinder j).cost) ≤ C.cost := by
    rw [← C.removeVacuous_cost]
    exact cylinderCostSum_le_cost D
  have hpos :
      (∑ j, (D.cylinder j).liftPositiveFresh.cost) ≤
        2 * ∑ j, (D.cylinder j).cost := by
    have hs := Finset.sum_le_sum fun j
        (_ : j ∈ (Finset.univ : Finset _)) ↦
      CubeCylinder.liftPositiveFresh_cost_le (D.cylinder j)
        (C.removeVacuous_cylinder_nonvacuous j)
    simpa [Finset.mul_sum] using hs
  calc
    xorTargetCost f ≤ xorTargetCostOf C := xorTargetCost_le C
    _ ≤ xorAffineIndicator D + (affineLinearSupport D).card +
        (∑ j, (D.cylinder j).cost) +
          ∑ j, (D.cylinder j).liftPositiveFresh.cost := by
      unfold xorTargetCostOf
      exact Nat.add_le_add_left (Nat.min_le_left _ _) _
    _ ≤ 1 + m + 3 * C.cost := by omega
    _ = _ := by rw [hC]

end HeadComplexity
