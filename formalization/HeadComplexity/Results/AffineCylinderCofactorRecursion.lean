import HeadComplexity.Results.SplitAffineCylinder

set_option linter.style.header false

/-!
# Affine-cylinder cofactor recursion

This module defines the attained first-coordinate split affine-cylinder cost
and proves the coarse Shannon recurrence from arbitrary optimal cofactor
certificates.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

noncomputable local instance affineCylinderRecursionPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {m : ℕ}

/-- A cost is realized by one of the two orientations of a split
affine-cylinder presentation. -/
def SplitAffineCylinderCost
    (f₀ f₁ : (Fin m → Bool) → Bool) (K : ℕ) : Prop :=
  (∃ D : PositiveSplitData f₀ f₁, D.cost = K) ∨
    ∃ D : NegativeSplitData f₀ f₁, D.cost = K

theorem exists_splitAffineCylinderCost
    (f₀ f₁ : (Fin m → Bool) → Bool) :
    ∃ K, SplitAffineCylinderCost f₀ f₁ K := by
  obtain ⟨C₀, _⟩ :=
    AffineCylinderThresholdCertificate.minimumCost_spec f₀
  obtain ⟨C₁, _⟩ :=
    AffineCylinderThresholdCertificate.minimumCost_spec f₁
  let D := positiveSplitDataOfCertificates C₀ C₁
  exact ⟨D.cost, Or.inl ⟨D, rfl⟩⟩

/-- Minimum first-coordinate split affine-cylinder cost. -/
noncomputable def splitAffineCylinderCost
    (f₀ f₁ : (Fin m → Bool) → Bool) : ℕ :=
  Nat.find (exists_splitAffineCylinderCost f₀ f₁)

theorem splitAffineCylinderCost_spec
    (f₀ f₁ : (Fin m → Bool) → Bool) :
    SplitAffineCylinderCost f₀ f₁
      (splitAffineCylinderCost f₀ f₁) :=
  Nat.find_spec (exists_splitAffineCylinderCost f₀ f₁)

theorem splitAffineCylinderCost_le_positive
    {f₀ f₁ : (Fin m → Bool) → Bool}
    (D : PositiveSplitData f₀ f₁) :
    splitAffineCylinderCost f₀ f₁ ≤ D.cost :=
  Nat.find_min' (exists_splitAffineCylinderCost f₀ f₁)
    (Or.inl ⟨D, rfl⟩)

theorem splitAffineCylinderCost_le_negative
    {f₀ f₁ : (Fin m → Bool) → Bool}
    (D : NegativeSplitData f₀ f₁) :
    splitAffineCylinderCost f₀ f₁ ≤ D.cost :=
  Nat.find_min' (exists_splitAffineCylinderCost f₀ f₁)
    (Or.inr ⟨D, rfl⟩)

theorem actc_join_le_splitAffineCylinderCost
    (f₀ f₁ : (Fin m → Bool) → Bool) :
    AffineCylinderThresholdCertificate.minimumCost (joinCofactors f₀ f₁) ≤
      splitAffineCylinderCost f₀ f₁ := by
  rcases splitAffineCylinderCost_spec f₀ f₁ with ⟨D, hD⟩ | ⟨D, hD⟩
  · rw [← hD]
    exact D.minimumCost_join_le_cost
  · rw [← hD]
    exact D.minimumCost_join_le_cost

theorem HStar_join_le_splitAffineCylinderCost
    (f₀ f₁ : (Fin m → Bool) → Bool) :
    HStar (m + 1) (joinCofactors f₀ f₁) ≤
      splitAffineCylinderCost f₀ f₁ :=
  (AffineCylinderThresholdCertificate.HStar_le_minimumCost _).trans
    (actc_join_le_splitAffineCylinderCost f₀ f₁)

private theorem cylinderCostSum_le_cost
    {f : (Fin m → Bool) → Bool}
    (C : AffineCylinderThresholdCertificate m f) :
    (∑ j, (C.cylinder j).cost) ≤ C.cost := by
  unfold AffineCylinderThresholdCertificate.cost
  omega

private theorem positive_generated_cost_le
    {f₀ f₁ : (Fin m → Bool) → Bool}
    (C₀ : AffineCylinderThresholdCertificate m f₀)
    (C₁ : AffineCylinderThresholdCertificate m f₁) :
    (positiveSplitDataOfCertificates C₀ C₁).cost ≤
      1 + m + 3 * C₀.cost + 2 * C₁.cost := by
  let D₀ := C₀.removeVacuous
  let D₁ := C₁.removeVacuous
  have hlin :
      (if ∃ i, splitAffineCoeff D₀.affineConst D₁.affineConst
          D₀.affineCoeff i ≠ 0 then 1 else 0) ≤ 1 := by
    split <;> omega
  have hslope :
      (Finset.univ.filter fun i ↦
        D₁.affineCoeff i ≠ D₀.affineCoeff i).card ≤ m := by
    simpa using Finset.card_le_univ
      (s := Finset.univ.filter fun i : Fin m ↦
        D₁.affineCoeff i ≠ D₀.affineCoeff i)
  have hlift₀ :
      (∑ j, (D₀.cylinder j).liftPositiveFresh.cost) ≤
        2 * ∑ j, (D₀.cylinder j).cost := by
    have h := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset _)) ↦
      CubeCylinder.liftPositiveFresh_cost_le (D₀.cylinder j)
        (C₀.removeVacuous_cylinder_nonvacuous j)
    simpa [Finset.mul_sum] using h
  have hlift₁ :
      (∑ j, (D₁.cylinder j).liftPositiveFresh.cost) ≤
        2 * ∑ j, (D₁.cylinder j).cost := by
    have h := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset _)) ↦
      CubeCylinder.liftPositiveFresh_cost_le (D₁.cylinder j)
        (C₁.removeVacuous_cylinder_nonvacuous j)
    simpa [Finset.mul_sum] using h
  have hsum₀ : (∑ j, (D₀.cylinder j).cost) ≤ C₀.cost := by
    rw [← C₀.removeVacuous_cost]
    exact cylinderCostSum_le_cost D₀
  have hsum₁ : (∑ j, (D₁.cylinder j).cost) ≤ C₁.cost := by
    rw [← C₁.removeVacuous_cost]
    exact cylinderCostSum_le_cost D₁
  dsimp only [D₀, D₁] at hlin hslope hlift₀ hlift₁ hsum₀ hsum₁
  unfold PositiveSplitData.cost PositiveSplitData.changedLinearSupport
    positiveSplitDataOfCertificates
  dsimp only
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  omega

private theorem negative_generated_cost_le
    {f₀ f₁ : (Fin m → Bool) → Bool}
    (C₀ : AffineCylinderThresholdCertificate m f₀)
    (C₁ : AffineCylinderThresholdCertificate m f₁) :
    (negativeSplitDataOfCertificates C₀ C₁).cost ≤
      1 + m + 2 * C₀.cost + 3 * C₁.cost := by
  let D₀ := C₀.removeVacuous
  let D₁ := C₁.removeVacuous
  have hlin :
      (if ∃ i, splitAffineCoeff D₀.affineConst D₁.affineConst
          D₀.affineCoeff i ≠ 0 then 1 else 0) ≤ 1 := by
    split <;> omega
  have hslope :
      (Finset.univ.filter fun i ↦
        D₁.affineCoeff i ≠ D₀.affineCoeff i).card ≤ m := by
    simpa using Finset.card_le_univ
      (s := Finset.univ.filter fun i : Fin m ↦
        D₁.affineCoeff i ≠ D₀.affineCoeff i)
  have hlift₀ :
      (∑ j, (D₀.cylinder j).liftNegativeFresh.cost) ≤
        2 * ∑ j, (D₀.cylinder j).cost := by
    have h := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset _)) ↦
      CubeCylinder.liftNegativeFresh_cost_le (D₀.cylinder j)
        (C₀.removeVacuous_cylinder_nonvacuous j)
    simpa [Finset.mul_sum] using h
  have hlift₁ :
      (∑ j, (D₁.cylinder j).liftNegativeFresh.cost) ≤
        2 * ∑ j, (D₁.cylinder j).cost := by
    have h := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset _)) ↦
      CubeCylinder.liftNegativeFresh_cost_le (D₁.cylinder j)
        (C₁.removeVacuous_cylinder_nonvacuous j)
    simpa [Finset.mul_sum] using h
  have hsum₀ : (∑ j, (D₀.cylinder j).cost) ≤ C₀.cost := by
    rw [← C₀.removeVacuous_cost]
    exact cylinderCostSum_le_cost D₀
  have hsum₁ : (∑ j, (D₁.cylinder j).cost) ≤ C₁.cost := by
    rw [← C₁.removeVacuous_cost]
    exact cylinderCostSum_le_cost D₁
  dsimp only [D₀, D₁] at hlin hslope hlift₀ hlift₁ hsum₀ hsum₁
  unfold NegativeSplitData.cost NegativeSplitData.changedLinearSupport
    negativeSplitDataOfCertificates
  dsimp only
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  omega

theorem splitAffineCylinderCost_le_oriented_zero
    (f₀ f₁ : (Fin m → Bool) → Bool) :
    splitAffineCylinderCost f₀ f₁ ≤
      1 + m + 3 * AffineCylinderThresholdCertificate.minimumCost f₀ +
        2 * AffineCylinderThresholdCertificate.minimumCost f₁ := by
  obtain ⟨C₀, hC₀⟩ :=
    AffineCylinderThresholdCertificate.minimumCost_spec f₀
  obtain ⟨C₁, hC₁⟩ :=
    AffineCylinderThresholdCertificate.minimumCost_spec f₁
  calc
    _ ≤ (positiveSplitDataOfCertificates C₀ C₁).cost :=
      splitAffineCylinderCost_le_positive _
    _ ≤ 1 + m + 3 * C₀.cost + 2 * C₁.cost :=
      positive_generated_cost_le C₀ C₁
    _ = _ := by rw [hC₀, hC₁]

theorem splitAffineCylinderCost_le_oriented_one
    (f₀ f₁ : (Fin m → Bool) → Bool) :
    splitAffineCylinderCost f₀ f₁ ≤
      1 + m + 2 * AffineCylinderThresholdCertificate.minimumCost f₀ +
        3 * AffineCylinderThresholdCertificate.minimumCost f₁ := by
  obtain ⟨C₀, hC₀⟩ :=
    AffineCylinderThresholdCertificate.minimumCost_spec f₀
  obtain ⟨C₁, hC₁⟩ :=
    AffineCylinderThresholdCertificate.minimumCost_spec f₁
  calc
    _ ≤ (negativeSplitDataOfCertificates C₀ C₁).cost :=
      splitAffineCylinderCost_le_negative _
    _ ≤ 1 + m + 2 * C₀.cost + 3 * C₁.cost :=
      negative_generated_cost_le C₀ C₁
    _ = _ := by rw [hC₀, hC₁]

/-- The affine-cylinder Shannon recursion, with the better cofactor chosen as
the shared base block. -/
theorem splitAffineCylinderCost_le_cofactorRecursion
    (f₀ f₁ : (Fin m → Bool) → Bool) :
    splitAffineCylinderCost f₀ f₁ ≤
      1 + m + 2 *
          (AffineCylinderThresholdCertificate.minimumCost f₀ +
            AffineCylinderThresholdCertificate.minimumCost f₁) +
        min (AffineCylinderThresholdCertificate.minimumCost f₀)
          (AffineCylinderThresholdCertificate.minimumCost f₁) := by
  by_cases h : AffineCylinderThresholdCertificate.minimumCost f₀ ≤
      AffineCylinderThresholdCertificate.minimumCost f₁
  · rw [Nat.min_eq_left h]
    convert splitAffineCylinderCost_le_oriented_zero f₀ f₁ using 1 <;>
      omega
  · have h' := Nat.le_of_not_ge h
    rw [Nat.min_eq_right h']
    convert splitAffineCylinderCost_le_oriented_one f₀ f₁ using 1 <;>
      omega

theorem affineCylinder_cofactor_recursion
    (f₀ f₁ : (Fin m → Bool) → Bool) :
    HStar (m + 1) (joinCofactors f₀ f₁) ≤
        AffineCylinderThresholdCertificate.minimumCost
          (joinCofactors f₀ f₁) ∧
      AffineCylinderThresholdCertificate.minimumCost
          (joinCofactors f₀ f₁) ≤
        splitAffineCylinderCost f₀ f₁ ∧
      splitAffineCylinderCost f₀ f₁ ≤
        1 + m + 2 *
            (AffineCylinderThresholdCertificate.minimumCost f₀ +
              AffineCylinderThresholdCertificate.minimumCost f₁) +
          min (AffineCylinderThresholdCertificate.minimumCost f₀)
            (AffineCylinderThresholdCertificate.minimumCost f₁) := by
  exact ⟨AffineCylinderThresholdCertificate.HStar_le_minimumCost _,
    actc_join_le_splitAffineCylinderCost f₀ f₁,
    splitAffineCylinderCost_le_cofactorRecursion f₀ f₁⟩

/-! ## Global coordinate-minimized split cost -/

/-- Canonical permutation which moves coordinate `j` into the first
position.  The swap is its own inverse. -/
def splitCoordinatePermutation (j : Fin (m + 1)) :
    Equiv.Perm (Fin (m + 1)) :=
  Equiv.swap 0 j

/-- Relabel a function so that coordinate `j` becomes the first coordinate. -/
def relabelForSplit (f : (Fin (m + 1) → Bool) → Bool)
    (j : Fin (m + 1)) : (Fin (m + 1) → Bool) → Bool :=
  fun x ↦ f (permuteBits (splitCoordinatePermutation j) x)

/-- Canonical `b`-cofactor obtained after moving coordinate `j` first. -/
def coordinateCofactor (f : (Fin (m + 1) → Bool) → Bool)
    (j : Fin (m + 1)) (b : Bool) : (Fin m → Bool) → Bool :=
  fun y ↦ relabelForSplit f j (consBit b y)

theorem join_coordinateCofactors
    (f : (Fin (m + 1) → Bool) → Bool) (j : Fin (m + 1)) :
    joinCofactors (coordinateCofactor f j false)
        (coordinateCofactor f j true) = relabelForSplit f j := by
  funext x
  rw [← consBit_head_tail x]
  cases x 0 <;> simp [joinCofactors, coordinateCofactor]

/-- A natural number is attained as the fixed-coordinate split cost of `f`. -/
def GlobalSplitAffineCylinderCostValue
    (f : (Fin (m + 1) → Bool) → Bool) (K : ℕ) : Prop :=
  ∃ j : Fin (m + 1),
    splitAffineCylinderCost (coordinateCofactor f j false)
      (coordinateCofactor f j true) = K

theorem exists_globalSplitAffineCylinderCostValue
    (f : (Fin (m + 1) → Bool) → Bool) :
    ∃ K, GlobalSplitAffineCylinderCostValue f K := by
  let j : Fin (m + 1) := 0
  exact ⟨splitAffineCylinderCost (coordinateCofactor f j false)
    (coordinateCofactor f j true), j, rfl⟩

/-- Split affine-cylinder cost minimized over every input coordinate. -/
noncomputable def globalSplitAffineCylinderCost
    (f : (Fin (m + 1) → Bool) → Bool) : ℕ :=
  Nat.find (exists_globalSplitAffineCylinderCostValue f)

theorem globalSplitAffineCylinderCost_spec
    (f : (Fin (m + 1) → Bool) → Bool) :
    GlobalSplitAffineCylinderCostValue f
      (globalSplitAffineCylinderCost f) :=
  Nat.find_spec (exists_globalSplitAffineCylinderCostValue f)

theorem globalSplitAffineCylinderCost_le_coordinate
    (f : (Fin (m + 1) → Bool) → Bool) (j : Fin (m + 1)) :
    globalSplitAffineCylinderCost f ≤
      splitAffineCylinderCost (coordinateCofactor f j false)
        (coordinateCofactor f j true) :=
  Nat.find_min' (exists_globalSplitAffineCylinderCostValue f) ⟨j, rfl⟩

theorem actc_le_coordinateSplitAffineCylinderCost
    (f : (Fin (m + 1) → Bool) → Bool) (j : Fin (m + 1)) :
    AffineCylinderThresholdCertificate.minimumCost f ≤
      splitAffineCylinderCost (coordinateCofactor f j false)
        (coordinateCofactor f j true) := by
  have h := actc_join_le_splitAffineCylinderCost
    (coordinateCofactor f j false) (coordinateCofactor f j true)
  rw [join_coordinateCofactors] at h
  have hperm := AffineCylinderThresholdCertificate.minimumCost_permute
    (splitCoordinatePermutation j) f
  change AffineCylinderThresholdCertificate.minimumCost (relabelForSplit f j) =
    AffineCylinderThresholdCertificate.minimumCost f at hperm
  rwa [hperm] at h

theorem actc_le_globalSplitAffineCylinderCost
    (f : (Fin (m + 1) → Bool) → Bool) :
    AffineCylinderThresholdCertificate.minimumCost f ≤
      globalSplitAffineCylinderCost f := by
  obtain ⟨j, hj⟩ := globalSplitAffineCylinderCost_spec f
  rw [← hj]
  exact actc_le_coordinateSplitAffineCylinderCost f j

theorem HStar_le_globalSplitAffineCylinderCost
    (f : (Fin (m + 1) → Bool) → Bool) :
    HStar (m + 1) f ≤ globalSplitAffineCylinderCost f :=
  (AffineCylinderThresholdCertificate.HStar_le_minimumCost f).trans
    (actc_le_globalSplitAffineCylinderCost f)

/-- The global split cost obeys the cofactor recursion at every chosen
coordinate. -/
theorem globalSplitAffineCylinderCost_le_coordinateRecursion
    (f : (Fin (m + 1) → Bool) → Bool) (j : Fin (m + 1)) :
    globalSplitAffineCylinderCost f ≤
      1 + m + 2 *
          (AffineCylinderThresholdCertificate.minimumCost
              (coordinateCofactor f j false) +
            AffineCylinderThresholdCertificate.minimumCost
              (coordinateCofactor f j true)) +
        min (AffineCylinderThresholdCertificate.minimumCost
              (coordinateCofactor f j false))
          (AffineCylinderThresholdCertificate.minimumCost
            (coordinateCofactor f j true)) := by
  exact (globalSplitAffineCylinderCost_le_coordinate f j).trans
    (splitAffineCylinderCost_le_cofactorRecursion
      (coordinateCofactor f j false) (coordinateCofactor f j true))

/-- Literal global form of the affine-cylinder cofactor recursion, valid at
any selected coordinate. -/
theorem global_affineCylinder_cofactor_recursion
    (f : (Fin (m + 1) → Bool) → Bool) (j : Fin (m + 1)) :
    HStar (m + 1) f ≤
        AffineCylinderThresholdCertificate.minimumCost f ∧
      AffineCylinderThresholdCertificate.minimumCost f ≤
        globalSplitAffineCylinderCost f ∧
      globalSplitAffineCylinderCost f ≤
        1 + m + 2 *
            (AffineCylinderThresholdCertificate.minimumCost
                (coordinateCofactor f j false) +
              AffineCylinderThresholdCertificate.minimumCost
                (coordinateCofactor f j true)) +
          min (AffineCylinderThresholdCertificate.minimumCost
                (coordinateCofactor f j false))
            (AffineCylinderThresholdCertificate.minimumCost
              (coordinateCofactor f j true)) := by
  exact ⟨AffineCylinderThresholdCertificate.HStar_le_minimumCost f,
    actc_le_globalSplitAffineCylinderCost f,
    globalSplitAffineCylinderCost_le_coordinateRecursion f j⟩

end HeadComplexity
