import HeadComplexity.Results.AffineCylinderCofactorRecursion

set_option linter.style.header false

/-!
# Split affine-cylinder refinement of split affine-free support

Positive monomials are cylinders of local cost one.  This module aligns the
nonlinear coefficients of two strict cofactor polynomials and proves that the
resulting split affine-cylinder presentation has exactly the split
affine-free support cost.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

noncomputable local instance splitAffineRefinementPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {m : ℕ}

/-- Nonlinear coefficients which change between two squarefree polynomials. -/
noncomputable def nonlinearDifferenceSupport
    (P₀ P₁ : SquarefreePolynomial m) : Finset (Finset (Fin m)) :=
  Finset.univ.filter fun S ↦
    2 ≤ S.card ∧ P₁.coeff S ≠ P₀.coeff S

/-- Linear coefficients which change across the split. -/
noncomputable def polynomialChangedLinearSupport
    (P₀ P₁ : SquarefreePolynomial m) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ P₁.coeff {i} ≠ P₀.coeff {i}

/-- The split affine-free cost of a fixed pair of strict cofactor
polynomials. -/
noncomputable def splitAffineFreePairCost
    (P₀ P₁ : SquarefreePolynomial m) : ℕ :=
  (if P₁.coeff ∅ ≠ P₀.coeff ∅ ∨
      ∃ i, P₀.coeff {i} ≠ 0 then 1 else 0) +
    P₀.nonlinearSupport.card +
    (polynomialChangedLinearSupport P₀ P₁).card +
    (nonlinearDifferenceSupport P₀ P₁).card

private noncomputable def nonlinearSets : Finset (Finset (Fin m)) :=
  Finset.univ.filter fun S ↦ 2 ≤ S.card

private theorem nonlinearSupport_sum_eq_all
    (P : SquarefreePolynomial m) (y : Fin m → Bool) :
    (∑ S ∈ P.nonlinearSupport,
        P.coeff S * squarefreeMonomial S y) =
      ∑ S ∈ (nonlinearSets : Finset (Finset (Fin m))),
        P.coeff S * squarefreeMonomial S y := by
  apply Finset.sum_subset
  · intro S hS
    simp only [SquarefreePolynomial.nonlinearSupport, nonlinearSets,
      Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    exact hS.1
  · intro S hS hnot
    simp only [nonlinearSets, Finset.mem_filter, Finset.mem_univ,
      true_and] at hS
    have hz : P.coeff S = 0 := by
      by_contra hnz
      exact hnot (by
        simp [SquarefreePolynomial.nonlinearSupport, hS, hnz])
    simp [hz]

private theorem differenceSupport_sum_eq_all
    (P₀ P₁ : SquarefreePolynomial m) (y : Fin m → Bool) :
    (∑ S ∈ nonlinearDifferenceSupport P₀ P₁,
        (P₁.coeff S - P₀.coeff S) * squarefreeMonomial S y) =
      ∑ S ∈ (nonlinearSets : Finset (Finset (Fin m))),
        (P₁.coeff S - P₀.coeff S) * squarefreeMonomial S y := by
  apply Finset.sum_subset
  · intro S hS
    simp only [nonlinearDifferenceSupport, nonlinearSets,
      Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    exact hS.1
  · intro S hS hnot
    simp only [nonlinearSets, Finset.mem_filter, Finset.mem_univ,
      true_and] at hS
    have heq : P₁.coeff S = P₀.coeff S := by
      by_contra hne
      exact hnot (by simp [nonlinearDifferenceSupport, hS, hne])
    simp [heq]

private theorem nonlinear_sum_add_difference
    (P₀ P₁ : SquarefreePolynomial m) (y : Fin m → Bool) :
    (∑ S ∈ P₀.nonlinearSupport,
        P₀.coeff S * squarefreeMonomial S y) +
      (∑ S ∈ nonlinearDifferenceSupport P₀ P₁,
        (P₁.coeff S - P₀.coeff S) * squarefreeMonomial S y) =
      ∑ S ∈ P₁.nonlinearSupport,
        P₁.coeff S * squarefreeMonomial S y := by
  rw [nonlinearSupport_sum_eq_all, differenceSupport_sum_eq_all,
    nonlinearSupport_sum_eq_all]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

private theorem splitPolynomialIndicator_eq
    (P₀ P₁ : SquarefreePolynomial m) :
    (if ∃ i, splitAffineCoeff (P₀.coeff ∅) (P₁.coeff ∅)
          (fun j ↦ P₀.coeff {j}) i ≠ 0 then 1 else 0) =
      if P₁.coeff ∅ ≠ P₀.coeff ∅ ∨
        ∃ i, P₀.coeff {i} ≠ 0 then 1 else 0 := by
  have hex :
      (∃ i, splitAffineCoeff (P₀.coeff ∅) (P₁.coeff ∅)
          (fun j ↦ P₀.coeff {j}) i ≠ 0) ↔
        P₁.coeff ∅ ≠ P₀.coeff ∅ ∨
          ∃ i, P₀.coeff {i} ≠ 0 := by
    constructor
    · rintro ⟨i, hi⟩
      induction i using Fin.cases with
      | zero =>
        left
        exact sub_ne_zero.mp (by simpa [splitAffineCoeff] using hi)
      | succ j =>
        right
        exact ⟨j, by simpa [splitAffineCoeff] using hi⟩
    · rintro (hconst | ⟨i, hi⟩)
      · exact ⟨0, by simpa [splitAffineCoeff] using sub_ne_zero.mpr hconst⟩
      · exact ⟨i.succ, by simpa [splitAffineCoeff] using hi⟩
  by_cases h : ∃ i, splitAffineCoeff (P₀.coeff ∅) (P₁.coeff ∅)
      (fun j ↦ P₀.coeff {j}) i ≠ 0
  · rw [if_pos h, if_pos (hex.mp h)]
  · rw [if_neg h, if_neg (fun h' ↦ h (hex.mpr h'))]

private theorem liftedPositiveMonomial_cost
    (S : Finset (Fin m)) :
    (CubeCylinder.positiveMonomial S).liftPositiveFresh.cost = 1 := by
  unfold CubeCylinder.liftPositiveFresh CubeCylinder.positiveMonomial
    CubeCylinder.cost
  simp
  exact Nat.one_le_pow _ 2 (by omega)

/-- The positive-monomial split presentation associated to two strict
cofactor polynomials. -/
noncomputable def splitDataOfSquarefreePair
    {f₀ f₁ : (Fin m → Bool) → Bool}
    (P₀ P₁ : SquarefreePolynomial m)
    (hP₀ : P₀.StrictSignRepresents f₀)
    (hP₁ : P₁.StrictSignRepresents f₁) :
    PositiveSplitData f₀ f₁ := by
  let C₀ := AffineCylinderThresholdCertificate.ofSquarefreePolynomial P₀ hP₀
  let supportAtΔ : Fin (nonlinearDifferenceSupport P₀ P₁).card →
      Finset (Fin m) := fun j ↦
    (((nonlinearDifferenceSupport P₀ P₁).equivFin).symm j).1
  refine
    { affineConst₀ := P₀.coeff ∅
      affineCoeff₀ := fun i ↦ P₀.coeff {i}
      affineConst₁ := P₁.coeff ∅
      affineCoeff₁ := fun i ↦ P₁.coeff {i}
      baseCount := C₀.termCount
      baseCylinder := C₀.cylinder
      baseCoefficient := C₀.coefficient
      baseCoefficient_ne_zero := C₀.coefficient_ne_zero
      baseCylinder_nonvacuous := ?_
      changeCount := (nonlinearDifferenceSupport P₀ P₁).card
      changeCylinder := fun j ↦
        CubeCylinder.positiveMonomial (supportAtΔ j)
      changeCoefficient := fun j ↦
        P₁.coeff (supportAtΔ j) - P₀.coeff (supportAtΔ j)
      changeCoefficient_ne_zero := ?_
      changeCylinder_nonvacuous := ?_
      represents₀ := C₀.represents
      represents₁ := ?_ }
  · intro j
    unfold C₀ AffineCylinderThresholdCertificate.ofSquarefreePolynomial
    dsimp only
    have hj := ((P₀.nonlinearSupport.equivFin).symm j).2
    have hcard : 2 ≤ ((P₀.nonlinearSupport.equivFin).symm j).1.card :=
      (Finset.mem_filter.mp hj).2.1
    simp only [CubeCylinder.positiveMonomial, not_and_or]
    left
    exact (Finset.card_pos.mp (lt_of_lt_of_le (by omega) hcard)).ne_empty
  · intro j
    have hj := (((nonlinearDifferenceSupport P₀ P₁).equivFin).symm j).2
    simp only [nonlinearDifferenceSupport, Finset.mem_filter,
      Finset.mem_univ, true_and] at hj
    exact sub_ne_zero.mpr hj.2
  · intro j
    have hj := (((nonlinearDifferenceSupport P₀ P₁).equivFin).symm j).2
    have hcard : 2 ≤
        (((nonlinearDifferenceSupport P₀ P₁).equivFin).symm j).1.card :=
      (Finset.mem_filter.mp hj).2.1
    simp only [CubeCylinder.positiveMonomial, not_and_or]
    left
    dsimp only [supportAtΔ]
    exact (Finset.card_pos.mp (lt_of_lt_of_le (by omega) hcard)).ne_empty
  · intro y
    have hbase :
        (∑ j : Fin P₀.nonlinearSupport.card,
          P₀.coeff ((P₀.nonlinearSupport.equivFin).symm j).1 *
            squarefreeMonomial
              ((P₀.nonlinearSupport.equivFin).symm j).1 y) =
          ∑ S ∈ P₀.nonlinearSupport,
            P₀.coeff S * squarefreeMonomial S y := by
      rw [← P₀.nonlinearSupport.sum_attach, Finset.attach_eq_univ,
        ← P₀.nonlinearSupport.equivFin.symm.sum_comp]
    have hchange :
        (∑ j : Fin (nonlinearDifferenceSupport P₀ P₁).card,
          (P₁.coeff (supportAtΔ j) - P₀.coeff (supportAtΔ j)) *
            squarefreeMonomial (supportAtΔ j) y) =
          ∑ S ∈ nonlinearDifferenceSupport P₀ P₁,
            (P₁.coeff S - P₀.coeff S) * squarefreeMonomial S y := by
      dsimp [supportAtΔ]
      rw [← (nonlinearDifferenceSupport P₀ P₁).sum_attach,
        Finset.attach_eq_univ,
        ← (nonlinearDifferenceSupport P₀ P₁).equivFin.symm.sum_comp]
    change ((0 < affineValue (P₁.coeff ∅) (fun i ↦ P₁.coeff {i}) y +
        (∑ j : Fin P₀.nonlinearSupport.card,
          P₀.coeff ((P₀.nonlinearSupport.equivFin).symm j).1 *
            (CubeCylinder.positiveMonomial
              ((P₀.nonlinearSupport.equivFin).symm j).1).eval y) +
        (∑ j : Fin (nonlinearDifferenceSupport P₀ P₁).card,
          (P₁.coeff (supportAtΔ j) - P₀.coeff (supportAtΔ j)) *
            (CubeCylinder.positiveMonomial (supportAtΔ j)).eval y) ↔
          f₁ y = true) ∧
        affineValue (P₁.coeff ∅) (fun i ↦ P₁.coeff {i}) y +
          (∑ j : Fin P₀.nonlinearSupport.card,
            P₀.coeff ((P₀.nonlinearSupport.equivFin).symm j).1 *
              (CubeCylinder.positiveMonomial
                ((P₀.nonlinearSupport.equivFin).symm j).1).eval y) +
          (∑ j : Fin (nonlinearDifferenceSupport P₀ P₁).card,
            (P₁.coeff (supportAtΔ j) - P₀.coeff (supportAtΔ j)) *
              (CubeCylinder.positiveMonomial (supportAtΔ j)).eval y) ≠ 0)
    simp_rw [CubeCylinder.eval_positiveMonomial]
    rw [hbase, hchange]
    have hnonlinear := nonlinear_sum_add_difference P₀ P₁ y
    have hscore :
        affineValue (P₁.coeff ∅) (fun i ↦ P₁.coeff {i}) y +
            (∑ S ∈ P₀.nonlinearSupport,
              P₀.coeff S * squarefreeMonomial S y) +
            (∑ S ∈ nonlinearDifferenceSupport P₀ P₁,
              (P₁.coeff S - P₀.coeff S) * squarefreeMonomial S y) =
          affineValue (P₁.coeff ∅) (fun i ↦ P₁.coeff {i}) y +
            ∑ S ∈ P₁.nonlinearSupport,
              P₁.coeff S * squarefreeMonomial S y := by
      rw [add_assoc, hnonlinear]
    rw [hscore]
    have heval :
        affineValue (P₁.coeff ∅) (fun i ↦ P₁.coeff {i}) y +
            ∑ S ∈ P₁.nonlinearSupport,
              P₁.coeff S * squarefreeMonomial S y = P₁.eval y := by
      simp [SquarefreePolynomial.eval, affineValue]
    rw [heval]
    exact hP₁ y

theorem splitDataOfSquarefreePair_cost
    {f₀ f₁ : (Fin m → Bool) → Bool}
    (P₀ P₁ : SquarefreePolynomial m)
    (hP₀ : P₀.StrictSignRepresents f₀)
    (hP₁ : P₁.StrictSignRepresents f₁) :
    (splitDataOfSquarefreePair P₀ P₁ hP₀ hP₁).cost =
      splitAffineFreePairCost P₀ P₁ := by
  unfold PositiveSplitData.cost PositiveSplitData.changedLinearSupport
    splitDataOfSquarefreePair splitAffineFreePairCost
  dsimp only
  rw [splitPolynomialIndicator_eq]
  change
    (if P₁.coeff ∅ ≠ P₀.coeff ∅ ∨ ∃ i, P₀.coeff {i} ≠ 0
      then 1 else 0) +
        (Finset.univ.filter fun i ↦
          P₁.coeff {i} ≠ P₀.coeff {i}).card +
        (∑ j : Fin P₀.nonlinearSupport.card,
          (CubeCylinder.positiveMonomial
            ((P₀.nonlinearSupport.equivFin).symm j).1).cost) +
        (∑ j : Fin (nonlinearDifferenceSupport P₀ P₁).card,
          (CubeCylinder.positiveMonomial
            (((nonlinearDifferenceSupport P₀ P₁).equivFin).symm j).1
              ).liftPositiveFresh.cost) =
      (if P₁.coeff ∅ ≠ P₀.coeff ∅ ∨ ∃ i, P₀.coeff {i} ≠ 0
        then 1 else 0) + P₀.nonlinearSupport.card +
        (polynomialChangedLinearSupport P₀ P₁).card +
        (nonlinearDifferenceSupport P₀ P₁).card
  have hbase :
      (∑ j : Fin P₀.nonlinearSupport.card,
        (CubeCylinder.positiveMonomial
          ((P₀.nonlinearSupport.equivFin).symm j).1).cost) =
        P₀.nonlinearSupport.card := by
    calc
      _ = ∑ _j : Fin P₀.nonlinearSupport.card, 1 := by
        apply Finset.sum_congr rfl
        intro j _
        apply CubeCylinder.cost_positiveMonomial
        have hj := ((P₀.nonlinearSupport.equivFin).symm j).2
        simp only [SquarefreePolynomial.nonlinearSupport, Finset.mem_filter,
          Finset.mem_univ, true_and] at hj
        exact Finset.card_pos.mp (lt_of_lt_of_le (by omega) hj.1)
      _ = P₀.nonlinearSupport.card := by simp
  have hchange :
      (∑ j : Fin (nonlinearDifferenceSupport P₀ P₁).card,
        (CubeCylinder.positiveMonomial
          (((nonlinearDifferenceSupport P₀ P₁).equivFin).symm j).1
            ).liftPositiveFresh.cost) =
        (nonlinearDifferenceSupport P₀ P₁).card := by
    simp_rw [liftedPositiveMonomial_cost]
    simp
  rw [hbase, hchange]
  unfold polynomialChangedLinearSupport
  omega

def SplitAffineFreeCostValue
    (f₀ f₁ : (Fin m → Bool) → Bool) (K : ℕ) : Prop :=
  ∃ P₀ P₁ : SquarefreePolynomial m,
    P₀.StrictSignRepresents f₀ ∧ P₁.StrictSignRepresents f₁ ∧
      splitAffineFreePairCost P₀ P₁ = K

theorem exists_splitAffineFreeCostValue
    (f₀ f₁ : (Fin m → Bool) → Bool) :
    ∃ K, SplitAffineFreeCostValue f₀ f₁ K := by
  obtain ⟨P₀, _, hP₀⟩ :=
    SquarefreePolynomial.exists_squarefree_strictSignRep_of_ThresholdDegLE
      (thresholdDeg_spec f₀)
  obtain ⟨P₁, _, hP₁⟩ :=
    SquarefreePolynomial.exists_squarefree_strictSignRep_of_ThresholdDegLE
      (thresholdDeg_spec f₁)
  exact ⟨splitAffineFreePairCost P₀ P₁, P₀, P₁, hP₀, hP₁, rfl⟩

/-- Minimum first-coordinate split affine-free support cost. -/
noncomputable def splitAffineFreeCost
    (f₀ f₁ : (Fin m → Bool) → Bool) : ℕ :=
  Nat.find (exists_splitAffineFreeCostValue f₀ f₁)

theorem splitAffineFreeCost_spec
    (f₀ f₁ : (Fin m → Bool) → Bool) :
    SplitAffineFreeCostValue f₀ f₁ (splitAffineFreeCost f₀ f₁) :=
  Nat.find_spec (exists_splitAffineFreeCostValue f₀ f₁)

/-- Split affine-cylinder cost refines split affine-free support cost. -/
theorem splitAffineCylinderCost_le_splitAffineFreeCost
    (f₀ f₁ : (Fin m → Bool) → Bool) :
    splitAffineCylinderCost f₀ f₁ ≤ splitAffineFreeCost f₀ f₁ := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hcost⟩ :=
    splitAffineFreeCost_spec f₀ f₁
  calc
    splitAffineCylinderCost f₀ f₁ ≤
        (splitDataOfSquarefreePair P₀ P₁ hP₀ hP₁).cost :=
      splitAffineCylinderCost_le_positive _
    _ = splitAffineFreePairCost P₀ P₁ :=
      splitDataOfSquarefreePair_cost P₀ P₁ hP₀ hP₁
    _ = splitAffineFreeCost f₀ f₁ := hcost

theorem split_affine_cylinder_refinement
    (f₀ f₁ : (Fin m → Bool) → Bool) :
    HStar (m + 1) (joinCofactors f₀ f₁) ≤
        AffineCylinderThresholdCertificate.minimumCost
          (joinCofactors f₀ f₁) ∧
      AffineCylinderThresholdCertificate.minimumCost
          (joinCofactors f₀ f₁) ≤
        splitAffineCylinderCost f₀ f₁ ∧
      splitAffineCylinderCost f₀ f₁ ≤ splitAffineFreeCost f₀ f₁ := by
  exact ⟨AffineCylinderThresholdCertificate.HStar_le_minimumCost _,
    actc_join_le_splitAffineCylinderCost f₀ f₁,
    splitAffineCylinderCost_le_splitAffineFreeCost f₀ f₁⟩

/-! ## Global coordinate-minimized refinement -/

/-- A natural number is attained as the split affine-free cost at one input
coordinate. -/
def GlobalSplitAffineFreeCostValue
    (f : (Fin (m + 1) → Bool) → Bool) (K : ℕ) : Prop :=
  ∃ j : Fin (m + 1),
    splitAffineFreeCost (coordinateCofactor f j false)
      (coordinateCofactor f j true) = K

theorem exists_globalSplitAffineFreeCostValue
    (f : (Fin (m + 1) → Bool) → Bool) :
    ∃ K, GlobalSplitAffineFreeCostValue f K := by
  let j : Fin (m + 1) := 0
  exact ⟨splitAffineFreeCost (coordinateCofactor f j false)
    (coordinateCofactor f j true), j, rfl⟩

/-- Split affine-free support cost minimized over every input coordinate. -/
noncomputable def globalSplitAffineFreeCost
    (f : (Fin (m + 1) → Bool) → Bool) : ℕ :=
  Nat.find (exists_globalSplitAffineFreeCostValue f)

theorem globalSplitAffineFreeCost_spec
    (f : (Fin (m + 1) → Bool) → Bool) :
    GlobalSplitAffineFreeCostValue f (globalSplitAffineFreeCost f) :=
  Nat.find_spec (exists_globalSplitAffineFreeCostValue f)

theorem globalSplitAffineFreeCost_le_coordinate
    (f : (Fin (m + 1) → Bool) → Bool) (j : Fin (m + 1)) :
    globalSplitAffineFreeCost f ≤
      splitAffineFreeCost (coordinateCofactor f j false)
        (coordinateCofactor f j true) :=
  Nat.find_min' (exists_globalSplitAffineFreeCostValue f) ⟨j, rfl⟩

theorem globalSplitAffineCylinderCost_le_globalSplitAffineFreeCost
    (f : (Fin (m + 1) → Bool) → Bool) :
    globalSplitAffineCylinderCost f ≤ globalSplitAffineFreeCost f := by
  obtain ⟨j, hj⟩ := globalSplitAffineFreeCost_spec f
  calc
    globalSplitAffineCylinderCost f ≤
        splitAffineCylinderCost (coordinateCofactor f j false)
          (coordinateCofactor f j true) :=
      globalSplitAffineCylinderCost_le_coordinate f j
    _ ≤ splitAffineFreeCost (coordinateCofactor f j false)
        (coordinateCofactor f j true) :=
      splitAffineCylinderCost_le_splitAffineFreeCost _ _
    _ = globalSplitAffineFreeCost f := hj

/-- Literal global theorem 114 chain, with both split invariants minimized
over all input coordinates. -/
theorem global_split_affine_cylinder_refinement
    (f : (Fin (m + 1) → Bool) → Bool) :
    HStar (m + 1) f ≤
        AffineCylinderThresholdCertificate.minimumCost f ∧
      AffineCylinderThresholdCertificate.minimumCost f ≤
        globalSplitAffineCylinderCost f ∧
      globalSplitAffineCylinderCost f ≤ globalSplitAffineFreeCost f := by
  exact ⟨AffineCylinderThresholdCertificate.HStar_le_minimumCost f,
    actc_le_globalSplitAffineCylinderCost f,
    globalSplitAffineCylinderCost_le_globalSplitAffineFreeCost f⟩

end HeadComplexity
