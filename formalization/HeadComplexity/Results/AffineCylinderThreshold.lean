import HeadComplexity.Atoms.CylinderApproximation
import HeadComplexity.Results.AffineFreeSparsity
import HeadComplexity.Results.ThresholdDegree

set_option linter.style.header false

/-!
# Affine-cylinder threshold cost

This module formalizes finite cylinder and affine-cylinder threshold
certificates, their attained minimum costs, and their compilation to fractional
heads.  It also compares affine-cylinder cost with cylinder cost and
affine-free polynomial-threshold sparsity.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

noncomputable local instance (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {n : ℕ} {f : (Fin n → Bool) → Bool}

/-- A finite strict threshold of Boolean cylinders. -/
structure CylinderThresholdCertificate (n : ℕ)
    (f : (Fin n → Bool) → Bool) where
  bias : ℝ
  termCount : ℕ
  cylinder : Fin termCount → CubeCylinder n
  coefficient : Fin termCount → ℝ
  coefficient_ne_zero : ∀ j, coefficient j ≠ 0
  represents : StrictSignRepresentsScore
    (fun bits ↦ bias + ∑ j, coefficient j * (cylinder j).eval bits) f

namespace CylinderThresholdCertificate

/-- Sum of the raw-calibration costs of the active cylinders. -/
def cost (C : CylinderThresholdCertificate n f) : ℕ :=
  ∑ j, (C.cylinder j).cost

/-- The signed truth-table coefficient used in the universal point-cylinder
certificate. -/
private def truthCoefficient (f : (Fin n → Bool) → Bool)
    (bits : Fin n → Bool) : ℝ :=
  if f bits then 1 else -1

/-- Every Boolean function has a faithful finite cylinder-threshold
certificate, obtained from its point cylinders. -/
noncomputable def pointCertificate (f : (Fin n → Bool) → Bool) :
    CylinderThresholdCertificate n f := by
  classical
  let e : (Fin n → Bool) ≃ Fin (Fintype.card (Fin n → Bool)) :=
    Fintype.equivFin _
  refine
    { bias := 0
      termCount := Fintype.card (Fin n → Bool)
      cylinder := fun j ↦ CubeCylinder.point (e.symm j)
      coefficient := fun j ↦ truthCoefficient f (e.symm j)
      coefficient_ne_zero := fun j ↦ by
        unfold truthCoefficient
        split <;> norm_num
      represents := ?_ }
  intro bits
  have hsum :
      (∑ j : Fin (Fintype.card (Fin n → Bool)),
          truthCoefficient f (e.symm j) *
            (CubeCylinder.point (e.symm j)).eval bits) =
        truthCoefficient f bits := by
    calc
      (∑ j : Fin (Fintype.card (Fin n → Bool)),
          truthCoefficient f (e.symm j) *
            (CubeCylinder.point (e.symm j)).eval bits) =
          ∑ target : (Fin n → Bool),
            truthCoefficient f target * (CubeCylinder.point target).eval bits := by
              simpa using e.symm.sum_comp
                (fun target ↦ truthCoefficient f target *
                  (CubeCylinder.point target).eval bits)
      _ = truthCoefficient f bits := by
        simp [CubeCylinder.eval_point]
  simp only [zero_add, hsum]
  unfold truthCoefficient
  cases hfb : f bits <;> simp

/-- Existence of an attained finite cylinder-threshold cost. -/
theorem exists_cost (f : (Fin n → Bool) → Bool) :
    ∃ K, ∃ C : CylinderThresholdCertificate n f, C.cost = K :=
  ⟨(pointCertificate f).cost, pointCertificate f, rfl⟩

/-- Minimum cylinder-threshold cost. -/
noncomputable def minimumCost (f : (Fin n → Bool) → Bool) : ℕ :=
  Nat.find (exists_cost f)

/-- The minimum cylinder-threshold cost has a realizing certificate. -/
theorem minimumCost_spec (f : (Fin n → Bool) → Bool) :
    ∃ C : CylinderThresholdCertificate n f, C.cost = minimumCost f :=
  Nat.find_spec (exists_cost f)

/-- The minimum cylinder-threshold cost is no larger than any explicit
certificate cost. -/
theorem minimumCost_le (C : CylinderThresholdCertificate n f) :
    minimumCost f ≤ C.cost :=
  Nat.find_min' (exists_cost f) ⟨C, rfl⟩

end CylinderThresholdCertificate

/-- Short name for minimum cylinder-threshold cost. -/
noncomputable abbrev ctc (f : (Fin n → Bool) → Bool) : ℕ :=
  CylinderThresholdCertificate.minimumCost f

/-- A finite strict threshold with one free affine block and Boolean cylinder
terms. -/
structure AffineCylinderThresholdCertificate (n : ℕ)
    (f : (Fin n → Bool) → Bool) where
  affineConst : ℝ
  affineCoeff : Fin n → ℝ
  termCount : ℕ
  cylinder : Fin termCount → CubeCylinder n
  coefficient : Fin termCount → ℝ
  coefficient_ne_zero : ∀ j, coefficient j ≠ 0
  represents : StrictSignRepresentsScore
    (fun bits ↦ affineValue affineConst affineCoeff bits +
      ∑ j, coefficient j * (cylinder j).eval bits) f

namespace AffineCylinderThresholdCertificate

/-- Whether the affine block has a nonconstant part. -/
def HasLinearPart (C : AffineCylinderThresholdCertificate n f) : Prop :=
  ∃ i, C.affineCoeff i ≠ 0

/-- One head for a nonconstant affine block, plus the sum of cylinder costs. -/
noncomputable def cost (C : AffineCylinderThresholdCertificate n f) : ℕ :=
  (if C.HasLinearPart then 1 else 0) + ∑ j, (C.cylinder j).cost

/-- Component labels for flattening the affine block and the cylinder blocks. -/
abbrev Component (C : AffineCylinderThresholdCertificate n f) : Type :=
  Fin (if C.HasLinearPart then 1 else 0) ⊕ Fin C.termCount

/-- Number of fractional atoms assigned to a component. -/
abbrev atomCount (C : AffineCylinderThresholdCertificate n f)
    (j : C.Component) : ℕ :=
  match j with
  | Sum.inl _ => 1
  | Sum.inr t => (C.cylinder t).cost

/-- Atom indices belonging to a component. -/
abbrev AtomIndex (C : AffineCylinderThresholdCertificate n f)
    (j : C.Component) : Type :=
  Fin (C.atomCount j)

/-- Real score supplied by an affine or cylinder component. -/
noncomputable def componentScore (C : AffineCylinderThresholdCertificate n f)
    (j : C.Component) (bits : Fin n → Bool) : ℝ :=
  match j with
  | Sum.inl _ => affineValue 0 C.affineCoeff bits
  | Sum.inr t => C.coefficient t * (C.cylinder t).eval bits

theorem card_sigma_atomIndex (C : AffineCylinderThresholdCertificate n f) :
    Fintype.card (Sigma C.AtomIndex) = C.cost := by
  classical
  unfold cost
  rw [Fintype.card_sigma, Fintype.sum_sum_type]
  simp [AtomIndex, atomCount]

theorem affineConst_add_sum_componentScore
    (C : AffineCylinderThresholdCertificate n f) (bits : Fin n → Bool) :
    C.affineConst + ∑ j, C.componentScore j bits =
      affineValue C.affineConst C.affineCoeff bits +
        ∑ j, C.coefficient j * (C.cylinder j).eval bits := by
  classical
  have haffine :
      (∑ _a : Fin (if C.HasLinearPart then 1 else 0),
          affineValue 0 C.affineCoeff bits) =
        affineValue 0 C.affineCoeff bits := by
    by_cases hlin : C.HasLinearPart
    · simp [hlin]
    · have hzero : ∀ i, C.affineCoeff i = 0 := by
        intro i
        by_contra hi
        exact hlin ⟨i, hi⟩
      simp [hlin, affineValue, hzero]
  unfold componentScore
  rw [Fintype.sum_sum_type]
  change C.affineConst +
      ((∑ _a : Fin (if C.HasLinearPart then 1 else 0),
          affineValue 0 C.affineCoeff bits) +
        ∑ t, C.coefficient t * (C.cylinder t).eval bits) = _
  rw [haffine]
  unfold affineValue
  ring

theorem component_uniformlyAtomsApproximable
    (C : AffineCylinderThresholdCertificate n f) :
    ∀ j, UniformlyAtomsApproximable (C.AtomIndex j) (C.componentScore j) := by
  intro j
  cases j with
  | inl a =>
      change UniformlyAtomsApproximable (Fin 1)
        (affineValue 0 C.affineCoeff)
      exact UniformlyOneAtomApproximable.toUniformlyAtomsApproximable
        (uniformlyOneAtomApproximable_affineValue 0 C.affineCoeff)
  | inr t =>
      change UniformlyAtomsApproximable (Fin (C.cylinder t).cost)
        (fun bits ↦ C.coefficient t * (C.cylinder t).eval bits)
      exact (C.cylinder t).uniformlyAtomsApproximable (C.coefficient t)

/-- Every affine-cylinder threshold certificate compiles with exactly its
declared cost. -/
theorem computable (C : AffineCylinderThresholdCertificate n f) :
    computableWithHeadsN n C.cost f := by
  have hstrict : StrictSignRepresentsScore
      (fun bits ↦ C.affineConst + ∑ j, C.componentScore j bits) f := by
    intro bits
    change ((0 < C.affineConst + ∑ j, C.componentScore j bits ↔
      f bits = true) ∧ C.affineConst + ∑ j, C.componentScore j bits ≠ 0)
    rw [C.affineConst_add_sum_componentScore bits]
    exact C.represents bits
  have h := computableWithHeadsCard_of_uniformlyAtomsApproximable
    C.componentScore C.component_uniformlyAtomsApproximable
      C.affineConst hstrict
  rwa [C.card_sigma_atomIndex] at h

/-- A certificate cost upper-bounds minimum head complexity. -/
theorem HStar_le (C : AffineCylinderThresholdCertificate n f) :
    HStar n f ≤ C.cost :=
  HStar_le_of_computableWithHeadsN C.computable

/-- A cylinder-threshold certificate is an affine-cylinder certificate with a
constant affine part. -/
noncomputable def ofCylinder (C : CylinderThresholdCertificate n f) :
    AffineCylinderThresholdCertificate n f where
  affineConst := C.bias
  affineCoeff := 0
  termCount := C.termCount
  cylinder := C.cylinder
  coefficient := C.coefficient
  coefficient_ne_zero := C.coefficient_ne_zero
  represents := by
    simpa [affineValue] using C.represents

theorem cost_ofCylinder (C : CylinderThresholdCertificate n f) :
    (ofCylinder C).cost = C.cost := by
  unfold cost HasLinearPart ofCylinder CylinderThresholdCertificate.cost
  simp

/-- Every Boolean function has an affine-cylinder certificate. -/
theorem exists_cost (f : (Fin n → Bool) → Bool) :
    ∃ K, ∃ C : AffineCylinderThresholdCertificate n f, C.cost = K := by
  let C := ofCylinder (CylinderThresholdCertificate.pointCertificate f)
  exact ⟨C.cost, C, rfl⟩

/-- Minimum affine-cylinder threshold cost. -/
noncomputable def minimumCost (f : (Fin n → Bool) → Bool) : ℕ :=
  Nat.find (exists_cost f)

/-- The minimum affine-cylinder cost has a realizing certificate. -/
theorem minimumCost_spec (f : (Fin n → Bool) → Bool) :
    ∃ C : AffineCylinderThresholdCertificate n f, C.cost = minimumCost f :=
  Nat.find_spec (exists_cost f)

/-- Minimum affine-cylinder cost is no larger than any certificate cost. -/
theorem minimumCost_le (C : AffineCylinderThresholdCertificate n f) :
    minimumCost f ≤ C.cost :=
  Nat.find_min' (exists_cost f) ⟨C, rfl⟩

/-- Minimum head complexity is at most minimum affine-cylinder cost. -/
theorem HStar_le_minimumCost (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ minimumCost f := by
  obtain ⟨C, hC⟩ := minimumCost_spec f
  rw [← hC]
  exact C.HStar_le

/-- Minimum affine-cylinder cost is at most minimum cylinder-threshold cost. -/
theorem minimumCost_le_cylinderMinimumCost
    (f : (Fin n → Bool) → Bool) :
    minimumCost f ≤ CylinderThresholdCertificate.minimumCost f := by
  obtain ⟨C, hC⟩ := CylinderThresholdCertificate.minimumCost_spec f
  rw [← hC, ← cost_ofCylinder C]
  exact minimumCost_le (ofCylinder C)

/-- A strict squarefree sign polynomial becomes an affine-cylinder
certificate by viewing every nonlinear monomial as a positive cylinder. -/
noncomputable def ofSquarefreePolynomial
    (P : SquarefreePolynomial n) (hP : P.StrictSignRepresents f) :
    AffineCylinderThresholdCertificate n f := by
  classical
  let supportAt : Fin P.nonlinearSupport.card → Finset (Fin n) :=
    fun j ↦ ((P.nonlinearSupport.equivFin).symm j).1
  refine
    { affineConst := P.coeff ∅
      affineCoeff := fun i ↦ P.coeff {i}
      termCount := P.nonlinearSupport.card
      cylinder := fun j ↦ CubeCylinder.positiveMonomial (supportAt j)
      coefficient := fun j ↦ P.coeff (supportAt j)
      coefficient_ne_zero := fun j ↦ ?_
      represents := ?_ }
  · have hj := ((P.nonlinearSupport.equivFin).symm j).2
    simp only [SquarefreePolynomial.nonlinearSupport, Finset.mem_filter,
      Finset.mem_univ, true_and] at hj
    exact hj.2
  · intro bits
    have hsum :
        (∑ j : Fin P.nonlinearSupport.card,
          P.coeff (supportAt j) * squarefreeMonomial (supportAt j) bits) =
        ∑ S ∈ P.nonlinearSupport,
          P.coeff S * squarefreeMonomial S bits := by
      dsimp [supportAt]
      rw [← P.nonlinearSupport.sum_attach, Finset.attach_eq_univ,
        ← P.nonlinearSupport.equivFin.symm.sum_comp]
    simp only [CubeCylinder.eval_positiveMonomial, hsum]
    rw [show affineValue (P.coeff ∅) (fun i ↦ P.coeff {i}) bits =
        P.coeff ∅ + affineValue 0 (fun i ↦ P.coeff {i}) bits by
      unfold affineValue
      ring]
    exact hP bits

/-- The polynomial-to-cylinder translation preserves affine-free support
cost exactly. -/
theorem cost_ofSquarefreePolynomial
    (P : SquarefreePolynomial n) (hP : P.StrictSignRepresents f) :
    (ofSquarefreePolynomial P hP).cost = P.affineFreeSupportCost := by
  classical
  have hcost : ∀ j : Fin P.nonlinearSupport.card,
      ((ofSquarefreePolynomial P hP).cylinder j).cost = 1 := by
    intro j
    apply CubeCylinder.cost_positiveMonomial
    have hj := ((P.nonlinearSupport.equivFin).symm j).2
    simp only [SquarefreePolynomial.nonlinearSupport, Finset.mem_filter,
      Finset.mem_univ, true_and] at hj
    exact Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) hj.1)
  have hsumcost :
      (∑ j : Fin P.nonlinearSupport.card,
        ((ofSquarefreePolynomial P hP).cylinder j).cost) =
        P.nonlinearSupport.card := by
    calc
      (∑ j : Fin P.nonlinearSupport.card,
          ((ofSquarefreePolynomial P hP).cylinder j).cost) =
          ∑ _j : Fin P.nonlinearSupport.card, 1 :=
            Finset.sum_congr rfl fun j _ ↦ hcost j
      _ = P.nonlinearSupport.card := by simp
  have hlinear :
      (ofSquarefreePolynomial P hP).HasLinearPart ↔ P.HasLinearPart := by
    unfold HasLinearPart SquarefreePolynomial.HasLinearPart
      ofSquarefreePolynomial
    rfl
  rw [cost, hlinear]
  change (if P.HasLinearPart then 1 else 0) +
      (∑ j : Fin P.nonlinearSupport.card,
        ((ofSquarefreePolynomial P hP).cylinder j).cost) = _
  rw [hsumcost]
  unfold SquarefreePolynomial.affineFreeSupportCost
  omega

/-- Every squarefree sign certificate upper-bounds minimum affine-cylinder
cost by its affine-free support cost. -/
theorem minimumCost_le_affineFreeSupportCost
    (P : SquarefreePolynomial n) (hP : P.StrictSignRepresents f) :
    minimumCost f ≤ P.affineFreeSupportCost := by
  rw [← cost_ofSquarefreePolynomial P hP]
  exact minimumCost_le (ofSquarefreePolynomial P hP)

end AffineCylinderThresholdCertificate

namespace CylinderThresholdCertificate

/-- Every cylinder-threshold certificate compiles with its declared cost. -/
theorem computable (C : CylinderThresholdCertificate n f) :
    computableWithHeadsN n C.cost f := by
  simpa only [AffineCylinderThresholdCertificate.cost_ofCylinder] using
    (AffineCylinderThresholdCertificate.ofCylinder C).computable

/-- A cylinder-threshold certificate upper-bounds minimum head complexity. -/
theorem HStar_le (C : CylinderThresholdCertificate n f) :
    HStar n f ≤ C.cost :=
  HStar_le_of_computableWithHeadsN C.computable

/-- Minimum head complexity is at most minimum cylinder-threshold cost. -/
theorem HStar_le_minimumCost (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ minimumCost f := by
  obtain ⟨C, hC⟩ := minimumCost_spec f
  rw [← hC]
  exact C.HStar_le

end CylinderThresholdCertificate

/-- Short name for minimum affine-cylinder threshold cost. -/
noncomputable abbrev actc (f : (Fin n → Bool) → Bool) : ℕ :=
  AffineCylinderThresholdCertificate.minimumCost f

/-- Minimum affine-cylinder cost is at most affine-free
polynomial-threshold sparsity. -/
theorem actc_le_affineFreeSparsity (f : (Fin n → Bool) → Bool) :
    actc f ≤ affineFreeSparsity f := by
  obtain ⟨P, hP, hPcost⟩ := affineFreeSparsity_spec f
  obtain ⟨Q, hQ, hQcost, _⟩ := P.exists_strictification f hP
  calc
    actc f ≤ Q.affineFreeSupportCost :=
      AffineCylinderThresholdCertificate.minimumCost_le_affineFreeSupportCost
        Q hQ
    _ = P.affineFreeSupportCost := hQcost
    _ = affineFreeSparsity f := hPcost

/-- Minimum affine-cylinder cost is at most cylinder-threshold cost. -/
theorem actc_le_ctc (f : (Fin n → Bool) → Bool) :
    actc f ≤ ctc f :=
  AffineCylinderThresholdCertificate.minimumCost_le_cylinderMinimumCost f

/-- Minimum head complexity is at most affine-cylinder threshold cost. -/
theorem HStar_le_actc (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ actc f :=
  AffineCylinderThresholdCertificate.HStar_le_minimumCost f

/-- The affine-cylinder invariant refines both cylinder cost and affine-free
polynomial-threshold sparsity. -/
theorem actc_le_min_ctc_affineFreeSparsity
    (f : (Fin n → Bool) → Bool) :
    actc f ≤ min (ctc f) (affineFreeSparsity f) := by
  rw [Nat.le_min]
  exact ⟨actc_le_ctc f, actc_le_affineFreeSparsity f⟩

/-- The exact threshold-degree, head-complexity, affine-cylinder sandwich. -/
theorem thresholdDeg_le_HStar_le_actc_le_min_ctc_affineFreeSparsity
    (f : (Fin n → Bool) → Bool) :
    thresholdDeg f ≤ HStar n f ∧
      HStar n f ≤ actc f ∧
      actc f ≤ min (ctc f) (affineFreeSparsity f) :=
  ⟨thresholdDeg_le_HStar f,
    AffineCylinderThresholdCertificate.HStar_le_minimumCost f,
    actc_le_min_ctc_affineFreeSparsity f⟩

/-- Threshold degree is a lower bound for affine-cylinder threshold cost. -/
theorem thresholdDeg_le_actc (f : (Fin n → Bool) → Bool) :
    thresholdDeg f ≤ actc f :=
  (thresholdDeg_le_HStar f).trans
    (AffineCylinderThresholdCertificate.HStar_le_minimumCost f)

/-- Affine-cylinder cost, affine-free sparsity, and ordinary PTF sparsity form
a nested hierarchy. -/
theorem actc_le_affineFreeSparsity_le_ptfSparsity
    (f : (Fin n → Bool) → Bool) :
    actc f ≤ affineFreeSparsity f ∧
      affineFreeSparsity f ≤ ptfSparsity f :=
  ⟨actc_le_affineFreeSparsity f,
    affineFreeSparsity_le_ptfSparsity f⟩

/-- The threshold-degree support-count corollary factors through affine-cylinder
cost. -/
theorem actc_le_one_add_sum_choose_of_ThresholdDegLE
    {f : (Fin n → Bool) → Bool} {d : ℕ} (h : ThresholdDegLE f d) :
    actc f ≤ 1 + ∑ r ∈ Finset.Icc 2 d, n.choose r :=
  (actc_le_affineFreeSparsity f).trans
    (affineFreeSparsity_le_one_add_sum_choose_of_ThresholdDegLE h)

end HeadComplexity
