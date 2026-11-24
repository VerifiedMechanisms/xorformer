import HeadComplexity.Research.LinearCylinderCompiler

set_option linter.style.header false

/-!
Scalar mixed-cylinder profiles save the separate gated constant term: absorb
that constant into the affine numerator of one reciprocal. This operation is
specific to scalar profiles; a further arbitrary affine multiplier would make
that numerator quadratic.
-/
noncomputable section
namespace HeadComplexity.ScalarCylinderCompiler
open Finset LinearCylinderCompiler
open scoped BigOperators
variable {n : ℕ}

/-- A nonempty selected set permits absorption of the profile's constant part
into one affine numerator, saving one head for scalar profiles. -/
theorem uniformlyAtomsApproximable_negativeFace_profile
    (P S : Finset (Fin n)) (hP : 0 < P.card)
    (target : Fin (P.card + 1) → ℝ) :
    UniformlyAtomsApproximable (Fin P.card)
      (fun x ↦ squarefreeMonomial S (flipBits x) *
        target ⟨selectedWeight P x, Nat.lt_succ_of_le (selectedWeight_le P x)⟩) := by
  classical
  obtain ⟨b, c, hprofile⟩ := exists_exact_hamming_reciprocals target
  let j0 : Fin P.card := ⟨0,hP⟩
  let g : Fin P.card → (Fin n → Bool) → ℝ := fun j x ↦
    squarefreeMonomial S (flipBits x) *
      (b j / ((selectedWeight P x : ℝ) + exactProfileShift P.card j) +
        if j = j0 then c else 0)
  have hd : ∀ j x, affineValue (exactProfileShift P.card j)
      (fun i ↦ if i ∈ P then 1 else 0) x =
      (selectedWeight P x : ℝ) + exactProfileShift P.card j := by
    intro j x
    unfold affineValue
    rw [selectedWeight_eq_sum]
    simp only [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    simp [add_comm]
  have hg : ∀ j, UniformlyOneAtomApproximable (g j) := by
    intro j
    let k : ℝ := if j = j0 then c else 0
    have ha := CoherentFaceGating.uniformlyOneAtomApproximable_negativeFace_ratio
      S (b j + k * exactProfileShift P.card j) (exactProfileShift P.card j)
      (fun i ↦ k * if i ∈ P then 1 else 0)
      (fun i ↦ if i ∈ P then 1 else 0) (exactProfileShift_pos P.card j)
      (fun i ↦ by split_ifs <;> norm_num)
    have heq : ∀ x, affineValue (b j + k * exactProfileShift P.card j)
        (fun i ↦ k * if i ∈ P then 1 else 0) x /
          affineValue (exactProfileShift P.card j) (fun i ↦ if i ∈ P then 1 else 0) x =
        b j / ((selectedWeight P x : ℝ) + exactProfileShift P.card j) + k := by
      intro x
      have hden : 0 < (selectedWeight P x : ℝ) + exactProfileShift P.card j := by
        have := exactProfileShift_pos P.card j
        positivity
      rw [hd]
      have hnum : affineValue (b j + k * exactProfileShift P.card j)
          (fun i ↦ k * if i ∈ P then 1 else 0) x =
          b j + k * ((selectedWeight P x : ℝ) + exactProfileShift P.card j) := by
        unfold affineValue
        rw [selectedWeight_eq_sum]
        simp only [mul_assoc, ite_mul, one_mul, zero_mul]
        rw [← Finset.mul_sum]
        rw [← Finset.sum_filter]
        simp only [filter_mem_eq_inter, univ_inter]
        ring
      rw [hnum]
      field_simp
    simpa only [heq, g, k] using ha
  have heq : ∀ x, (∑ j, g j x) = squarefreeMonomial S (flipBits x) *
      target ⟨selectedWeight P x, Nat.lt_succ_of_le (selectedWeight_le P x)⟩ := by
    intro x
    have hp := hprofile ⟨selectedWeight P x,
      Nat.lt_succ_of_le (selectedWeight_le P x)⟩
    rw [← hp]
    simp only [g, ← Finset.mul_sum, Finset.sum_add_distrib]
    simp [add_comm]
  have hsum := CubeCylinder.uniformlyAtomsApproximable_fin_sum g hg
  simpa only [heq] using hsum

/-- A scalar cylinder saves one head whenever its positive side is nonempty. -/
theorem uniformlyAtomsApproximable_cylinder_positive
    (C : CubeCylinder n) (hC : 0 < C.positive.card) :
    UniformlyAtomsApproximable (Fin C.positive.card) C.eval := by
  have h := uniformlyAtomsApproximable_negativeFace_profile C.positive C.negative hC
    (fun k ↦ if k.val = C.positive.card then 1 else 0)
  have heq : ∀ x,
      squarefreeMonomial C.negative (flipBits x) *
        (if selectedWeight C.positive x = C.positive.card then 1 else 0) = C.eval x := by
    intro x
    rw [← positiveMonomial_eq_weight_test, CubeCylinder.squarefreeMonomial_flipBits]
    unfold CubeCylinder.eval squarefreeMonomial CubeCylinder.negativeSquarefreeMonomial
    ring
  simpa only [heq] using h

/-- The zero-positive-literal case needs only one head. -/
theorem uniformlyAtomsApproximable_cylinder_positive_max
    (C : CubeCylinder n) :
    UniformlyAtomsApproximable (Fin (max 1 C.positive.card)) C.eval := by
  by_cases hC : 0 < C.positive.card
  · rw [max_eq_right hC]
    exact uniformlyAtomsApproximable_cylinder_positive C hC
  · have he : C.positive = ∅ := Finset.card_eq_zero.mp (by omega)
    have h := (CubeCylinder.uniformlyOneAtomApproximable_signedNegativeMonomial
      C.negative 1).toUniformlyAtomsApproximable
    have hc : C.positive.card = 0 := by simp [he]
    rw [hc, max_eq_left (by omega : 0 ≤ 1)]
    convert h using 1
    funext x
    simp [CubeCylinder.eval, CubeCylinder.negativeSquarefreeMonomial, he]

/-- Complementing every input exchanges the two scalar-cylinder budgets. -/
theorem uniformlyAtomsApproximable_cylinder_negative_max
    (C : CubeCylinder n) :
    UniformlyAtomsApproximable (Fin (max 1 C.negative.card)) C.eval := by
  let D : CubeCylinder n := ⟨C.negative, C.positive, C.disjoint.symm⟩
  have hD : ∀ x, D.eval (flipBits x) = C.eval x := by
    intro x
    have hbit : ∀ i, boolToReal (flipBits x i) = 1 - boolToReal (x i) := by
      intro i
      cases hx : x i <;> simp [flipBits, boolToReal, hx]
    change (∏ i ∈ C.negative, boolToReal (flipBits x i)) *
      (∏ i ∈ C.positive, (1 - boolToReal (flipBits x i))) =
      (∏ i ∈ C.positive, boolToReal (x i)) *
      (∏ i ∈ C.negative, (1 - boolToReal (x i)))
    simp_rw [hbit, sub_sub_cancel]
    ring
  intro ε hε
  obtain ⟨φ, c, hφ⟩ := uniformlyAtomsApproximable_cylinder_positive_max D ε hε
  exact ⟨fun h ↦ (φ h).flip, c, fun x ↦ by
    simpa only [FracAtom.flip_eval, hD] using hφ (flipBits x)⟩

/-- A scalar mixed cylinder is uniformly approximable with the smaller
nonzero literal count. Every approximant uses admissible original atoms. -/
theorem uniformlyAtomsApproximable_cylinder_min
    (C : CubeCylinder n) :
    UniformlyAtomsApproximable
      (Fin (max 1 (min C.positive.card C.negative.card))) C.eval := by
  by_cases h : C.positive.card ≤ C.negative.card
  · rw [min_eq_left h]
    exact uniformlyAtomsApproximable_cylinder_positive_max C
  · rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))]
    exact uniformlyAtomsApproximable_cylinder_negative_max C

end HeadComplexity.ScalarCylinderCompiler

