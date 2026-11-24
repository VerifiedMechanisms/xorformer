import HeadComplexity.Atoms.ExactHammingProfile
import HeadComplexity.Atoms.CylinderApproximation
import HeadComplexity.Research.CoherentFaceGating
import HeadComplexity.Research.AnchoredAtomicDecomposition

set_option linter.style.header false

/-!
# A linear head budget for affine scores on mixed cylinders

Interpolation in the number of positive literals turns an affine score on a
mixed cylinder into at most one more head than the number of positive literals.
Simultaneous complementation gives the corresponding negative-literal bound.
The inherited exponential cylinder cost is not changed by this module.
-/

namespace HeadComplexity.LinearCylinderCompiler

open Finset
open scoped BigOperators

variable {n : ℕ}

/-- The number of true bits in a selected coordinate set. -/
def selectedWeight (P : Finset (Fin n)) (x : Fin n → Bool) : ℕ :=
  (P.filter fun i ↦ x i = true).card

theorem selectedWeight_le (P : Finset (Fin n)) (x : Fin n → Bool) :
    selectedWeight P x ≤ P.card := Finset.card_filter_le _ _

theorem selectedWeight_eq_sum (P : Finset (Fin n)) (x : Fin n → Bool) :
    (selectedWeight P x : ℝ) = ∑ i ∈ P, boolToReal (x i) := by
  unfold selectedWeight boolToReal
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp

theorem selectedWeight_eq_card_iff (P : Finset (Fin n)) (x : Fin n → Bool) :
    selectedWeight P x = P.card ↔ ∀ i ∈ P, x i = true := by
  exact Finset.card_filter_eq_iff

theorem positiveMonomial_eq_weight_test (P : Finset (Fin n)) (x : Fin n → Bool) :
    squarefreeMonomial P x = if selectedWeight P x = P.card then 1 else 0 := by
  classical
  by_cases h : selectedWeight P x = P.card
  · rw [ite_eq_left h]
    unfold squarefreeMonomial
    apply Finset.prod_eq_one
    intro i hi
    simp [boolToReal, (selectedWeight_eq_card_iff P x).mp h i hi]
  · rw [ite_eq_right h]
    have hex : ∃ i ∈ P, x i = false := by
      by_contra hn
      push Not at hn
      apply h
      rw [selectedWeight_eq_card_iff]
      intro i hi
      cases hx : x i <;> simp_all
    obtain ⟨i, hi, hx⟩ := hex
    unfold squarefreeMonomial
    apply Finset.prod_eq_zero hi
    simp [boolToReal, hx]

private theorem affineValue_scale (a r : ℝ) (u : Fin n → ℝ)
    (x : Fin n → Bool) :
    affineValue (r * a) (fun i ↦ r * u i) x = r * affineValue a u x := by
  unfold affineValue
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- An arbitrary profile of selected Hamming weight, multiplied by an affine
score and restricted to a negative coordinate face, has a linear head budget.
No condition on the intersection of the selected coordinates and the face is
needed. Every approximating head is an original admissible fractional atom. -/
theorem uniformlyAtomsApproximable_negativeFace_profile_affine
    (P S : Finset (Fin n)) (target : Fin (P.card + 1) → ℝ)
    (a : ℝ) (u : Fin n → ℝ) :
    UniformlyAtomsApproximable (Fin (P.card + 1))
      (fun x ↦ squarefreeMonomial S (flipBits x) * affineValue a u x *
        target ⟨selectedWeight P x, Nat.lt_succ_of_le (selectedWeight_le P x)⟩) := by
  classical
  obtain ⟨b, c, hprofile⟩ := exists_exact_hamming_reciprocals target
  let g : Fin (P.card + 1) → (Fin n → Bool) → ℝ := Fin.cases
    (fun x ↦ squarefreeMonomial S (flipBits x) * (c * affineValue a u x))
    (fun h x ↦ squarefreeMonomial S (flipBits x) *
      (b h * affineValue a u x / ((selectedWeight P x : ℝ) + exactProfileShift P.card h)))
  have hg : ∀ h, UniformlyOneAtomApproximable (g h) := by
    intro h
    refine Fin.cases ?_ (fun j ↦ ?_) h
    · simpa only [g, Fin.cases_zero, affineValue_scale] using
        AnchoredAtomicDecomposition.uniformlyOneAtomApproximable_negativeFace_affine
          S (c * a) (fun i ↦ c * u i)
    · have hd : ∀ x, affineValue (exactProfileShift P.card j)
          (fun i ↦ if i ∈ P then 1 else 0) x =
          (selectedWeight P x : ℝ) + exactProfileShift P.card j := by
        intro x
        unfold affineValue
        rw [selectedWeight_eq_sum]
        simp only [ite_mul, one_mul, zero_mul]
        rw [← Finset.sum_filter]
        simp [add_comm]
      have ha := CoherentFaceGating.uniformlyOneAtomApproximable_negativeFace_ratio
        S (b j * a) (exactProfileShift P.card j) (fun i ↦ b j * u i)
        (fun i ↦ if i ∈ P then 1 else 0) (exactProfileShift_pos P.card j)
        (fun i ↦ by split_ifs <;> norm_num)
      simpa only [g, Fin.cases_succ, affineValue_scale, hd] using ha
  have heq : ∀ x, (∑ h, g h x) =
      squarefreeMonomial S (flipBits x) * affineValue a u x *
        target ⟨selectedWeight P x, Nat.lt_succ_of_le (selectedWeight_le P x)⟩ := by
    intro x
    have hp := hprofile ⟨selectedWeight P x,
      Nat.lt_succ_of_le (selectedWeight_le P x)⟩
    rw [← hp]
    simp only [g, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  have hsum := CubeCylinder.uniformlyAtomsApproximable_fin_sum g hg
  simpa only [heq] using hsum

/-- A mixed-cylinder affine score has an approximation using the number of
positive literals plus one heads. -/
theorem uniformlyAtomsApproximable_cylinder_affine_positive
    (C : CubeCylinder n) (a : ℝ) (u : Fin n → ℝ) :
    UniformlyAtomsApproximable (Fin (C.positive.card + 1))
      (fun x ↦ C.eval x * affineValue a u x) := by
  have h := uniformlyAtomsApproximable_negativeFace_profile_affine
    C.positive C.negative (fun k ↦ if k.val = C.positive.card then 1 else 0) a u
  have heq : ∀ x,
      squarefreeMonomial C.negative (flipBits x) * affineValue a u x *
        (if selectedWeight C.positive x = C.positive.card then 1 else 0) =
      C.eval x * affineValue a u x := by
    intro x
    rw [← positiveMonomial_eq_weight_test]
    rw [CubeCylinder.squarefreeMonomial_flipBits]
    unfold CubeCylinder.eval squarefreeMonomial CubeCylinder.negativeSquarefreeMonomial
    ring
  simpa only [heq] using h

/-- Simultaneous complementation gives a head budget controlled by the number
of negative literals. This uses exact symmetry of the original atom class. -/
theorem uniformlyAtomsApproximable_cylinder_affine_negative
    (C : CubeCylinder n) (a : ℝ) (u : Fin n → ℝ) :
    UniformlyAtomsApproximable (Fin (C.negative.card + 1))
      (fun x ↦ C.eval x * affineValue a u x) := by
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
  obtain ⟨φ, c, hφ⟩ := uniformlyAtomsApproximable_cylinder_affine_positive
    D (a + ∑ i, u i) (fun i ↦ -u i) ε hε
  refine ⟨fun h ↦ (φ h).flip, c, fun x ↦ ?_⟩
  simpa only [FracAtom.flip_eval, hD,
    AnchoredAtomicDecomposition.affineValue_flipBits] using hφ (flipBits x)

/-- The cheaper orientation gives a linear head budget for every affine
mixed-cylinder score, without modifying the older exponential cost. -/
theorem uniformlyAtomsApproximable_cylinder_affine_min
    (C : CubeCylinder n) (a : ℝ) (u : Fin n → ℝ) :
    UniformlyAtomsApproximable
      (Fin (min C.positive.card C.negative.card + 1))
      (fun x ↦ C.eval x * affineValue a u x) := by
  by_cases h : C.positive.card ≤ C.negative.card
  · rw [min_eq_left h]
    exact uniformlyAtomsApproximable_cylinder_affine_positive C a u
  · rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))]
    exact uniformlyAtomsApproximable_cylinder_affine_negative C a u

/-- A strict sign representation by finitely many affine cylinder blocks
compiles into the original unrestricted model with the sum of their linear
budgets. The affine numerators and their signed cancellation are unrestricted. -/
theorem computableWithHeadsN_of_cylinder_affine_sum
    {J : Type*} [Fintype J] (C : J → CubeCylinder n)
    (a : J → ℝ) (u : J → Fin n → ℝ) (bias : ℝ)
    (f : (Fin n → Bool) → Bool)
    (hstrict : StrictSignRepresentsScore
      (fun x ↦ bias + ∑ j, (C j).eval x * affineValue (a j) (u j) x) f) :
    computableWithHeadsN n
      (∑ j, (min (C j).positive.card (C j).negative.card + 1)) f := by
  have h := computableWithHeadsCard_of_uniformlyAtomsApproximable
    (I := fun j ↦ Fin (min (C j).positive.card (C j).negative.card + 1))
    (fun j x ↦ (C j).eval x * affineValue (a j) (u j) x)
    (fun j ↦ uniformlyAtomsApproximable_cylinder_affine_min (C j) (a j) (u j))
    bias hstrict
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h

end HeadComplexity.LinearCylinderCompiler
