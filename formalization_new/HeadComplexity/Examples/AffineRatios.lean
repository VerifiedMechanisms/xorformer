module

public import HeadComplexity.Attention.AffineFraction
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# Worked examples of affine ratios

The admissibility criterion has both a positivity and a slope condition. The examples
below check their boundary cases and show how different affine ratios can describe
the same scalar score on a Boolean cube.
-/

@[expose] public section

open scoped BigOperators

namespace HeadComplexity.Examples.AffineRatios

open Attention

/-- An affine fraction specified by the constant and coefficients of each affine map. -/
noncomputable def ofCoefficients {n : ℕ} (a : ℝ) (u : Fin n → ℝ) (b : ℝ) (v : Fin n → ℝ) :
    AffineFraction n :=
  ⟨(AffineMap.constCoeffEquiv ℝ (Fin n)).symm (a, u),
    (AffineMap.constCoeffEquiv ℝ (Fin n)).symm (b, v)⟩

/-- A two-bit affine denominator is positive on the cube exactly when it is positive at each of
the four corners. -/
private theorem denominator_pos_two_iff (b : ℝ) (v : Fin 2 → ℝ) :
    (∀ x, 0 < (AffineMap.constCoeffEquiv ℝ (Fin 2)).symm (b, v) (Bool.cubePoint ℝ x)) ↔
      0 < b ∧ 0 < b + v 0 ∧ 0 < b + v 1 ∧ 0 < b + v 0 + v 1 := by
  simp [AffineMap.constCoeffEquiv_symm_apply, dotProduct, Fin.sum_univ_two,
    Fin.forall_fin_succ_pi, Bool.forall_bool, add_assoc, and_left_comm, and_assoc]

/-- The denominator with constant one and slopes one and two permits arbitrary numerator
coefficients. -/
theorem positive_denominator (a : ℝ) (u : Fin 2 → ℝ) :
    (ofCoefficients a u 1 ![1, 2]).Admissible := by
  norm_num [AffineFraction.Admissible, denominator_pos_two_iff, ofCoefficients,
    Fin.forall_fin_two, funext_iff]

/-- The denominator with constant three and slopes both negative one permits arbitrary numerator
coefficients. -/
theorem negative_denominator (a : ℝ) (u : Fin 2 → ℝ) :
    (ofCoefficients a u 3 ![-1, -1]).Admissible := by
  norm_num [AffineFraction.Admissible, denominator_pos_two_iff, ofCoefficients,
    Fin.forall_fin_two, funext_iff]

/-- The displayed numerator with two positive slopes is admissible over the constant denominator
one. -/
theorem constant_positive (a : ℝ) : (ofCoefficients a (![1, 2] : Fin 2 → ℝ) 1 0).Admissible := by
  norm_num [AffineFraction.Admissible, denominator_pos_two_iff, ofCoefficients, Fin.forall_fin_two]

/-- The displayed numerator with two negative slopes is admissible over the constant denominator
one. -/
theorem constant_negative (a : ℝ) : (ofCoefficients a (![-1, -2] : Fin 2 → ℝ) 1 0).Admissible := by
  norm_num [AffineFraction.Admissible, denominator_pos_two_iff, ofCoefficients, Fin.forall_fin_two]

/-- Any constant numerator is admissible over the constant denominator one. -/
theorem constant_zero (a : ℝ) : (ofCoefficients a (0 : Fin 2 → ℝ) 1 0).Admissible := by
  norm_num [AffineFraction.Admissible, denominator_pos_two_iff, ofCoefficients, Fin.forall_fin_two]

/-- The displayed positive denominator is inadmissible because its slopes have opposite signs. -/
theorem mixed_denominator (u : Fin 2 → ℝ) : ¬ (ofCoefficients 0 u 3 ![1, -1]).Admissible := by
  norm_num [AffineFraction.Admissible, denominator_pos_two_iff, ofCoefficients,
    Fin.forall_fin_two, funext_iff]

/-- The displayed denominator is inadmissible because one slope is zero and the other is
nonzero. -/
theorem partially_zero_denominator (u : Fin 2 → ℝ) :
    ¬ (ofCoefficients 0 u 1 ![1, 0]).Admissible := by
  norm_num [AffineFraction.Admissible, denominator_pos_two_iff, ofCoefficients,
    Fin.forall_fin_two, funext_iff]

/-- The denominator with constant two and slopes both negative one is inadmissible because it
vanishes at the all-true input. -/
theorem vanishing_denominator (u : Fin 2 → ℝ) :
    ¬ (ofCoefficients 0 u 2 ![-1, -1]).Admissible := by
  norm_num [AffineFraction.Admissible, denominator_pos_two_iff, ofCoefficients]

/-- With a constant denominator, a numerator with one zero slope and one nonzero slope is
inadmissible. -/
theorem partially_zero_numerator :
    ¬ (ofCoefficients 0 (![1, 0] : Fin 2 → ℝ) 1 0).Admissible := by
  norm_num [AffineFraction.Admissible, denominator_pos_two_iff, ofCoefficients,
    Fin.forall_fin_two, funext_iff]

/-- The difference of two bits has mixed numerator slopes and is inadmissible over the constant
denominator one. -/
theorem difference_constant_not_admissible :
    ¬ (ofCoefficients 0 (![1, -1] : Fin 2 → ℝ) 1 0).Admissible := by
  norm_num [AffineFraction.Admissible, denominator_pos_two_iff, ofCoefficients,
    Fin.forall_fin_two, funext_iff]

/-- The difference of two bits also has a representation with a nonconstant denominator. -/
theorem difference_ratio (x : Fin 2 → Bool) :
    (ofCoefficients 0 ![2, -2] 1 ![1, 1]).eval x = Bool.cubePoint ℝ x 0 - Bool.cubePoint ℝ x 1 := by
  cases h₀ : x 0 <;> cases h₁ : x 1 <;>
    norm_num [AffineFraction.eval, ofCoefficients, AffineMap.constCoeffEquiv_symm_apply,
      dotProduct, Fin.sum_univ_two, h₀, h₁]

/-- The fraction with numerator twice the bit difference and denominator one plus Hamming weight
is admissible. -/
private theorem difference_admissible : (ofCoefficients 0 ![2, -2] 1 ![1, 1]).Admissible := by
  norm_num [AffineFraction.Admissible, denominator_pos_two_iff, ofCoefficients,
    Fin.forall_fin_two, funext_iff]

/-- A scalar head profile can realize the exact difference of the two input bits. -/
theorem difference_is_scalarHeadProfile :
    ∃ p : ScalarHeadProfile 2, ∀ x, p.eval x = Bool.cubePoint ℝ x 0 - Bool.cubePoint ℝ x 1 := by
  obtain ⟨p, hp⟩ := (AffineFraction.realizable_iff _).2 difference_admissible
  exact ⟨p, fun x ↦ by rw [p.eval_eq_eval_toAffineFraction, hp, difference_ratio]⟩

/-- With no input coordinates, exact realization requires only a positive denominator. -/
theorem dimension_zero (r : AffineFraction 0) :
    (∃ p : ScalarHeadProfile 0, p.toAffineFraction = r) ↔ 0 < r.denominator 0 := by
  rw [r.realizable_iff]
  have hvertex (x : Fin 0 → Bool) : Bool.cubePoint ℝ x = 0 := funext fun i ↦ i.elim0
  simp [AffineFraction.Admissible, hvertex]

/-- A constant offset is an exact score even without heads. -/
theorem constant_score_zero_heads (n : ℕ) (c : ℝ) :
    HasHeadScore (fun _ : Fin n → Bool ↦ c) 0 :=
  hasHeadScore_zero_iff.mpr ⟨c, rfl⟩

/-- One head realizes the signed difference of the bits with an arbitrary constant offset. -/
theorem difference_plus_constant_is_shared_score (c : ℝ) :
    HasHeadScore (fun x : Fin 2 → Bool ↦ c + (Bool.cubePoint ℝ x 0 - Bool.cubePoint ℝ x 1)) 1 := by
  apply hasHeadScore_iff_exists_affineFractions.mpr
  refine ⟨c, fun _ ↦ ofCoefficients 0 ![2, -2] 1 ![1, 1], fun _ ↦ difference_admissible, ?_⟩
  intro x
  simp only [Fin.sum_univ_one, difference_ratio]

end HeadComplexity.Examples.AffineRatios
