import HeadComplexity.Atoms.UnitMinimumStrict
import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Atoms.FracAtomHead
import Mathlib.Algebra.BigOperators.Fin

set_option linter.style.header false

namespace HeadComplexity.UnitMinimumAnalytic

open scoped BigOperators
open Metric Set

def cubeIndex (x : Fin 18 → Bool) : Fin (2^18) :=
  finFunctionFinEquiv (fun i ↦ finTwoEquiv.symm (x i))

theorem cubeIndex_bit (x : Fin 18 → Bool) (i : Fin 18) :
    (IntegerBinaryFiber.bit (cubeIndex x).val i.val : ℝ) = boolToReal (x i) := by
  have hh := congrArg (fun f : Fin 18 → Fin 2 ↦ (f i).val)
    (finFunctionFinEquiv.symm_apply_apply (fun j ↦ finTwoEquiv.symm (x j)))
  change (cubeIndex x).val / 2^i.val % 2 = (finTwoEquiv.symm (x i)).val at hh
  unfold IntegerBinaryFiber.bit
  rw [hh]
  cases x i <;> simp [finTwoEquiv, boolToReal]

theorem A_bool (h : Fin 3) (x : Fin 18 → Bool) (z : Space) :
    A h (cubeIndex x).val z = affineValue 0 (fun i ↦ z (numeratorIndex i h)) x := by
  simp only [A, numeratorForm_apply, affineValue, zero_add, cubeIndex_bit]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem B_bool (h : Fin 3) (x : Fin 18 → Bool) (z : Space) :
    B h (cubeIndex x).val z = affineValue 1 (fun i ↦ z (denominatorIndex i h)) x := by
  simp only [B, denominatorForm_apply, affineValue, cubeIndex_bit]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem denominator_margin (z : Space) (hz : z ∈ certBall) (h : Fin 3) :
    ∑ i : Fin 18, -z (denominatorIndex i h) < 1 := by
  have hone : ∀ i : Fin 18, IntegerBinaryFiber.bit 262143 i.val = 1 := by decide +kernel
  have hh := beta_pos.trans (B_bound h 262143 z hz)
  simp only [B, denominatorForm_apply, hone, Int.cast_one, one_mul] at hh
  rw [Finset.sum_neg_distrib]
  linarith

noncomputable def attentionAtoms (z : Space) (hz : z ∈ certBall) (h : Fin 3) : FracAtom 18 :=
  FracAtom.ofNegativeAffineRatio 0
    (fun i ↦ (2 / (UnitMinimumCenter.gamma : ℝ)) * z (numeratorIndex i h))
    1 (fun i ↦ z (denominatorIndex i h)) (by norm_num)
    (fun i ↦ slope_negative z hz i h) (denominator_margin z hz h)

theorem attentionAtoms_eval (z : Space) (hz : z ∈ certBall) (h : Fin 3) (x : Fin 18 → Bool) :
    (attentionAtoms z hz h).eval x =
      (2 / (UnitMinimumCenter.gamma : ℝ)) * A h (cubeIndex x).val z / B h (cubeIndex x).val z := by
  rw [attentionAtoms, FracAtom.ofNegativeAffineRatio_eval, A_bool, B_bool]
  unfold affineValue
  simp only [zero_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem attention_score (z : Space) (hz : z ∈ certBall) (x : Fin 18 → Bool) :
    1 + ∑ h : Fin 3, (attentionAtoms z hz h).eval x = candidateScore (cubeIndex x).val z := by
  simp only [attentionAtoms_eval, candidateScore, T, Finset.mul_sum, mul_div_assoc]

noncomputable def counterexampleFunction (x : Fin 18 → Bool) : Bool :=
  decide (0 < fullLabel (cubeIndex x).val)

theorem root_computes_function (z : Space) (hz : z ∈ certBall) (hzero : F z = 0) :
    fracComputable 18 3 counterexampleFunction := by
  refine ⟨attentionAtoms z hz, 1, ?_⟩
  intro x
  rw [attention_score]
  have hm := full_cube_unit_margin z hz hzero (cubeIndex x)
  unfold counterexampleFunction
  rw [decide_eq_true_eq]
  have hy : fullLabel (cubeIndex x).val = 1 ∨ fullLabel (cubeIndex x).val = -1 := by
    unfold fullLabel
    split_ifs <;> simp
  rcases hy with hy | hy <;> rw [hy] at hm ⊢ <;> norm_num at hm ⊢ <;> linarith

theorem counterexampleFunction_computable : computableWithHeadsN 18 3 counterexampleFunction := by
  obtain ⟨z, hz, hzero, _⟩ := exists_certified_root
  exact computable_of_fracComputable (root_computes_function z hz hzero)

theorem counterexampleFunction_shared_computable :
    computableWithSharedHeadsN 18 3 counterexampleFunction := by
  obtain ⟨z, hz, hzero, _⟩ := exists_certified_root
  exact computableWithSharedHeadsN_of_fracComputable (root_computes_function z hz hzero)

#print axioms cubeIndex_bit
#print axioms counterexampleFunction_computable
#print axioms counterexampleFunction_shared_computable

end HeadComplexity.UnitMinimumAnalytic
