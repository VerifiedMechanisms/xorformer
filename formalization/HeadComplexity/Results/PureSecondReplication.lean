import HeadComplexity.Results.PureSourceLinearApproximation
import HeadComplexity.Results.RoPESmallInputs

set_option linter.style.header false

namespace HeadComplexity.PureThreeReplicatedGrid

open scoped BigOperators

def secondPositive (p : Fin 36) : Bool :=
  if p.val / 2 = 0 ∨ p.val / 2 = 3 ∨ p.val / 2 = 9 then true
  else if p.val / 2 = 1 ∨ p.val / 2 = 4 ∨ p.val / 2 = 10 then false
  else decide (p.val % 2 = 0)

def secondNegative (p : Fin 36) : Bool :=
  if p.val / 2 = 0 then true
  else if p.val / 2 = 1 then false
  else decide (p.val % 2 = 0)

theorem secondPositive_score : score (coordinate (m := 2) secondPositive) = 4 / 39999 := by
  norm_num [score, coordinate, numerator, denominator, secondPositive,
    u, d, boolToReal, finProdFinEquiv, Fin.sum_univ_succ]

theorem secondPositive_complement_score :
    score (coordinate (m := 2) (fun p ↦ !(secondPositive p))) = 4 / 39999 := by
  norm_num [score, coordinate, numerator, denominator, secondPositive,
    u, d, boolToReal, finProdFinEquiv, Fin.sum_univ_succ]

theorem secondNegative_score : score (coordinate (m := 2) secondNegative) = -(4 / 39999) := by
  norm_num [score, coordinate, numerator, denominator, secondNegative,
    u, d, boolToReal, finProdFinEquiv, Fin.sum_univ_succ]

theorem secondNegative_complement_score :
    score (coordinate (m := 2) (fun p ↦ !(secondNegative p))) = -(4 / 39999) := by
  norm_num [score, coordinate, numerator, denominator, secondNegative,
    u, d, boolToReal, finProdFinEquiv, Fin.sum_univ_succ]

theorem classifier_two_not_isLTF : ¬ isLTF (classifier 2) := by
  rintro ⟨c, w, hw⟩
  have hp : classifier 2 secondPositive = true := by
    simp only [classifier, secondPositive_score]
    norm_num
  have hpc : classifier 2 (fun p ↦ !(secondPositive p)) = true := by
    simp only [classifier, secondPositive_complement_score]
    norm_num
  have hn : classifier 2 secondNegative ≠ true := by
    simp only [classifier, secondNegative_score]
    norm_num
  have hnc : classifier 2 (fun p ↦ !(secondNegative p)) ≠ true := by
    simp only [classifier, secondNegative_complement_score]
    norm_num
  have he (x : Fin 36 → Bool) :
      (c + ∑ p, w p * boolToReal (x p)) +
          (c + ∑ p, w p * boolToReal (!(x p))) = 2 * c + ∑ p, w p := by
    have hb (b : Bool) : boolToReal b + boolToReal (!b) = 1 := by
      cases b <;> norm_num [boolToReal]
    rw [add_add_add_comm, ← Finset.sum_add_distrib]
    simp_rw [← mul_add, hb, mul_one]
    ring
  have hp' := (hw secondPositive).mpr hp
  have hpc' := (hw (fun p ↦ !(secondPositive p))).mpr hpc
  have hn' : c + ∑ p, w p * boolToReal (secondNegative p) ≤ 0 :=
    le_of_not_gt (fun h ↦ hn ((hw _).mp h))
  have hnc' : c + ∑ p, w p * boolToReal (!(secondNegative p)) ≤ 0 :=
    le_of_not_gt (fun h ↦ hnc ((hw _).mp h))
  have he1 := he secondPositive
  have he2 := he secondNegative
  linarith

theorem classifier_two_head_minima_lower :
    2 ≤ PureRoPEHStar 36 (classifier 2) ∧ 2 ≤ SharedHStar 36 (classifier 2) ∧
      2 ≤ StandardPureRoPEHStar 36 (classifier 2) ∧
      2 ≤ FreePureRoPEHStar 36 (classifier 2) := by
  have hv : 2 ≤ HStar 36 (classifier 2) := by
    by_contra h
    have hm : HStar 36 (classifier 2) ≤ 1 := by omega
    exact classifier_two_not_isLTF
      (isLTF_of_computable_one _ (computableWithHeadsN_of_computableWithSharedHeadsN
        (computableWithSharedHeadsN_mono hm
          (computableWithSharedHeadsN_of_computableWithHeadsN (HStar_computable _)))))
  have hp : 2 ≤ PureRoPEHStar 36 (classifier 2) := by
    by_contra h
    have hm : PureRoPEHStar 36 (classifier 2) ≤ 2 := by omega
    have he := pureRoPEHStar_eq_vanilla_of_le_two (classifier 2) hm
    change PureRoPEHStar 36 (classifier 2) = HStar 36 (classifier 2) at he
    omega
  rw [SharedHStar_eq_HStar, standardPureRoPEHStar_eq_scalar, freePureRoPEHStar_eq_scalar]
  exact ⟨hp, hv, hp, hp⟩

end HeadComplexity.PureThreeReplicatedGrid
