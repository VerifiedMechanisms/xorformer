import HeadComplexity.Results.PureSecondReplication

set_option linter.style.header false

namespace HeadComplexity.PureThreeReplicatedGrid

open scoped BigOperators

/-- Three positive inputs with type counts given by cyclic permutations of
`(0,8,9;10,10,10)`. Their pointwise first moments equal those of `fifthNegative`. -/
def fifthPositive (h : Fin 3) (p : Fin 90) : Bool :=
  let j := (p.val / 5) % 6
  let r := p.val / 30 * 5 + p.val % 5
  if j < 3 then
    if (j + h.val) % 3 = 0 then false
    else if (j + h.val) % 3 = 1 then decide (r < 8)
    else decide (6 ≤ r)
  else decide (r / 5 ≠ h.val)

/-- The negative orbit has type counts given by cyclic permutations of
`(0,2,15;14,15,1)`. The layouts make the first-moment equality pointwise. -/
def fifthNegative (h : Fin 3) (p : Fin 90) : Bool :=
  let j := (p.val / 5) % 6
  let r := p.val / 30 * 5 + p.val % 5
  if j < 3 then
    if (j + h.val) % 3 = 0 then false
    else if (j + h.val) % 3 = 1 then decide (r = 6 ∨ r = 7)
    else true
  else
    if (j - 3 + h.val) % 3 = 0 then decide (r ≠ 0)
    else if (j - 3 + h.val) % 3 = 1 then true
    else decide (r = 0)

set_option maxHeartbeats 5000000 in
-- Expand the three concrete ninety-coordinate inputs and evaluate their rational scores.
theorem fifthPositive_score (h : Fin 3) :
    score (coordinate (m := 5) (fifthPositive h)) = 49292 / 30441495 := by
  fin_cases h <;>
    norm_num [score, coordinate, numerator, denominator, fifthPositive,
      u, d, boolToReal, finProdFinEquiv, Fin.sum_univ_succ]

set_option maxHeartbeats 5000000 in
-- Expand the three concrete ninety-coordinate inputs and evaluate their rational scores.
theorem fifthNegative_score (h : Fin 3) :
    score (coordinate (m := 5) (fifthNegative h)) = -(1292 / 30413637) := by
  fin_cases h <;>
    norm_num [score, coordinate, numerator, denominator, fifthNegative,
      u, d, boolToReal, finProdFinEquiv, Fin.sum_univ_succ]

theorem fifth_first_moments (p : Fin 90) :
    (∑ h, boolToReal (fifthPositive h p)) =
      ∑ h, boolToReal (fifthNegative h p) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases p <;> norm_num [fifthPositive, fifthNegative, boolToReal]

theorem classifier_five_not_isLTF : ¬ isLTF (classifier 5) := by
  rintro ⟨c, w, hw⟩
  have hp (h : Fin 3) : 0 < c + ∑ p, w p * boolToReal (fifthPositive h p) := by
    apply (hw _).mpr
    simp only [classifier, fifthPositive_score]
    norm_num
  have hn (h : Fin 3) : c + ∑ p, w p * boolToReal (fifthNegative h p) ≤ 0 := by
    apply le_of_not_gt
    intro hh
    have hc := (hw _).mp hh
    simp only [classifier, fifthNegative_score] at hc
    norm_num at hc
  have he :
      (∑ h : Fin 3, (c + ∑ p, w p * boolToReal (fifthPositive h p))) =
        ∑ h : Fin 3, (c + ∑ p, w p * boolToReal (fifthNegative h p)) := by
    simp only [Finset.sum_add_distrib]
    congr 1
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [← Finset.mul_sum, ← Finset.mul_sum, fifth_first_moments]
  have hpos : 0 < ∑ h : Fin 3, (c + ∑ p, w p * boolToReal (fifthPositive h p)) :=
    Finset.sum_pos (fun h _ ↦ hp h) Finset.univ_nonempty
  have hneg : (∑ h : Fin 3, (c + ∑ p, w p * boolToReal (fifthNegative h p))) ≤ 0 :=
    Finset.sum_nonpos (fun h _ ↦ hn h)
  linarith

theorem classifier_five_head_minima_lower :
    2 ≤ PureRoPEHStar 90 (classifier 5) ∧ 2 ≤ SharedHStar 90 (classifier 5) ∧
      2 ≤ StandardPureRoPEHStar 90 (classifier 5) ∧
      2 ≤ FreePureRoPEHStar 90 (classifier 5) := by
  have hv : 2 ≤ HStar 90 (classifier 5) := by
    by_contra h
    have hm : HStar 90 (classifier 5) ≤ 1 := by omega
    exact classifier_five_not_isLTF
      (isLTF_of_computable_one _ (computableWithHeadsN_of_computableWithSharedHeadsN
        (computableWithSharedHeadsN_mono hm
          (computableWithSharedHeadsN_of_computableWithHeadsN (HStar_computable _)))))
  have hp : 2 ≤ PureRoPEHStar 90 (classifier 5) := by
    by_contra h
    have hm : PureRoPEHStar 90 (classifier 5) ≤ 2 := by omega
    have he := pureRoPEHStar_eq_vanilla_of_le_two (classifier 5) hm
    change PureRoPEHStar 90 (classifier 5) = HStar 90 (classifier 5) at he
    omega
  rw [SharedHStar_eq_HStar, standardPureRoPEHStar_eq_scalar, freePureRoPEHStar_eq_scalar]
  exact ⟨hp, hv, hp, hp⟩

theorem classifier_five_threshold_degree_lower : 2 ≤ thresholdDeg (classifier 5) := by
  classical
  have hc : ThresholdDegLE (classifier 5) 3 :=
    thresholdDegLE_of_pureRoPEComputable (pure_computable 5 (by norm_num))
  have hex : ∃ d, ThresholdDegLE (classifier 5) d := ⟨3, hc⟩
  have he : thresholdDeg (classifier 5) = Nat.find hex := by
    unfold thresholdDeg
    rw [dif_pos hex]
  rw [he]
  by_contra h
  have hle : Nat.find hex ≤ 1 := by omega
  obtain ⟨P, hP, hs⟩ := Nat.find_spec hex
  exact classifier_five_not_isLTF
    ((ThresholdDegLE_one_iff_isLTF _).mp ⟨P, hP.trans hle, hs⟩)

end HeadComplexity.PureThreeReplicatedGrid
