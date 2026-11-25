import HeadComplexity.Results.PureSecondReplication
import HeadComplexity.Polynomial.QuadraticMomentCertificate
import HeadComplexity.Results.PureSourceTwoReplicasUpper

set_option linter.style.header false

namespace HeadComplexity.PureThreeReplicatedGrid

open scoped BigOperators

def positiveCount (h : Fin 3) (j : Fin 6) : ℕ :=
  ![![1, 4, 4, 1, 3, 5], ![4, 1, 4, 5, 1, 3], ![4, 4, 1, 3, 5, 1]] h j

/-- The six cyclic shifts of each of three count patterns. -/
def balancedPositive (i : Fin 3 × Fin 6) (p : Fin 36) : Bool :=
  decide (((p.val / 12 * 2 + p.val % 2 + i.2.val) % 6) <
    positiveCount i.1 ⟨(p.val / 2) % 6, Nat.mod_lt _ (by decide)⟩)

set_option maxHeartbeats 5000000 in
-- Each of the eighteen explicit Boolean inputs is checked by exact rational arithmetic.
theorem balancedPositive_score (i : Fin 3 × Fin 6) :
    score (coordinate (m := 2) (balancedPositive i)) = 1 / 1999950 := by
  rcases i with ⟨h, s⟩
  fin_cases h <;> fin_cases s <;>
    norm_num [score, coordinate, numerator, denominator, balancedPositive, positiveCount,
      u, d, boolToReal, finProdFinEquiv, Fin.sum_univ_succ]

set_option maxHeartbeats 5000000 in
-- The complementary inputs have exactly the opposite nonzero source scores.
theorem balancedPositive_complement_score (i : Fin 3 × Fin 6) :
    score (coordinate (m := 2) (fun p ↦ !(balancedPositive i p))) = -(1 / 1999950) := by
  rcases i with ⟨h, s⟩
  fin_cases h <;> fin_cases s <;>
    norm_num [score, coordinate, numerator, denominator, balancedPositive, positiveCount,
      u, d, boolToReal, finProdFinEquiv, Fin.sum_univ_succ]

theorem balancedPositive_moment (p : Fin 36) :
    (∑ i : Fin 3 × Fin 6, boolToReal (balancedPositive i p)) = 9 := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases p <;>
    norm_num [balancedPositive, positiveCount, boolToReal,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem classifier_two_not_thresholdDegLE_two : ¬ ThresholdDegLE (classifier 2) 2 := by
  apply QuadraticMomentCertificate.not_thresholdDegLE_two _ balancedPositive
  · intro p
    convert balancedPositive_moment p using 1
    norm_num
  · intro i
    simp only [classifier, balancedPositive_score]
    norm_num
  · intro i
    simp only [classifier, balancedPositive_complement_score]
    norm_num

theorem classifier_two_pure_head_minimum : PureRoPEHStar 36 (classifier 2) = 3 := by
  classical
  have hu : PureRoPEHStar 36 (classifier 2) ≤ 3 :=
    Nat.find_min' (exists_pureRoPEComputable _) (pure_computable 2 (by norm_num))
  have hl : ¬ PureRoPEHStar 36 (classifier 2) ≤ 2 := by
    intro hh
    obtain ⟨P, hP, hs⟩ := thresholdDegLE_of_pureRoPEComputable
      (pureRoPEHStar_computable (classifier 2))
    exact classifier_two_not_thresholdDegLE_two ⟨P, hP.trans hh, hs⟩
  omega

theorem classifier_two_head_minima :
    PureRoPEHStar 36 (classifier 2) = 3 ∧ SharedHStar 36 (classifier 2) = 3 ∧
      StandardPureRoPEHStar 36 (classifier 2) = 3 ∧
      FreePureRoPEHStar 36 (classifier 2) = 3 := by
  have hp := classifier_two_pure_head_minimum
  have hu : HStar 36 (classifier 2) ≤ 3 := by
    classical
    have hc := computableWithHeadsN_of_computableWithSharedHeadsN classifier_two_vanilla_three
    have hex := exists_computable (classifier 2)
    have he : HStar 36 (classifier 2) = Nat.find hex := by
      unfold HStar
      rw [dif_pos hex]
    rw [he]
    exact Nat.find_min' hex hc
  have hv : HStar 36 (classifier 2) = 3 := by
    have hl := pureRoPEHStar_le_vanilla (classifier 2)
    change PureRoPEHStar 36 (classifier 2) ≤ HStar 36 (classifier 2) at hl
    omega
  rw [SharedHStar_eq_HStar, standardPureRoPEHStar_eq_scalar, freePureRoPEHStar_eq_scalar]
  exact ⟨hp, hv, hp, hp⟩

theorem classifier_two_threshold_degree : thresholdDeg (classifier 2) = 3 := by
  classical
  have hc : ThresholdDegLE (classifier 2) 3 :=
    thresholdDegLE_of_pureRoPEComputable (pure_computable 2 (by norm_num))
  have hex : ∃ d, ThresholdDegLE (classifier 2) d := ⟨3, hc⟩
  have he : thresholdDeg (classifier 2) = Nat.find hex := by
    unfold thresholdDeg
    rw [dif_pos hex]
  rw [he]
  have hu := Nat.find_min' hex hc
  have hl : ¬ Nat.find hex ≤ 2 := by
    intro hh
    obtain ⟨P, hP, hs⟩ := Nat.find_spec hex
    exact classifier_two_not_thresholdDegLE_two ⟨P, hP.trans hh, hs⟩
  omega

end HeadComplexity.PureThreeReplicatedGrid
