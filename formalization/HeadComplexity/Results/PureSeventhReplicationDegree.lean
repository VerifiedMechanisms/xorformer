import HeadComplexity.Results.PureFifthReplicationNonlinear
import HeadComplexity.Polynomial.RoPEGroupSymmetrization
import HeadComplexity.Polynomial.QuadraticMomentCertificate

set_option linter.style.header false

namespace HeadComplexity.PureThreeReplicatedGrid

open scoped BigOperators
open MvPolynomial

def seventhIndex (p : Fin 126) : Fin 6 × Fin 21 :=
  (⟨(p.val / 7) % 6, Nat.mod_lt _ (by decide)⟩,
    ⟨p.val / 42 * 7 + p.val % 7, by omega⟩)

noncomputable def seventhCount (x : Fin 6 × Fin 21 → Bool) (g : Fin 6) : ℝ :=
  ∑ r, boolToReal (x (g, r))

noncomputable def seventhAggregate (c : Fin 6 → ℝ) (g : Fin 6) : ℝ :=
  (2 * c g - 21) / 7

noncomputable def seventhCountScore (c : Fin 6 → ℝ) : ℝ :=
  ∑ h : Fin 3,
    (2 * ((∑ g, seventhAggregate c g) + seventhAggregate c h.castSucc.castSucc.castSucc)) /
      (200 + seventhAggregate c h.castSucc.castSucc.castSucc -
        seventhAggregate c ⟨h.val + 3, by omega⟩)

set_option maxHeartbeats 5000000 in
-- The finite reindexing identity expands 126 Boolean coordinates into six type counts.
theorem seventh_score_count (x : Fin 6 × Fin 21 → Bool) :
    score (coordinate (m := 7) (fun p ↦ x (seventhIndex p))) =
      seventhCountScore (seventhCount x) := by
  have hn (h : Fin 3) :
      numerator h (coordinate (m := 7) (fun p ↦ x (seventhIndex p))) =
        2 * ((∑ g, seventhAggregate (seventhCount x) g) +
          seventhAggregate (seventhCount x) h.castSucc.castSucc.castSucc) := by
    fin_cases h <;>
      norm_num [numerator, coordinate, u, seventhIndex, seventhCount,
        seventhAggregate, finProdFinEquiv, Fin.sum_univ_succ, Fin.succ] <;> ring
  have hd (h : Fin 3) :
      denominator h (coordinate (m := 7) (fun p ↦ x (seventhIndex p))) =
        200 + seventhAggregate (seventhCount x) h.castSucc.castSucc.castSucc -
          seventhAggregate (seventhCount x) ⟨h.val + 3, by omega⟩ := by
    fin_cases h <;>
      norm_num [denominator, coordinate, d, seventhIndex, seventhCount,
        seventhAggregate, finProdFinEquiv, Fin.sum_univ_succ, Fin.succ] <;> ring
  simp only [score, seventhCountScore, hn, hd]

def seventhPositiveCounts (h : Fin 6) : Fin 6 → ℕ :=
  ![![0,15,20,15,11,1], ![0,20,15,15,1,11], ![15,0,20,11,15,1],
    ![15,20,0,11,1,15], ![20,0,15,1,15,11], ![20,15,0,1,11,15]] h

def seventhNegativeCounts (h : Fin 6) : Fin 6 → ℕ :=
  ![![0,15,20,17,3,7], ![0,20,15,17,7,3], ![15,0,20,3,17,7],
    ![15,20,0,3,7,17], ![20,0,15,7,17,3], ![20,15,0,7,3,17]] h

theorem seventh_count_moments :
    (∀ g, (∑ h, (seventhPositiveCounts h g : ℝ)) =
      ∑ h, (seventhNegativeCounts h g : ℝ)) ∧
    ∀ g j, (∑ h, (seventhPositiveCounts h g : ℝ) * seventhPositiveCounts h j) =
      ∑ h, (seventhNegativeCounts h g : ℝ) * seventhNegativeCounts h j := by
  constructor
  · intro g
    fin_cases g <;> norm_num [seventhPositiveCounts, seventhNegativeCounts, Fin.sum_univ_succ]
  · intro g j
    fin_cases g <;> fin_cases j <;>
      norm_num [seventhPositiveCounts, seventhNegativeCounts, Fin.sum_univ_succ]

theorem seventh_positive_count_score (h : Fin 6) :
    seventhCountScore (fun g ↦ (seventhPositiveCounts h g : ℝ)) = 3637 / 346730560 := by
  fin_cases h <;>
    norm_num [seventhCountScore, seventhAggregate, seventhPositiveCounts, Fin.sum_univ_succ]

theorem seventh_negative_count_score (h : Fin 6) :
    seventhCountScore (fun g ↦ (seventhNegativeCounts h g : ℝ)) = -(203 / 346729048) := by
  fin_cases h <;>
    norm_num [seventhCountScore, seventhAggregate, seventhNegativeCounts, Fin.sum_univ_succ]

theorem seventhCount_permute (x : Fin 6 × Fin 21 → Bool)
    (π : Fin 6 → Equiv.Perm (Fin 21)) :
    seventhCount (fun p ↦ x (p.1, π p.1 p.2)) = seventhCount x := by
  funext g
  exact Equiv.sum_comp (π g) (fun r ↦ boolToReal (x (g, r)))

theorem seventh_group_sign (P : MvPolynomial (Fin 126) ℝ)
    (hs : SignRepresents P (classifier 7)) (x : Fin 6 × Fin 21 → Bool) :
    let Q := RoPEGroupSymmetrization.groupPolynomial (rename seventhIndex P)
    (0 < seventhCountScore (seventhCount x) → 0 < eval (seventhCount x) Q) ∧
    (seventhCountScore (seventhCount x) ≤ 0 → eval (seventhCount x) Q ≤ 0) := by
  classical
  dsimp only
  have he := RoPEGroupSymmetrization.groupPolynomial_eval (rename seventhIndex P) x
  simp only [hammingWeight_eq_sum] at he
  change eval (seventhCount x) _ = _ at he
  rw [he]
  simp only [eval_rename]
  constructor
  · intro hx
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro π _
    apply (hs (fun p ↦ x ((seventhIndex p).1, π (seventhIndex p).1 (seventhIndex p).2))).mpr
    change decide (0 < score (coordinate _)) = true
    rw [seventh_score_count (fun q ↦ x (q.1, π q.1 q.2)), seventhCount_permute]
    exact decide_eq_true hx
  · intro hx
    apply Finset.sum_nonpos
    intro π _
    apply le_of_not_gt
    intro hp
    have hh := (hs (fun p ↦ x ((seventhIndex p).1,
      π (seventhIndex p).1 (seventhIndex p).2))).mp hp
    change decide (0 < score (coordinate _)) = true at hh
    rw [seventh_score_count (fun q ↦ x (q.1, π q.1 q.2)), seventhCount_permute] at hh
    exact not_lt_of_ge hx (of_decide_eq_true hh)

def seventhPositiveInput (h : Fin 6) (p : Fin 6 × Fin 21) : Bool :=
  decide (p.2.val < seventhPositiveCounts h p.1)

def seventhNegativeInput (h : Fin 6) (p : Fin 6 × Fin 21) : Bool :=
  decide (p.2.val < seventhNegativeCounts h p.1)

theorem seventhPositiveInput_count (h : Fin 6) :
    seventhCount (seventhPositiveInput h) = fun g ↦ (seventhPositiveCounts h g : ℝ) := by
  funext g
  simp only [seventhCount, Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases h <;> fin_cases g <;>
    norm_num [seventhPositiveInput, seventhPositiveCounts, boolToReal]

theorem seventhNegativeInput_count (h : Fin 6) :
    seventhCount (seventhNegativeInput h) = fun g ↦ (seventhNegativeCounts h g : ℝ) := by
  funext g
  simp only [seventhCount, Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases h <;> fin_cases g <;>
    norm_num [seventhNegativeInput, seventhNegativeCounts, boolToReal]

theorem classifier_seven_not_thresholdDegLE_two : ¬ ThresholdDegLE (classifier 7) 2 := by
  classical
  rintro ⟨P, hP, hs⟩
  let Q := RoPEGroupSymmetrization.groupPolynomial (rename seventhIndex P)
  have hQ : Q.totalDegree ≤ 2 :=
    (RoPEGroupSymmetrization.groupPolynomial_degree _).trans
      ((totalDegree_rename_le _ _).trans hP)
  have hp (h : Fin 6) : 0 < eval (fun g ↦ (seventhPositiveCounts h g : ℝ)) Q := by
    have hh := (seventh_group_sign P hs (seventhPositiveInput h)).1
    rw [seventhPositiveInput_count, seventh_positive_count_score] at hh
    exact hh (by norm_num)
  have hn (h : Fin 6) : eval (fun g ↦ (seventhNegativeCounts h g : ℝ)) Q ≤ 0 := by
    have hh := (seventh_group_sign P hs (seventhNegativeInput h)).2
    rw [seventhNegativeInput_count, seventh_negative_count_score] at hh
    exact hh (by norm_num)
  have he := QuadraticMomentCertificate.eval_sum_eq_of_moments
    (fun h g ↦ (seventhPositiveCounts h g : ℝ))
    (fun h g ↦ (seventhNegativeCounts h g : ℝ))
    seventh_count_moments.1 seventh_count_moments.2 Q hQ
  have hpos : 0 < ∑ h, eval (fun g ↦ (seventhPositiveCounts h g : ℝ)) Q :=
    Finset.sum_pos (fun h _ ↦ hp h) Finset.univ_nonempty
  have hneg : (∑ h, eval (fun g ↦ (seventhNegativeCounts h g : ℝ)) Q) ≤ 0 :=
    Finset.sum_nonpos (fun h _ ↦ hn h)
  linarith

theorem classifier_seven_pure_head_minimum : PureRoPEHStar 126 (classifier 7) = 3 := by
  classical
  have hu : PureRoPEHStar 126 (classifier 7) ≤ 3 :=
    Nat.find_min' (exists_pureRoPEComputable _) (pure_computable 7 (by norm_num))
  have hl : ¬ PureRoPEHStar 126 (classifier 7) ≤ 2 := by
    intro hh
    obtain ⟨P, hP, hs⟩ := thresholdDegLE_of_pureRoPEComputable
      (pureRoPEHStar_computable (classifier 7))
    exact classifier_seven_not_thresholdDegLE_two ⟨P, hP.trans hh, hs⟩
  omega

theorem classifier_seven_threshold_degree : thresholdDeg (classifier 7) = 3 := by
  classical
  have hc : ThresholdDegLE (classifier 7) 3 :=
    thresholdDegLE_of_pureRoPEComputable (pure_computable 7 (by norm_num))
  have hex : ∃ d, ThresholdDegLE (classifier 7) d := ⟨3, hc⟩
  have he : thresholdDeg (classifier 7) = Nat.find hex := by
    unfold thresholdDeg
    rw [dif_pos hex]
  rw [he]
  have hu := Nat.find_min' hex hc
  have hl : ¬ Nat.find hex ≤ 2 := by
    intro hh
    obtain ⟨P, hP, hs⟩ := Nat.find_spec hex
    exact classifier_seven_not_thresholdDegLE_two ⟨P, hP.trans hh, hs⟩
  omega

theorem classifier_seven_head_minima_lower :
    PureRoPEHStar 126 (classifier 7) = 3 ∧ 3 ≤ SharedHStar 126 (classifier 7) ∧
      StandardPureRoPEHStar 126 (classifier 7) = 3 ∧
      FreePureRoPEHStar 126 (classifier 7) = 3 := by
  have hp := classifier_seven_pure_head_minimum
  have hv := pureRoPEHStar_le_vanilla (classifier 7)
  rw [SharedHStar_eq_HStar, standardPureRoPEHStar_eq_scalar, freePureRoPEHStar_eq_scalar]
  exact ⟨hp, by simpa [hp] using hv, hp, hp⟩

end HeadComplexity.PureThreeReplicatedGrid
