import HeadComplexity.Results.PureSourceLinearApproximation

set_option linter.style.header false

/-!
# The third replicated source is again a linear threshold

A covariance estimate sharpens the coarse score approximation. The exact
head minimum is not monotone in the replication count: it is one at counts
one and three, but three at count two.
-/

namespace HeadComplexity.PureThreeReplicatedGrid

open scoped BigOperators

theorem three_pair_distance_bound (a b c : ℝ)
    (ha : |a| ≤ 3) (hb : |b| ≤ 3) (hc : |c| ≤ 3) :
    |a - b| + |a - c| + |b - c| ≤ 12 := by
  obtain ⟨hal, hau⟩ := abs_le.mp ha
  obtain ⟨hbl, hbu⟩ := abs_le.mp hb
  obtain ⟨hcl, hcu⟩ := abs_le.mp hc
  rcases le_total (a - b) 0 with hab | hab <;>
    rcases le_total (a - c) 0 with hac | hac <;>
    rcases le_total (b - c) 0 with hbc | hbc <;>
    simp_all only [abs_of_nonneg, abs_of_nonpos] <;> linarith

theorem reciprocal_denominator_gap (q : Fin 18 → ℝ)
    (hq : ∀ g, |q g| ≤ 1) (i j : Fin 3) :
    |1 / denominator i q - 1 / denominator j q| ≤ 12 / (194 * 194) := by
  obtain ⟨hil, hiu⟩ := denominator_bounds i q hq
  obtain ⟨hjl, hju⟩ := denominator_bounds j q hq
  have hi : 0 < denominator i q := by linarith
  have hj : 0 < denominator j q := by linarith
  have he : 1 / denominator i q - 1 / denominator j q =
      (denominator j q - denominator i q) / (denominator i q * denominator j q) := by
    field_simp
  rw [he, abs_div, abs_of_pos (mul_pos hi hj)]
  have hd : |denominator j q - denominator i q| ≤ 12 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  apply (div_le_div_iff₀ (mul_pos hi hj) (by norm_num : (0 : ℝ) < 194 * 194)).mpr
  nlinarith [mul_nonneg (by linarith : 0 ≤ denominator i q - 194)
    (by linarith : 0 ≤ denominator j q - 194)]

noncomputable def balancedLinearScore (q : Fin 18 → ℝ) : ℝ :=
  (2 * linearScore q / 3) * ∑ i, 1 / denominator i q

theorem score_covariance_identity (q : Fin 18 → ℝ) :
    score q - balancedLinearScore q = (2 / 3 : ℝ) *
      ((firstSum 0 q - firstSum 1 q) * (1 / denominator 0 q - 1 / denominator 1 q) +
       (firstSum 0 q - firstSum 2 q) * (1 / denominator 0 q - 1 / denominator 2 q) +
       (firstSum 1 q - firstSum 2 q) * (1 / denominator 1 q - 1 / denominator 2 q)) := by
  norm_num [score, balancedLinearScore, numerator_firstSum, linearScore_firstSum,
    Fin.sum_univ_succ]
  ring

theorem score_covariance_bound (q : Fin 18 → ℝ) (hq : ∀ g, |q g| ≤ 1) :
    |score q - balancedLinearScore q| ≤ 96 / (194 * 194) := by
  rw [score_covariance_identity, abs_mul]
  norm_num only [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  have hd := three_pair_distance_bound (firstSum 0 q) (firstSum 1 q) (firstSum 2 q)
    (firstSum_abs_le 0 q hq) (firstSum_abs_le 1 q hq) (firstSum_abs_le 2 q hq)
  have hterm (i j : Fin 3) :
      |(firstSum i q - firstSum j q) * (1 / denominator i q - 1 / denominator j q)| ≤
        |firstSum i q - firstSum j q| * (12 / (194 * 194)) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (reciprocal_denominator_gap q hq i j) (abs_nonneg _)
  have h01 := hterm 0 1
  have h02 := hterm 0 2
  have h12 := hterm 1 2
  have ht := abs_add_le
    ((firstSum 0 q - firstSum 1 q) * (1 / denominator 0 q - 1 / denominator 1 q) +
      (firstSum 0 q - firstSum 2 q) * (1 / denominator 0 q - 1 / denominator 2 q))
    ((firstSum 1 q - firstSum 2 q) * (1 / denominator 1 q - 1 / denominator 2 q))
  have hs := abs_add_le
    ((firstSum 0 q - firstSum 1 q) * (1 / denominator 0 q - 1 / denominator 1 q))
    ((firstSum 0 q - firstSum 2 q) * (1 / denominator 0 q - 1 / denominator 2 q))
  nlinarith

theorem balancedLinearScore_abs_lower (q : Fin 18 → ℝ) (hq : ∀ g, |q g| ≤ 1) :
    2 * |linearScore q| / 206 ≤ |balancedLinearScore q| := by
  have hi (i : Fin 3) : (1 : ℝ) / 206 ≤ 1 / denominator i q := by
    obtain ⟨hl, hu⟩ := denominator_bounds i q hq
    exact one_div_le_one_div_of_le (by linarith) hu
  have hs : (3 : ℝ) / 206 ≤ ∑ i, 1 / denominator i q := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hi i)
    norm_num at h ⊢
    exact h
  rw [balancedLinearScore, abs_mul, abs_div, abs_mul,
    abs_of_nonneg (by linarith : 0 ≤ ∑ i, 1 / denominator i q)]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg (linearScore q))]

theorem score_pos_iff_linear_of_third_margin (q : Fin 18 → ℝ)
    (hq : ∀ g, |q g| ≤ 1) (hl : (1 : ℝ) / 3 ≤ |linearScore q|) :
    0 < score q ↔ 0 < linearScore q := by
  have he := score_covariance_bound q hq
  have hb := balancedLinearScore_abs_lower q hq
  have hstrict : |score q - balancedLinearScore q| < |balancedLinearScore q| := by
    nlinarith
  have hnonneg := abs_nonneg (score q - balancedLinearScore q)
  have hsign : 0 < score q ↔ 0 < balancedLinearScore q := by
    rcases le_total 0 (balancedLinearScore q) with hp | hn
    · rw [abs_of_nonneg hp] at hstrict
      have h := (abs_lt.mp hstrict).1
      constructor <;> intro <;> linarith
    · rw [abs_of_nonpos hn] at hstrict
      have h := (abs_lt.mp hstrict).2
      constructor <;> intro <;> linarith
  have hsum : 0 < ∑ i, 1 / denominator i q := by
    apply Finset.sum_pos
    · intro i _
      apply one_div_pos.mpr
      have h := (denominator_bounds i q hq).1
      linarith
    · exact Finset.univ_nonempty
  rw [hsign, balancedLinearScore, mul_pos_iff_of_pos_right hsum,
    div_pos_iff_of_pos_right (by norm_num : (0 : ℝ) < 3),
    mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)]

theorem coordinate_three_abs_le (x : Fin 54 → Bool) (g : Fin 18) :
    |coordinate (m := 3) x g| ≤ 1 := by
  norm_num [coordinate, Fin.sum_univ_succ]
  cases h0 : x (finProdFinEquiv (g, (0 : Fin 3))) <;>
    cases h1 : x (finProdFinEquiv (g, (1 : Fin 3))) <;>
    cases h2 : x (finProdFinEquiv (g, (2 : Fin 3))) <;>
    norm_num [boolToReal, h0, h1, h2]

theorem linearScore_three_centered (x : Fin 54 → Bool) :
    linearScore (coordinate (m := 3) x) =
      2 * (∑ p : Fin 54, (linearWeight (group (m := 3) p) : ℝ) * boolToReal (x p)) / 3 - 63 := by
  have hs := replicated_weighted_sum (m := 3) (by norm_num)
    (fun g ↦ (linearWeight g : ℝ)) x
  have hw : (∑ g : Fin 18, (linearWeight g : ℝ)) = 63 := by
    exact_mod_cast linearWeight_sum
  have he : (∑ p : Fin 54, (2 * (linearWeight (group (m := 3) p) : ℝ) / 3) *
      boolToReal (x p)) =
      2 * (∑ p : Fin 54, (linearWeight (group (m := 3) p) : ℝ) * boolToReal (x p)) / 3 := by
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hs' : 2 * (∑ p : Fin 54, (linearWeight (group (m := 3) p) : ℝ) *
      boolToReal (x p)) / 3 = linearScore (coordinate (m := 3) x) + 63 := by
    simpa only [Nat.cast_ofNat, he, hw, linearScore] using hs
  linarith

theorem linearScore_three_margin (x : Fin 54 → Bool) :
    (1 : ℝ) / 3 ≤ |linearScore (coordinate (m := 3) x)| := by
  let K : ℕ := ∑ p : Fin 54, if x p then linearWeight (group (m := 3) p) else 0
  have hk : (∑ p : Fin 54, (linearWeight (group (m := 3) p) : ℝ) * boolToReal (x p)) =
      (K : ℝ) := by
    dsimp [K]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro p _
    cases x p <;> simp [boolToReal]
  rw [linearScore_three_centered, hk]
  by_cases hK : K ≤ 94
  · have hK' : (K : ℝ) ≤ 94 := by exact_mod_cast hK
    rw [abs_of_nonpos (by linarith : 2 * (K : ℝ) / 3 - 63 ≤ 0)]
    linarith
  · have hK' : 95 ≤ (K : ℝ) := by exact_mod_cast (by omega : 95 ≤ K)
    rw [abs_of_nonneg (by linarith : 0 ≤ 2 * (K : ℝ) / 3 - 63)]
    linarith

theorem classifier_three_linear (x : Fin 54 → Bool) :
    classifier 3 x = true ↔ 0 < linearScore (coordinate (m := 3) x) := by
  simp only [classifier, decide_eq_true_eq]
  exact score_pos_iff_linear_of_third_margin _ (coordinate_three_abs_le x)
    (linearScore_three_margin x)

theorem classifier_three_isLTF : isLTF (classifier 3) := by
  refine ⟨-63, fun p ↦ 2 * (linearWeight (group (m := 3) p) : ℝ) / 3, fun x ↦ ?_⟩
  rw [classifier_three_linear, linearScore_three_centered]
  have he : (∑ p : Fin 54, (2 * (linearWeight (group (m := 3) p) : ℝ) / 3) *
      boolToReal (x p)) =
      2 * (∑ p : Fin 54, (linearWeight (group (m := 3) p) : ℝ) * boolToReal (x p)) / 3 := by
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he]
  constructor <;> intro h <;> linarith

theorem classifier_three_head_minima :
    PureRoPEHStar 54 (classifier 3) = 1 ∧ SharedHStar 54 (classifier 3) = 1 ∧
      StandardPureRoPEHStar 54 (classifier 3) = 1 ∧
      FreePureRoPEHStar 54 (classifier 3) = 1 := by
  have hv : HStar 54 (classifier 3) = 1 := by
    apply (HStar_eq_one_iff _).mpr
    refine ⟨?_, classifier_three_isLTF⟩
    intro hc
    have hh := hc (fun _ ↦ true) (fun _ ↦ false)
    rw [classifier_all_true 3 (by norm_num), classifier_all_false 3 (by norm_num)] at hh
    cases hh
  have hvle : HStar 54 (classifier 3) ≤ 3 := by omega
  have hp := pureRoPEHStar_eq_vanilla_of_vanilla_le_three (classifier 3) hvle
  rw [hv] at hp
  rw [SharedHStar_eq_HStar, standardPureRoPEHStar_eq_scalar, freePureRoPEHStar_eq_scalar]
  exact ⟨hp, hv, hp, hp⟩

end HeadComplexity.PureThreeReplicatedGrid
