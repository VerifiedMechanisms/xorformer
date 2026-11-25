import HeadComplexity.Results.PureSourceLinearApproximation
import HeadComplexity.Results.AffineFractionNormalForm

set_option linter.style.header false

/-!
# A three-head vanilla realization of the second replicated source

Adding the common weighted linear score to every denominator orients all
denominator slopes. On its zero hyperplane the score is unchanged. Away from
that hyperplane, an integer margin preserves the sign at replication two.
-/

namespace HeadComplexity.PureThreeReplicatedGrid

open scoped BigOperators

theorem linearScore_abs_le (q : Fin 18 → ℝ) (hq : ∀ g, |q g| ≤ 1) :
    |linearScore q| ≤ 63 := by
  calc
    |linearScore q| ≤ ∑ g, |(linearWeight g : ℝ) * q g| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ g : Fin 18, (linearWeight g : ℝ) := by
      apply Finset.sum_le_sum
      intro g _
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (hq g)
    _ = 63 := by exact_mod_cast linearWeight_sum

noncomputable def orientedScore (q : Fin 18 → ℝ) : ℝ :=
  ∑ h, numerator h q / (denominator h q + linearScore q)

theorem oriented_denominator_lower (h : Fin 3) (q : Fin 18 → ℝ)
    (hq : ∀ g, |q g| ≤ 1) : 131 ≤ denominator h q + linearScore q := by
  have h1 := (denominator_bounds h q hq).1
  have h2 := (abs_le.mp (linearScore_abs_le q hq)).1
  linarith

theorem oriented_score_error (q : Fin 18 → ℝ) (hq : ∀ g, |q g| ≤ 1) :
    |orientedScore q - 2 * linearScore q / (200 + linearScore q)| ≤
      (6 * (2 * |linearScore q| + 36) / 131) / (200 + linearScore q) := by
  have hL := (abs_le.mp (linearScore_abs_le q hq)).1
  have hB : 0 < 200 + linearScore q := by linarith
  have he : orientedScore q - 2 * linearScore q / (200 + linearScore q) =
      ∑ h, (numerator h q / (denominator h q + linearScore q) -
        numerator h q / (200 + linearScore q)) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, numerator_sum]
    rfl
  rw [he]
  calc
    |∑ h, (numerator h q / (denominator h q + linearScore q) -
        numerator h q / (200 + linearScore q))| ≤
        ∑ h, |numerator h q / (denominator h q + linearScore q) -
          numerator h q / (200 + linearScore q)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h, (6 * |numerator h q| / 131) / (200 + linearScore q) := by
      apply Finset.sum_le_sum
      intro h _
      have hl := oriented_denominator_lower h q hq
      have hd : 0 < denominator h q + linearScore q := by linarith
      obtain ⟨hlo, hup⟩ := denominator_bounds h q hq
      have hb : |200 - denominator h q| ≤ 6 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hid : numerator h q / (denominator h q + linearScore q) -
          numerator h q / (200 + linearScore q) =
          (numerator h q * (200 - denominator h q) /
            (denominator h q + linearScore q)) / (200 + linearScore q) := by
        field_simp
        ring
      rw [hid, abs_div, abs_div, abs_mul, abs_of_pos hB, abs_of_pos hd]
      apply div_le_div_of_nonneg_right _ hB.le
      apply (div_le_div_iff₀ hd (by norm_num : (0 : ℝ) < 131)).mpr
      have hn := abs_nonneg (numerator h q)
      have h1 := mul_le_mul_of_nonneg_left hb hn
      have h2 := mul_le_mul_of_nonneg_left hl hn
      nlinarith
    _ = (6 * (∑ h, |numerator h q|) / 131) / (200 + linearScore q) := by
      rw [← Finset.sum_div, ← Finset.sum_div, ← Finset.mul_sum]
    _ ≤ (6 * (2 * |linearScore q| + 36) / 131) / (200 + linearScore q) := by
      apply div_le_div_of_nonneg_right _ hB.le
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (numerator_abs_sum_le q hq) (by norm_num)) (by norm_num)

theorem oriented_score_pos_iff_linear_of_margin (q : Fin 18 → ℝ)
    (hq : ∀ g, |q g| ≤ 1) (hl : 1 ≤ |linearScore q|) :
    0 < orientedScore q ↔ 0 < linearScore q := by
  have hL := (abs_le.mp (linearScore_abs_le q hq)).1
  have hB : 0 < 200 + linearScore q := by linarith
  have he := oriented_score_error q hq
  have hb : |orientedScore q - 2 * linearScore q / (200 + linearScore q)| <
      2 * |linearScore q| / (200 + linearScore q) := by
    apply lt_of_le_of_lt he
    apply div_lt_div_of_pos_right _ hB
    nlinarith
  have ht : |2 * linearScore q / (200 + linearScore q)| =
      2 * |linearScore q| / (200 + linearScore q) := by
    rw [abs_div, abs_mul, abs_of_pos hB]
    norm_num
  rw [← ht] at hb
  have hs : (0 < orientedScore q ↔ 0 < 2 * linearScore q / (200 + linearScore q)) := by
    rcases le_total 0 (2 * linearScore q / (200 + linearScore q)) with hp | hn
    · rw [abs_of_nonneg hp] at hb
      have hpos := lt_of_le_of_lt (abs_nonneg
        (orientedScore q - 2 * linearScore q / (200 + linearScore q))) hb
      have := (abs_lt.mp hb).1
      constructor <;> intro <;> linarith
    · rw [abs_of_nonpos hn] at hb
      have := (abs_lt.mp hb).2
      constructor <;> intro <;> linarith
  rw [hs, div_pos_iff_of_pos_right hB, mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)]

theorem coordinate_two_abs_le (x : Fin 36 → Bool) (g : Fin 18) :
    |coordinate (m := 2) x g| ≤ 1 := by
  simp only [coordinate, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  cases h0 : x (finProdFinEquiv (g, (0 : Fin 2))) <;>
    cases h1 : x (finProdFinEquiv (g, (1 : Fin 2))) <;> norm_num [boolToReal, h0, h1]

theorem linearScore_two_integer (x : Fin 36 → Bool) :
    ∃ k : ℤ, linearScore (coordinate (m := 2) x) = k := by
  let K : ℕ := ∑ p : Fin 36, if x p then linearWeight (group (m := 2) p) else 0
  have hs := replicated_weighted_sum (m := 2) (by norm_num)
    (fun g ↦ (linearWeight g : ℝ)) x
  have hw : (∑ g : Fin 18, (linearWeight g : ℝ)) = 63 := by exact_mod_cast linearWeight_sum
  have hk : (∑ p : Fin 36, (linearWeight (group (m := 2) p) : ℝ) * boolToReal (x p)) =
      (K : ℝ) := by
    dsimp [K]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro p _
    cases x p <;> simp [boolToReal]
  have hs' : (K : ℝ) = linearScore (coordinate (m := 2) x) + 63 := by
    have hmul (a : ℝ) : 2 * a / (2 : ℝ) = a := by ring
    simpa only [Nat.cast_ofNat, hmul, hw, linearScore, hk] using hs
  refine ⟨(K : ℤ) - 63, ?_⟩
  push_cast
  linarith

theorem oriented_score_two_sign (x : Fin 36 → Bool) :
    0 < orientedScore (coordinate (m := 2) x) ↔ classifier 2 x = true := by
  have hq := coordinate_two_abs_le x
  simp only [classifier, decide_eq_true_eq]
  by_cases hz : linearScore (coordinate (m := 2) x) = 0
  · simp only [orientedScore, hz, add_zero, score]
  · have hm : 1 ≤ |linearScore (coordinate (m := 2) x)| := by
      obtain ⟨k, hk⟩ := linearScore_two_integer x
      rw [hk]
      have hk0 : k ≠ 0 := by
        intro h
        exact hz (hk.trans (by rw [h]; norm_num))
      have hab : (1 : ℤ) ≤ |k| := by
        rcases lt_or_gt_of_ne hk0 with hn | hp
        · rw [abs_of_neg hn]; omega
        · rw [abs_of_pos hp]; omega
      exact_mod_cast hab
    exact (oriented_score_pos_iff_linear_of_margin _ hq hm).trans
      (score_pos_iff_linear_of_margin _ hq hm).symm

noncomputable def orientedTwoFraction (h : Fin 3) : AffineFraction 36 where
  A p := u h (group (m := 2) p)
  b := -42
  C p := d h (group (m := 2) p) + (linearWeight (group (m := 2) p) : ℝ)
  d := 137

theorem oriented_slope_pos (h : Fin 3) (g : Fin 18) :
    0 < d h g + (linearWeight g : ℝ) := by
  dsimp [d, linearWeight]
  split_ifs <;> norm_num

theorem orientedTwoFraction_numerator (h : Fin 3) (x : Fin 36 → Bool) :
    (orientedTwoFraction h).numerator x = numerator h (coordinate (m := 2) x) := by
  have hs := replicated_weighted_sum (m := 2) (by norm_num) (u h) x
  rw [sum_u] at hs
  norm_num only [Nat.cast_ofNat, mul_div_cancel_left₀, show (2 : ℝ) ≠ 0 by norm_num] at hs
  dsimp [orientedTwoFraction, AffineFraction.numerator, numerator]
  linarith

theorem orientedTwoFraction_denominator (h : Fin 3) (x : Fin 36 → Bool) :
    (orientedTwoFraction h).denominator x =
      denominator h (coordinate (m := 2) x) + linearScore (coordinate (m := 2) x) := by
  have hd := replicated_weighted_sum (m := 2) (by norm_num) (d h) x
  rw [sum_d] at hd
  have hw := replicated_weighted_sum (m := 2) (by norm_num)
    (fun g ↦ (linearWeight g : ℝ)) x
  have hw' : (∑ g : Fin 18, (linearWeight g : ℝ)) = 63 := by exact_mod_cast linearWeight_sum
  rw [hw'] at hw
  norm_num only [Nat.cast_ofNat, mul_div_cancel_left₀, show (2 : ℝ) ≠ 0 by norm_num] at hd hw
  simp only [orientedTwoFraction, AffineFraction.denominator, add_mul, Finset.sum_add_distrib,
    denominator, linearScore]
  linarith

theorem classifier_two_vanilla_three : computableWithSharedHeadsN 36 3 (classifier 2) := by
  apply (computableWithSharedHeadsN_iff_affineFractionComputable 3 _).mpr
  refine ⟨orientedTwoFraction, 0, ?_, ?_⟩
  · intro h
    refine ⟨?_, Or.inl (fun p ↦ oriented_slope_pos h _), ?_⟩
    · intro x
      rw [orientedTwoFraction_denominator]
      have := oriented_denominator_lower h _ (coordinate_two_abs_le x)
      linarith
    · intro hz
      have hp := oriented_slope_pos h (group (m := 2) (0 : Fin 36))
      have he := hz (0 : Fin 36)
      change d h _ + (linearWeight _ : ℝ) = 0 at he
      linarith
  · intro x
    simp only [zero_add, AffineFraction.eval, orientedTwoFraction_numerator,
      orientedTwoFraction_denominator]
    exact oriented_score_two_sign x

end HeadComplexity.PureThreeReplicatedGrid
