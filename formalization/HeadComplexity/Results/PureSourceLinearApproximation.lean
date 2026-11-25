import HeadComplexity.Results.PureThreeReplicatedGrid
import HeadComplexity.Results.RoPEBoundaryCases

set_option linter.style.header false

/-!
# The first replicated source is a nonconstant linear threshold function

A uniform score estimate explains why the separation family need not separate
at small replication counts.  At replication one its exact classifier is a
weighted majority with weights four and three on the two halves of each block.
-/

namespace HeadComplexity.PureThreeReplicatedGrid

open scoped BigOperators

def linearWeight (g : Fin 18) : ℕ := if g.val % 6 < 3 then 4 else 3

noncomputable def linearScore (q : Fin 18 → ℝ) : ℝ :=
  ∑ g, (linearWeight g : ℝ) * q g

noncomputable def firstSum (h : Fin 3) (q : Fin 18 → ℝ) : ℝ :=
  ∑ g, if g.val % 6 = h.val then q g else 0

theorem firstSum_abs_le (h : Fin 3) (q : Fin 18 → ℝ)
    (hq : ∀ g, |q g| ≤ 1) : |firstSum h q| ≤ 3 := by
  calc
    |firstSum h q| ≤ ∑ g, |if g.val % 6 = h.val then q g else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ g : Fin 18, if g.val % 6 = h.val then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro g _
      split_ifs <;> simp_all
    _ = 3 := by
      fin_cases h <;> simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] <;> norm_num

theorem numerator_firstSum (h : Fin 3) (q : Fin 18 → ℝ) :
    numerator h q = 2 * (∑ g, q g) + 2 * firstSum h q := by
  simp only [numerator, firstSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hgh : g.val % 6 = h.val
  · simp [u, hgh]
    ring
  · simp [u, hgh]

theorem linearScore_firstSum (q : Fin 18 → ℝ) :
    linearScore q = 3 * (∑ g, q g) + ∑ h : Fin 3, firstSum h q := by
  norm_num [linearScore, linearWeight, firstSum, Fin.sum_univ_succ]
  ring

theorem numerator_sum (q : Fin 18 → ℝ) :
    (∑ h, numerator h q) = 2 * linearScore q := by
  simp_rw [numerator_firstSum]
  rw [linearScore_firstSum]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  ring

theorem numerator_abs_sum_le (q : Fin 18 → ℝ) (hq : ∀ g, |q g| ≤ 1) :
    (∑ h, |numerator h q|) ≤ 2 * |linearScore q| + 36 := by
  have hfirst : |∑ h, firstSum h q| ≤ 9 := by
    calc
      |∑ h, firstSum h q| ≤ ∑ h, |firstSum h q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin 3, (3 : ℝ) := Finset.sum_le_sum fun h _ ↦ firstSum_abs_le h q hq
      _ = 9 := by norm_num
  have ht : 3 * |∑ g, q g| ≤ |linearScore q| + 9 := by
    have he : 3 * (∑ g, q g) = linearScore q - ∑ h, firstSum h q := by
      rw [linearScore_firstSum]
      ring
    have hb := abs_sub (linearScore q) (∑ h, firstSum h q)
    rw [← he, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at hb
    linarith
  calc
    (∑ h, |numerator h q|) ≤ ∑ h : Fin 3, (2 * |∑ g, q g| + 6) := by
      apply Finset.sum_le_sum
      intro h _
      rw [numerator_firstSum]
      have ha := abs_add_le (2 * ∑ g, q g) (2 * firstSum h q)
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ha
      have hb := firstSum_abs_le h q hq
      linarith
    _ ≤ 2 * |linearScore q| + 36 := by
      norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat]
      linarith

theorem score_linear_error (q : Fin 18 → ℝ) (hq : ∀ g, |q g| ≤ 1) :
    |score q - linearScore q / 100| ≤
      6 * (2 * |linearScore q| + 36) / (200 * 194) := by
  have he : score q - linearScore q / 100 =
      ∑ h, (numerator h q / denominator h q - numerator h q / 200) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, numerator_sum]
    dsimp [score]
    ring
  rw [he]
  calc
    |∑ h, (numerator h q / denominator h q - numerator h q / 200)| ≤
        ∑ h, |numerator h q / denominator h q - numerator h q / 200| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h, (6 * |numerator h q| / (200 * 194)) := by
      apply Finset.sum_le_sum
      intro h _
      obtain ⟨hl, hu⟩ := denominator_bounds h q hq
      have hd : 0 < denominator h q := by linarith
      have hb : |200 - denominator h q| ≤ 6 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hid : numerator h q / denominator h q - numerator h q / 200 =
          numerator h q * (200 - denominator h q) / (200 * denominator h q) := by
        field_simp
      rw [hid, abs_div, abs_mul, abs_of_pos (mul_pos (by norm_num) hd)]
      apply (div_le_div_iff₀ (mul_pos (by norm_num) hd) (by norm_num)).mpr
      have hn := abs_nonneg (numerator h q)
      have h1 := mul_le_mul_of_nonneg_left hb hn
      have h2 := mul_le_mul_of_nonneg_left hl hn
      nlinarith
    _ = 6 * (∑ h, |numerator h q|) / (200 * 194) := by
      rw [← Finset.sum_div, ← Finset.mul_sum]
    _ ≤ 6 * (2 * |linearScore q| + 36) / (200 * 194) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (numerator_abs_sum_le q hq) (by norm_num)) (by norm_num)

theorem score_pos_iff_linear_of_margin (q : Fin 18 → ℝ)
    (hq : ∀ g, |q g| ≤ 1) (hl : 1 ≤ |linearScore q|) :
    0 < score q ↔ 0 < linearScore q := by
  have he := score_linear_error q hq
  have hb : |score q - linearScore q / 100| < |linearScore q| / 100 := by
    apply lt_of_le_of_lt he
    nlinarith
  rcases le_total 0 (linearScore q) with hp | hn
  · rw [abs_of_nonneg hp] at hl hb
    have hs := (abs_lt.mp hb).1
    constructor <;> intro <;> linarith
  · rw [abs_of_nonpos hn] at hl hb
    have hs := (abs_lt.mp hb).2
    constructor <;> intro <;> linarith

theorem coordinate_one (x : Fin 18 → Bool) (g : Fin 18) :
    coordinate (m := 1) x g = 2 * boolToReal (x g) - 1 := by
  simp [coordinate, finProdFinEquiv]

theorem linearWeight_sum : (∑ g : Fin 18, linearWeight g) = 63 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [linearWeight]

theorem linearScore_centered (x : Fin 18 → Bool) :
    linearScore (coordinate (m := 1) x) =
      2 * ((∑ g : Fin 18, if x g then linearWeight g else 0 : ℕ) : ℝ) - 63 := by
  simp only [linearScore, coordinate_one, mul_sub, mul_one, Finset.sum_sub_distrib]
  have hw : (∑ g : Fin 18, (linearWeight g : ℝ)) = 63 := by
    exact_mod_cast linearWeight_sum
  rw [hw]
  congr 1
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  cases x g
  · simp [boolToReal]
  · simp [boolToReal]
    ring

theorem linearScore_one_margin (x : Fin 18 → Bool) :
    1 ≤ |linearScore (coordinate (m := 1) x)| := by
  rw [linearScore_centered]
  let k : ℕ := ∑ g : Fin 18, if x g then linearWeight g else 0
  change 1 ≤ |2 * (k : ℝ) - 63|
  by_cases hk : k ≤ 31
  · have hk' : (k : ℝ) ≤ 31 := by exact_mod_cast hk
    rw [abs_of_nonpos (by linarith : 2 * (k : ℝ) - 63 ≤ 0)]
    linarith
  · have hk' : 32 ≤ (k : ℝ) := by exact_mod_cast (by omega : 32 ≤ k)
    rw [abs_of_nonneg (by linarith : 0 ≤ 2 * (k : ℝ) - 63)]
    linarith

theorem classifier_one_linear (x : Fin 18 → Bool) :
    classifier 1 x = true ↔ 0 < linearScore (coordinate (m := 1) x) := by
  simp only [classifier, decide_eq_true_eq]
  apply score_pos_iff_linear_of_margin
  · intro g
    rw [coordinate_one]
    cases hx : x g <;> norm_num [boolToReal, hx]
  · exact linearScore_one_margin x

theorem classifier_one_isLTF : isLTF (classifier 1) := by
  refine ⟨-63, fun g ↦ 2 * (linearWeight g : ℝ), fun x ↦ ?_⟩
  rw [classifier_one_linear]
  have he : -63 + ∑ g, 2 * (linearWeight g : ℝ) * boolToReal (x g) =
      linearScore (coordinate (m := 1) x) := by
    simp only [linearScore, coordinate_one, mul_sub, mul_one, Finset.sum_sub_distrib]
    have hw : (∑ g : Fin 18, (linearWeight g : ℝ)) = 63 := by
      exact_mod_cast linearWeight_sum
    rw [hw]
    have hs : (∑ g, 2 * (linearWeight g : ℝ) * boolToReal (x g)) =
        ∑ g, (linearWeight g : ℝ) * (2 * boolToReal (x g)) := by
      apply Finset.sum_congr rfl
      intro g _
      ring
    rw [hs]
    ring
  rw [he]

theorem classifier_one_head_minima :
    PureRoPEHStar 18 (classifier 1) = 1 ∧ SharedHStar 18 (classifier 1) = 1 ∧
      StandardPureRoPEHStar 18 (classifier 1) = 1 ∧
      FreePureRoPEHStar 18 (classifier 1) = 1 := by
  have hv : HStar 18 (classifier 1) = 1 := by
    apply (HStar_eq_one_iff _).mpr
    refine ⟨?_, classifier_one_isLTF⟩
    intro hc
    have hh := hc (fun _ ↦ true) (fun _ ↦ false)
    rw [classifier_all_true 1 (by norm_num), classifier_all_false 1 (by norm_num)] at hh
    cases hh
  have hvle : HStar 18 (classifier 1) ≤ 3 := by omega
  have hp := pureRoPEHStar_eq_vanilla_of_vanilla_le_three (classifier 1) hvle
  rw [hv] at hp
  rw [SharedHStar_eq_HStar, standardPureRoPEHStar_eq_scalar, freePureRoPEHStar_eq_scalar]
  exact ⟨hp, hv, hp, hp⟩

end HeadComplexity.PureThreeReplicatedGrid
