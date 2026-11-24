import HeadComplexity.Results.PureRoPEReplication

set_option linter.style.header false

/-!
# Exact integer-lattice tie removal for the replicated pure family

The unshifted cubic has denominator dividing A*m^3 on every Boolean input.
A negative readout bias of size 1/(16*A*m^3) therefore removes all ties while
preserving the full Boolean truth table. No enumeration of the replicated
cube or evaluation of its enormous dimension is used.
-/

namespace HeadComplexity.PureRoPEReplicationStrict

noncomputable section

open PureRoPECenteredConstruction PureRoPEReplication
open scoped BigOperators

def W : ℤ := 32 * 1000000000

def integerS (h : Fin 3) (i : Fin 14) : ℤ := (i.val + 1) ^ h.val

def integerB (h : Fin 3) (i : Fin 14) : ℤ :=
  32 * (i.val + 1) ^ (h.val + 3) - 2 ^ (2 - h.val) * 15 ^ (h.val + 3)

theorem baseS_eq (h : Fin 3) (i : Fin 14) :
    baseS h i = (integerS h i : ℝ) / 10000 := by
  simp [baseS, integerS]

theorem baseB_eq (h : Fin 3) (i : Fin 14) :
    baseB h i = (integerB h i : ℝ) / W := by
  fin_cases h <;> norm_num [baseB, integerB, W] <;> ring

def integerSpin (b : Bool) : ℤ := if b then 1 else -1

theorem integerSpin_cast (b : Bool) : (integerSpin b : ℝ) = spin b := by
  cases b <;> norm_num [integerSpin, spin]

def integerMean {m : ℕ} (x : Fin (14 * m) → Bool) (i : Fin 14) : ℤ :=
  ∑ r : Fin m, integerSpin (x (finProdFinEquiv (i, r)))

theorem means_eq {m : ℕ} (x : Fin (14 * m) → Bool) (i : Fin 14) :
    means x i = (integerMean x i : ℝ) / m := by
  simp [means, integerMean, integerSpin_cast]

def integerNumerator {m : ℕ} (x : Fin (14 * m) → Bool) (h : Fin 3) : ℤ :=
  ∑ i, integerS h i * integerMean x i

def integerDenominator {m : ℕ} (x : Fin (14 * m) → Bool) (h : Fin 3) : ℤ :=
  W * m + ∑ i, integerB h i * integerMean x i

theorem numerator_eq {m : ℕ} (x : Fin (14 * m) → Bool) (h : Fin 3) :
    numerator x h = (integerNumerator x h : ℝ) / (10000 * m) := by
  simp only [numerator, baseS_eq, means_eq, integerNumerator, Int.cast_sum, Int.cast_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem denominator_eq {m : ℕ} (hm : 0 < m) (x : Fin (14 * m) → Bool) (h : Fin 3) :
    denominator x h = (integerDenominator x h : ℝ) / ((W : ℝ) * m) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hw : (W : ℝ) ≠ 0 := by norm_num [W]
  simp only [denominator, baseB_eq, means_eq, integerDenominator,
    Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_sum]
  rw [add_div, div_self (mul_ne_zero hw hm'), Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

def integerCleared {m : ℕ} (x : Fin (14 * m) → Bool) : ℤ :=
  integerNumerator x 0 * integerDenominator x 1 * integerDenominator x 2 +
    integerNumerator x 1 * integerDenominator x 0 * integerDenominator x 2 +
    integerNumerator x 2 * integerDenominator x 0 * integerDenominator x 1

def scale (m : ℕ) : ℝ := 10000 * (W : ℝ) ^ 2 * (m : ℝ) ^ 3

theorem scale_positive {m : ℕ} (hm : 0 < m) : 0 < scale m := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  unfold scale W
  positivity

theorem scaled_cubic_integer {m : ℕ} (hm : 0 < m) (x : Fin (14 * m) → Bool) :
    scale m * clearedScore 0 x = (integerCleared x : ℝ) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hw : (W : ℝ) ≠ 0 := by norm_num [W]
  simp only [clearedScore, ThreeHeadCubicFace.cleared, zero_mul, zero_add,
    numerator_eq, denominator_eq hm, integerCleared, Int.cast_add, Int.cast_mul, scale]
  field_simp

theorem means_abs_le_one {m : ℕ} (hm : 0 < m) (x : Fin (14 * m) → Bool) (i : Fin 14) :
    |means x i| ≤ 1 := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hp (b : Bool) : spin b ≤ 1 := by cases b <;> norm_num [spin]
  have hn (b : Bool) : -1 ≤ spin b := by cases b <;> norm_num [spin]
  have hsumP := Finset.sum_le_sum (s := Finset.univ)
    (fun (r : Fin m) _ ↦ hp (x (finProdFinEquiv (i, r))))
  have hsumN := Finset.sum_le_sum (s := Finset.univ)
    (fun (r : Fin m) _ ↦ hn (x (finProdFinEquiv (i, r))))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, mul_neg] at hsumP hsumN
  rw [abs_le]
  unfold means
  constructor
  · apply (le_div_iff₀ hm').mpr
    simpa using hsumN
  · apply (div_le_iff₀ hm').mpr
    simpa using hsumP

theorem sum_abs_baseB_lt_one (h : Fin 3) : ∑ i, |baseB h i| < 1 := by
  apply lt_trans _ (base_sum h)
  apply Finset.sum_lt_sum
  · intro i _
    exact (base_mass h i).le
  · exact ⟨0, Finset.mem_univ _, base_mass h 0⟩

theorem denominator_lt_two {m : ℕ} (hm : 0 < m) (x : Fin (14 * m) → Bool)
    (h : Fin 3) : denominator x h < 2 := by
  have hsum : (∑ i, baseB h i * means x i) ≤ ∑ i, |baseB h i| := by
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ |baseB h i * means x i| := le_abs_self _
      _ = |baseB h i| * |means x i| := abs_mul _ _
      _ ≤ |baseB h i| * 1 := mul_le_mul_of_nonneg_left (means_abs_le_one hm x i) (abs_nonneg _)
      _ = _ := mul_one _
  have hh := sum_abs_baseB_lt_one h
  unfold denominator
  linarith

def denominatorProduct {m : ℕ} (x : Fin (14 * m) → Bool) : ℝ :=
  denominator x 0 * denominator x 1 * denominator x 2

theorem product_positive {m : ℕ} (hm : 0 < m) (x : Fin (14 * m) → Bool) :
    0 < denominatorProduct x :=
  mul_pos (mul_pos (denominator_positive hm x 0) (denominator_positive hm x 1))
    (denominator_positive hm x 2)

theorem product_lt_eight {m : ℕ} (hm : 0 < m) (x : Fin (14 * m) → Bool) :
    denominatorProduct x < 8 := by
  have h0 := denominator_positive hm x 0
  have h1 := denominator_positive hm x 1
  have h2 := denominator_positive hm x 2
  have g0 := denominator_lt_two hm x 0
  have g1 := denominator_lt_two hm x 1
  have g2 := denominator_lt_two hm x 2
  have h01 : denominator x 0 * denominator x 1 < 4 := by
    calc
      _ < 2 * denominator x 1 := mul_lt_mul_of_pos_right g0 h1
      _ < 2 * 2 := mul_lt_mul_of_pos_left g1 (by norm_num)
      _ = 4 := by norm_num
  unfold denominatorProduct
  calc
    _ < 4 * denominator x 2 := mul_lt_mul_of_pos_right h01 h2
    _ < 4 * 2 := mul_lt_mul_of_pos_left g2 (by norm_num)
    _ = 8 := by norm_num

def epsilon (m : ℕ) : ℝ := 1 / (16 * scale m)

theorem epsilon_positive {m : ℕ} (hm : 0 < m) : 0 < epsilon m := by
  unfold epsilon
  exact div_pos (by norm_num) (mul_pos (by norm_num) (scale_positive hm))

theorem bias_eq (m : ℕ) : bias m = -epsilon m := by
  unfold bias epsilon scale W
  push_cast
  ring

theorem score_bias {m : ℕ} (x : Fin (14 * m) → Bool) :
    score (bias m) x = score 0 x - epsilon m := by
  rw [bias_eq]
  simp only [score, zero_add]
  ring

theorem positive_cubic_gap {m : ℕ} (hm : 0 < m) (x : Fin (14 * m) → Bool)
    (hF : 0 < clearedScore 0 x) : 1 / scale m ≤ clearedScore 0 x := by
  have hI : (0 : ℤ) < integerCleared x := by
    have hp : (0 : ℝ) < (integerCleared x : ℝ) := by
      rw [← scaled_cubic_integer hm]
      exact mul_pos (scale_positive hm) hF
    exact_mod_cast hp
  have hI' : (1 : ℤ) ≤ integerCleared x := by omega
  have hI'' : (1 : ℝ) ≤ (integerCleared x : ℝ) := by exact_mod_cast hI'
  apply (div_le_iff₀ (scale_positive hm)).mpr
  rw [mul_comm, scaled_cubic_integer hm]
  exact hI''

theorem positive_score_gap {m : ℕ} (hm : 0 < m) (x : Fin (14 * m) → Bool)
    (hF : 0 < clearedScore 0 x) : 2 * epsilon m < score 0 x := by
  have hp := product_positive hm x
  have hp8 := product_lt_eight hm x
  have hs := scale_positive hm
  have hsmall : (2 * epsilon m) * denominatorProduct x < 1 / scale m := by
    calc
      _ = (2 * denominatorProduct x) / (16 * scale m) := by unfold epsilon; ring
      _ < 16 / (16 * scale m) :=
        div_lt_div_of_pos_right (by linarith) (mul_pos (by norm_num) hs)
      _ = 1 / scale m := by field_simp
  have hlt := hsmall.trans_le (positive_cubic_gap hm x hF)
  have he : clearedScore 0 x = denominatorProduct x * score 0 x := clearedScore_eq hm 0 x
  rw [he, mul_comm (2 * epsilon m)] at hlt
  exact (mul_lt_mul_iff_right₀ hp).mp (by simpa [mul_comm] using hlt)

theorem full_cube_strict {m : ℕ} (hm : 0 < m) (x : Fin (14 * m) → Bool) :
    (0 < score (bias m) x ↔ 0 < clearedScore 0 x) ∧
      epsilon m ≤ |score (bias m) x| := by
  have he := score_bias x
  have heps := epsilon_positive hm
  by_cases hF : 0 < clearedScore 0 x
  · have hg := positive_score_gap hm x hF
    have hp : 0 < score (bias m) x := by linarith
    constructor
    · exact ⟨fun _ ↦ hF, fun _ ↦ hp⟩
    · rw [abs_of_pos hp]
      linarith
  · have hn : clearedScore 0 x ≤ 0 := le_of_not_gt hF
    have hprod := product_positive hm x
    have hc : clearedScore 0 x = denominatorProduct x * score 0 x := clearedScore_eq hm 0 x
    have hs : score 0 x ≤ 0 := by
      rw [hc] at hn
      by_contra hs
      have hp := mul_pos hprod (lt_of_not_ge hs)
      linarith
    have hb : score (bias m) x < 0 := by linarith
    constructor
    · constructor <;> intro h <;> linarith
    · rw [abs_of_neg hb]
      linarith

def unshiftedFunction {m : ℕ} (x : Fin (14 * m) → Bool) : Bool := by
  classical
  exact decide (0 < clearedScore 0 x)

theorem biasedFunction_eq_unshifted {m : ℕ} (hm : 0 < m) :
    PureRoPEReplication.function (bias m) = (unshiftedFunction : (Fin (14 * m) → Bool) → Bool) := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simpa [PureRoPEReplication.function, unshiftedFunction] using (full_cube_strict hm x).1

theorem unshifted_pure_three {m : ℕ} (hm : 0 < m) :
    pureRoPEComputable (14 * m) 3 (unshiftedFunction (m := m)) := by
  rw [← biasedFunction_eq_unshifted hm]
  exact pureRoPEComputable_three hm (bias m)

def explicitUnshiftedFunction : (Fin (14 * replicationCount) → Bool) → Bool :=
  unshiftedFunction

theorem explicitUnshiftedFunction_pure_three :
    pureRoPEComputable (14 * replicationCount) 3 explicitUnshiftedFunction :=
  unshifted_pure_three replicationCount_positive

theorem explicitUnshiftedFunction_eq :
    PureRoPEReplication.explicitFunction = explicitUnshiftedFunction :=
  biasedFunction_eq_unshifted replicationCount_positive

theorem explicitUnshiftedFunction_margin (x : Fin (14 * replicationCount) → Bool) :
    epsilon replicationCount ≤ |score (bias replicationCount) x| :=
  (full_cube_strict replicationCount_positive x).2

theorem explicitUnshiftedFunction_thresholdDegLE :
    ThresholdDegLE explicitUnshiftedFunction 3 :=
  thresholdDegLE_of_pureRoPEComputable explicitUnshiftedFunction_pure_three

theorem pureAtoms_query_weight {m : ℕ} (hm : 0 < m) (h : Fin 3) :
    (pureAtoms hm h).γ = 1 - ∑ i, baseS h i := by
  simp only [pureAtoms, replicatedAtom, atom, sum_replicate hm]

theorem pureAtoms_query_numerator {m : ℕ} (hm : 0 < m) (h : Fin 3) :
    (pureAtoms hm h).η = - ∑ i, baseB h i := by
  simp only [pureAtoms, replicatedAtom, atom, zero_mul, one_mul, zero_add, zero_sub,
    sum_replicate hm]

theorem pureAtoms_token_weights {m : ℕ} (hm : 0 < m) (h : Fin 3)
    (i : Fin 14) (r : Fin m) :
    (pureAtoms hm h).a (finProdFinEquiv (i, r)) = (baseS h i - baseB h i) / m ∧
      (pureAtoms hm h).b (finProdFinEquiv (i, r)) = (baseS h i + baseB h i) / m := by
  simp only [pureAtoms, replicatedAtom, atom, replicate, Equiv.symm_apply_apply]
  constructor <;> ring

theorem pureAtoms_values {m : ℕ} (hm : 0 < m) (h : Fin 3) :
    (pureAtoms hm h).v₀ = -1 ∧ (pureAtoms hm h).v₁ = 1 := by
  norm_num [pureAtoms, replicatedAtom, atom]

theorem means_constant {m : ℕ} (hm : 0 < m) (b : Bool) (i : Fin 14) :
    means (fun _ : Fin (14 * m) ↦ b) i = spin b := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [means, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem sum_baseS_positive (h : Fin 3) : 0 < ∑ i, baseS h i := by
  apply Finset.sum_pos
  · intro i _
    exact lt_of_le_of_lt (abs_nonneg _) (base_mass h i)
  · exact Finset.univ_nonempty

theorem unshifted_all_true {m : ℕ} (hm : 0 < m) :
    unshiftedFunction (fun _ : Fin (14 * m) ↦ true) = true := by
  have hs : 0 < score 0 (fun _ : Fin (14 * m) ↦ true) := by
    unfold score
    simp only [zero_add]
    apply Finset.sum_pos
    · intro h _
      apply div_pos
      · simpa only [means_constant hm, spin, ite_true, mul_one] using sum_baseS_positive h
      · exact denominator_positive hm _ h
    · exact Finset.univ_nonempty
  have hf : 0 < clearedScore 0 (fun _ : Fin (14 * m) ↦ true) := by
    rw [clearedScore_eq hm]
    exact mul_pos (product_positive hm _) hs
  simpa [unshiftedFunction] using hf

theorem unshifted_all_false {m : ℕ} (hm : 0 < m) :
    unshiftedFunction (fun _ : Fin (14 * m) ↦ false) = false := by
  have hs : score 0 (fun _ : Fin (14 * m) ↦ false) < 0 := by
    unfold score
    simp only [zero_add]
    apply Finset.sum_neg
    · intro h _
      apply div_neg_of_neg_of_pos
      · simpa only [means_constant hm, spin, Bool.false_eq_true, ite_false, mul_neg_one,
          Finset.sum_neg_distrib] using neg_neg_of_pos (sum_baseS_positive h)
      · exact denominator_positive hm _ h
    · exact Finset.univ_nonempty
  have hf : clearedScore 0 (fun _ : Fin (14 * m) ↦ false) < 0 := by
    rw [clearedScore_eq hm]
    exact mul_neg_of_pos_of_neg (product_positive hm _) hs
  simp [unshiftedFunction, not_lt_of_ge hf.le]

theorem explicitUnshiftedFunction_not_complement_invariant :
    ¬ ∀ x : Fin (14 * replicationCount) → Bool,
      explicitUnshiftedFunction (fun i ↦ !(x i)) = explicitUnshiftedFunction x := by
  intro h
  have hh := h (fun _ ↦ false)
  simp only [Bool.not_false, explicitUnshiftedFunction,
    unshifted_all_true replicationCount_positive,
    unshifted_all_false replicationCount_positive] at hh
  cases hh

end

end HeadComplexity.PureRoPEReplicationStrict
