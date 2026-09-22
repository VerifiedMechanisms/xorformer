import HeadComplexity.Results.OneBitGateThresholdDegree
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option linter.style.header false

/-!
# Top threshold degree

The degree-at-most-`n - 1` cube polynomials form the hyperplane orthogonal to
the parity character.  Removing the parity component of a non-parity sign
table gives a strict sign representation in that hyperplane.
-/

namespace HeadComplexity

open Finset MvPolynomial
open scoped BigOperators

variable {n : ℕ}

/-- The `±1` encoding of a Boolean truth table. -/
def booleanSignValue (f : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) : ℝ :=
  if f x then 1 else -1

/-- The parity character in the convention that parity inputs have value
`-1`. -/
def paritySignValue (x : Fin n → Bool) : ℝ :=
  if PARITY n x then -1 else 1

/-- Agreement with parity is encoded by `-1`, disagreement by `1`. -/
def parityAgreementValue (f : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) : ℝ :=
  booleanSignValue f x * paritySignValue x

@[simp] theorem booleanSignValue_sq
    (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    booleanSignValue f x ^ 2 = 1 := by
  cases h : f x <;> simp [booleanSignValue, h]

@[simp] theorem paritySignValue_sq (x : Fin n → Bool) :
    paritySignValue x ^ 2 = 1 := by
  cases h : PARITY n x <;> simp [paritySignValue, h]

theorem parityAgreementValue_eq (f : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) :
    parityAgreementValue f x =
      if f x = PARITY n x then -1 else 1 := by
  cases hf : f x <;> cases hp : PARITY n x <;>
    simp [parityAgreementValue, booleanSignValue, paritySignValue, hf, hp]

/-- The parity sign agrees with the usual product character on the cube. -/
theorem paritySignValue_eq_prod (x : Fin n → Bool) :
    paritySignValue x =
      ∏ i, (1 - 2 * boolToReal (x i)) := by
  rw [prod_one_sub_two]
  by_cases hodd : Odd (hammingWeight x)
  · rw [hodd.neg_one_pow]
    simp [paritySignValue, PARITY, hodd]
  · have heven : Even (hammingWeight x) := by
      rwa [← Nat.not_odd_iff_even]
    rw [heven.neg_one_pow]
    simp [paritySignValue, PARITY, hodd]

/-- Sign of the leading coefficient of the cube indicator at `x`. -/
def cubeIndicatorTopSign (x : Fin n → Bool) : ℝ :=
  (-1 : ℝ) ^ n * paritySignValue x

@[simp] theorem cubeIndicatorTopSign_sq (x : Fin n → Bool) :
    cubeIndicatorTopSign x ^ 2 = 1 := by
  unfold cubeIndicatorTopSign
  rw [mul_pow, paritySignValue_sq, mul_one, ← pow_mul]
  norm_num

/-- Monic version of the point-indicator polynomial.  A false coordinate uses
`X_i - 1`, while a true coordinate uses `X_i`. -/
noncomputable def monicCubeIndicator (x : Fin n → Bool) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i, (X i - C (if x i then 0 else 1))

/-- Removing the common top monomial leaves degree at most `n - 1`. -/
noncomputable def lowerCubeIndicator (x : Fin n → Bool) :
    MvPolynomial (Fin n) ℝ :=
  monicCubeIndicator x - monicCubeIndicator (fun _ ↦ true)

private theorem monicFactor_totalDegree_le
    (x : Fin n → Bool) (i : Fin n) :
    (X i - C (if x i then (0 : ℝ) else 1)).totalDegree ≤ 1 := by
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_X]
  · split <;> simp

private theorem totalDegree_prod_monicFactors_le
    (x : Fin n → Bool) (s : Finset (Fin n)) :
    (∏ i ∈ s, (X i - C (if x i then (0 : ℝ) else 1))).totalDegree ≤
      s.card := by
  refine (totalDegree_finsetProd s
    (fun i ↦ X i - C (if x i then (0 : ℝ) else 1))).trans ?_
  exact (Finset.sum_le_card_nsmul s _ 1
    (fun i _ ↦ monicFactor_totalDegree_le x i)).trans (by simp)

private theorem totalDegree_prod_X_le (s : Finset (Fin n)) :
    (∏ i ∈ s, (X i : MvPolynomial (Fin n) ℝ)).totalDegree ≤ s.card := by
  refine (totalDegree_finsetProd s (fun i ↦ X i)).trans ?_
  simp

private theorem lower_upper_card (i : Fin n) :
    (Finset.univ.filter fun j : Fin n ↦ j < i).card +
      (Finset.univ.filter fun j : Fin n ↦ i < j).card = n - 1 := by
  let lo := Finset.univ.filter fun j : Fin n ↦ j < i
  let hi := Finset.univ.filter fun j : Fin n ↦ i < j
  have hdis : Disjoint lo hi := by
    refine Finset.disjoint_left.mpr ?_
    intro j hjlo hjhi
    simp only [lo, hi, Finset.mem_filter, Finset.mem_univ, true_and] at hjlo hjhi
    exact (lt_asymm hjlo hjhi)
  have hunion : lo ∪ hi = Finset.univ.erase i := by
    ext j
    simp only [lo, hi, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_erase]
    constructor
    · intro h
      rcases h with h | h
      · exact ⟨ne_of_lt h, trivial⟩
      · exact ⟨Ne.symm (ne_of_lt h), trivial⟩
    · rintro ⟨hne, -⟩
      exact lt_or_gt_of_ne hne
  rw [← Finset.card_union_of_disjoint hdis, hunion,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]

/-- The common leading monomial cancels, leaving total degree at most
`n - 1`. -/
theorem lowerCubeIndicator_totalDegree_le (x : Fin n → Bool) :
    (lowerCubeIndicator x).totalDegree ≤ n - 1 := by
  classical
  have htrue : monicCubeIndicator (fun _ : Fin n ↦ true) =
      ∏ i : Fin n, X i := by
    simp [monicCubeIndicator]
  have hexpand := Finset.prod_sub_ordered (Finset.univ : Finset (Fin n))
    (fun i ↦ (X i : MvPolynomial (Fin n) ℝ))
    (fun i ↦ C (if x i then (0 : ℝ) else 1))
  have hlower : lowerCubeIndicator x =
      -∑ i : Fin n,
        C (if x i then (0 : ℝ) else 1) *
          (∏ j ∈ Finset.univ with j < i,
            (X j - C (if x j then (0 : ℝ) else 1))) *
          ∏ j ∈ Finset.univ with i < j, X j := by
    unfold lowerCubeIndicator
    rw [htrue]
    change (∏ i : Fin n,
        (X i - C (if x i then (0 : ℝ) else 1))) - ∏ i : Fin n, X i = _
    rw [hexpand]
    ring
  rw [hlower, totalDegree_neg]
  apply totalDegree_finsetSum_le
  intro i hi
  let lo := Finset.univ.filter fun j : Fin n ↦ j < i
  let up := Finset.univ.filter fun j : Fin n ↦ i < j
  have hlo :
      (∏ j ∈ lo, (X j - C (if x j then (0 : ℝ) else 1))).totalDegree ≤
        lo.card := totalDegree_prod_monicFactors_le x lo
  have hup :
      (∏ j ∈ up, (X j : MvPolynomial (Fin n) ℝ)).totalDegree ≤ up.card :=
    totalDegree_prod_X_le up
  calc
    (C (if x i then (0 : ℝ) else 1) *
        (∏ j ∈ Finset.univ with j < i,
          (X j - C (if x j then (0 : ℝ) else 1))) *
        ∏ j ∈ Finset.univ with i < j, X j).totalDegree ≤
        0 + lo.card + up.card := by
      refine (totalDegree_mul _ _).trans ?_
      refine Nat.add_le_add (totalDegree_mul _ _ |>.trans ?_) hup
      exact Nat.add_le_add (by split <;> simp) hlo
    _ = n - 1 := by
      simp only [zero_add]
      exact lower_upper_card i

private theorem eval_monicCubeIndicator_self (x : Fin n → Bool) :
    eval (cubePoint x) (monicCubeIndicator x) = cubeIndicatorTopSign x := by
  classical
  rw [monicCubeIndicator, map_prod]
  have hfactor : ∀ i : Fin n,
      eval (cubePoint x) (X i - C (if x i then (0 : ℝ) else 1)) =
        (-1 : ℝ) * (1 - 2 * boolToReal (x i)) := by
    intro i
    cases h : x i <;> norm_num [cubePoint, boolToReal, h]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← paritySignValue_eq_prod]
  rfl

private theorem eval_monicCubeIndicator_ne {x y : Fin n → Bool}
    (hxy : x ≠ y) :
    eval (cubePoint y) (monicCubeIndicator x) = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra h
    apply hxy
    funext i
    exact of_not_not (not_exists.mp h i)
  rw [monicCubeIndicator, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  cases hx : x i <;> cases hy : y i <;>
    simp_all [cubePoint, boolToReal]

theorem eval_monicCubeIndicator (x y : Fin n → Bool) :
    eval (cubePoint y) (monicCubeIndicator x) =
      if x = y then cubeIndicatorTopSign x else 0 := by
  by_cases hxy : x = y
  · subst y
    rw [if_pos rfl]
    exact eval_monicCubeIndicator_self x
  · rw [if_neg hxy]
    exact eval_monicCubeIndicator_ne hxy

theorem eval_lowerCubeIndicator (x y : Fin n → Bool) :
    eval (cubePoint y) (lowerCubeIndicator x) =
      (if x = y then cubeIndicatorTopSign x else 0) -
        (if (fun _ : Fin n ↦ true) = y then 1 else 0) := by
  rw [lowerCubeIndicator, map_sub, eval_monicCubeIndicator,
    eval_monicCubeIndicator]
  have htop : cubeIndicatorTopSign (fun _ : Fin n ↦ true) = 1 := by
    rw [cubeIndicatorTopSign, paritySignValue_eq_prod]
    simp only [boolToReal, if_true, mul_one, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [show (1 - 2 : ℝ) = -1 by norm_num, ← pow_two, ← pow_mul]
    norm_num
  rw [htop]

/-- Interpolation inside the parity-orthogonal hyperplane. -/
noncomputable def lowerCubeInterpolation
    (r : (Fin n → Bool) → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ x, C (cubeIndicatorTopSign x * r x) * lowerCubeIndicator x

theorem lowerCubeInterpolation_totalDegree_le
    (r : (Fin n → Bool) → ℝ) :
    (lowerCubeInterpolation r).totalDegree ≤ n - 1 := by
  classical
  unfold lowerCubeInterpolation
  apply totalDegree_finsetSum_le
  intro x hx
  calc
    (C (cubeIndicatorTopSign x * r x) * lowerCubeIndicator x).totalDegree ≤
        (C (cubeIndicatorTopSign x * r x)).totalDegree +
          (lowerCubeIndicator x).totalDegree := totalDegree_mul _ _
    _ ≤ 0 + (n - 1) := Nat.add_le_add (by
      rw [totalDegree_C])
      (lowerCubeIndicator_totalDegree_le x)
    _ = n - 1 := Nat.zero_add _

theorem eval_lowerCubeInterpolation
    (r : (Fin n → Bool) → ℝ)
    (horth : ∑ x, cubeIndicatorTopSign x * r x = 0)
    (y : Fin n → Bool) :
    eval (cubePoint y) (lowerCubeInterpolation r) = r y := by
  classical
  unfold lowerCubeInterpolation
  simp_rw [map_sum, map_mul, eval_C, eval_lowerCubeIndicator]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfirst :
      (∑ x, cubeIndicatorTopSign x * r x *
        (if x = y then cubeIndicatorTopSign x else 0)) = r y := by
    rw [Finset.sum_eq_single y]
    · rw [if_pos rfl]
      calc
        cubeIndicatorTopSign y * r y * cubeIndicatorTopSign y =
            cubeIndicatorTopSign y ^ 2 * r y := by ring
        _ = r y := by rw [cubeIndicatorTopSign_sq, one_mul]
    · intro x hx hxy
      rw [if_neg hxy]
      ring
    · intro hy
      exact (hy (Finset.mem_univ y)).elim
  rw [hfirst]
  have hsecond :
      (∑ x, cubeIndicatorTopSign x * r x *
        (if (fun _ : Fin n ↦ true) = y then 1 else 0)) = 0 := by
    rw [← Finset.sum_mul]
    rw [horth, zero_mul]
  rw [hsecond, sub_zero]

/-- Sum of the parity-agreement signs. -/
noncomputable def parityCorrelationSum
    (f : (Fin n → Bool) → Bool) : ℝ :=
  ∑ x, parityAgreementValue f x

/-- The parity component removed from a sign truth table, without division. -/
noncomputable def centeredSignValue
    (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℝ :=
  (2 ^ n : ℕ) * booleanSignValue f x -
    parityCorrelationSum f * paritySignValue x

private theorem exists_parity_agreement
    {f : (Fin n → Bool) → Bool}
    (hf : f ≠ complementFn (PARITY n)) :
    ∃ x, f x = PARITY n x := by
  by_contra h
  push Not at h
  apply hf
  funext x
  specialize h x
  cases hfx : f x <;> cases hpx : PARITY n x <;>
    simp_all [complementFn]

private theorem exists_parity_disagreement
    {f : (Fin n → Bool) → Bool} (hf : f ≠ PARITY n) :
    ∃ x, f x ≠ PARITY n x := by
  by_contra h
  push Not at h
  apply hf
  funext x
  exact h x

private theorem parityCorrelationSum_bounds
    {f : (Fin n → Bool) → Bool}
    (hparity : f ≠ PARITY n)
    (hcomplement : f ≠ complementFn (PARITY n)) :
    (-(2 ^ n : ℕ) : ℝ) < parityCorrelationSum f ∧
      parityCorrelationSum f < (2 ^ n : ℕ) := by
  classical
  obtain ⟨xeq, hxeq⟩ := exists_parity_agreement hcomplement
  obtain ⟨xne, hxne⟩ := exists_parity_disagreement hparity
  have hallLower : ∀ x ∈ (Finset.univ : Finset (Fin n → Bool)),
      (-1 : ℝ) ≤ parityAgreementValue f x := by
    intro x hx
    rw [parityAgreementValue_eq]
    split <;> norm_num
  have hallUpper : ∀ x ∈ (Finset.univ : Finset (Fin n → Bool)),
      parityAgreementValue f x ≤ (1 : ℝ) := by
    intro x hx
    rw [parityAgreementValue_eq]
    split <;> norm_num
  have hlower :
      (∑ _x : Fin n → Bool, (-1 : ℝ)) <
        ∑ x, parityAgreementValue f x := by
    apply Finset.sum_lt_sum hallLower
    exact ⟨xne, Finset.mem_univ _, by
      rw [parityAgreementValue_eq, if_neg hxne]
      norm_num⟩
  have hupper :
      (∑ x, parityAgreementValue f x) <
        ∑ _x : Fin n → Bool, (1 : ℝ) := by
    apply Finset.sum_lt_sum hallUpper
    exact ⟨xeq, Finset.mem_univ _, by
      rw [parityAgreementValue_eq, if_pos hxeq]
      norm_num⟩
  constructor
  · simpa [parityCorrelationSum, Fintype.card_bool] using hlower
  · simpa [parityCorrelationSum, Fintype.card_bool] using hupper

private theorem centeredSignValue_strict
    {f : (Fin n → Bool) → Bool}
    (hparity : f ≠ PARITY n)
    (hcomplement : f ≠ complementFn (PARITY n))
    (x : Fin n → Bool) :
    0 < booleanSignValue f x * centeredSignValue f x := by
  have hb := parityCorrelationSum_bounds hparity hcomplement
  norm_num [Nat.cast_pow] at hb
  cases hfx : f x <;> cases hpx : PARITY n x <;>
    simp [booleanSignValue, centeredSignValue, paritySignValue,
      hfx, hpx] <;> linarith [hb.1, hb.2]

private theorem centeredSignValue_orthogonal
    (f : (Fin n → Bool) → Bool) :
    ∑ x, cubeIndicatorTopSign x * centeredSignValue f x = 0 := by
  classical
  have hterm : ∀ x : Fin n → Bool,
      cubeIndicatorTopSign x * centeredSignValue f x =
        (-1 : ℝ) ^ n * (2 ^ n : ℕ) * parityAgreementValue f x -
          (-1 : ℝ) ^ n * parityCorrelationSum f := by
    intro x
    unfold cubeIndicatorTopSign centeredSignValue parityAgreementValue
    calc
      (-1 : ℝ) ^ n * paritySignValue x *
          ((2 ^ n : ℕ) * booleanSignValue f x -
            parityCorrelationSum f * paritySignValue x) =
          (-1 : ℝ) ^ n * (2 ^ n : ℕ) *
              (booleanSignValue f x * paritySignValue x) -
            (-1 : ℝ) ^ n * parityCorrelationSum f *
              paritySignValue x ^ 2 := by ring
      _ = (-1 : ℝ) ^ n * (2 ^ n : ℕ) *
            (booleanSignValue f x * paritySignValue x) -
          (-1 : ℝ) ^ n * parityCorrelationSum f := by
        rw [paritySignValue_sq, mul_one]
  simp_rw [hterm, Finset.sum_sub_distrib]
  unfold parityCorrelationSum
  simp only [Nat.cast_pow, Nat.cast_ofNat, Finset.sum_const,
    Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
    Finset.prod_const, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- Every truth table other than parity and its complement has a strict sign
polynomial of degree at most `n - 1`. -/
theorem thresholdDegLE_pred_of_ne_parity_complement
    {f : (Fin n → Bool) → Bool}
    (hparity : f ≠ PARITY n)
    (hcomplement : f ≠ complementFn (PARITY n)) :
    ThresholdDegLE f (n - 1) := by
  let r := centeredSignValue f
  let P := lowerCubeInterpolation r
  refine ⟨P, lowerCubeInterpolation_totalDegree_le r, ?_⟩
  intro x
  rw [show eval (cubePoint x) P = r x by
    exact eval_lowerCubeInterpolation r (centeredSignValue_orthogonal f) x]
  have hstrict := centeredSignValue_strict hparity hcomplement x
  change 0 < booleanSignValue f x * r x at hstrict
  cases hfx : f x with
  | false =>
      have hr : r x < 0 := by
        simp [booleanSignValue, hfx] at hstrict
        linarith
      simp [not_lt_of_ge hr.le]
  | true =>
      have hr : 0 < r x := by
        simpa [booleanSignValue, hfx] using hstrict
      simp [hr]

/-- **Theorem 27.** For `n ≥ 1`, top threshold degree occurs only for parity
and its output complement. -/
theorem thresholdDeg_eq_ambient_iff (hn : 1 ≤ n)
    (f : (Fin n → Bool) → Bool) :
    thresholdDeg f = n ↔
      f = PARITY n ∨ f = complementFn (PARITY n) := by
  constructor
  · intro htop
    by_contra h
    push Not at h
    have hle : thresholdDeg f ≤ n - 1 :=
      thresholdDeg_le_of_ThresholdDegLE
        (thresholdDegLE_pred_of_ne_parity_complement h.1 h.2)
    omega
  · rintro (rfl | rfl)
    · exact thresholdDeg_parity n
    · rw [thresholdDeg_complement, thresholdDeg_parity]

end HeadComplexity
