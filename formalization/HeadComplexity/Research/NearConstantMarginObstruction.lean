import HeadComplexity.Atoms.AtomPolynomials
import HeadComplexity.Atoms.AtomicMargin
import HeadComplexity.Polynomial.ParityThresholdDegree
import HeadComplexity.Research.ConditionedReciprocalApproximation

set_option linter.style.header false

/-!
A quantitative obstruction to repairing margins by forcing every denominator
to be nearly constant. The denominator restriction is explicit and is not
assumed of unrestricted original-model representations.
-/

noncomputable section

namespace HeadComplexity.NearConstantMarginObstruction

open Finset MvPolynomial
open scoped BigOperators

variable {n : ℕ}

def geometricPoly (A B : MvPolynomial (Fin n) ℝ) (q : ℝ) (d : ℕ) :
    MvPolynomial (Fin n) ℝ :=
  C q⁻¹ * A * ∑ j ∈ Finset.range (d + 1), (1 - C q⁻¹ * B) ^ j

theorem geometricPoly_eval (A B : MvPolynomial (Fin n) ℝ)
    (q : ℝ) (d : ℕ) (x : Fin n → Bool) :
    eval (cubePoint x) (geometricPoly A B q d) =
      ConditionedReciprocalApproximation.headApprox
        (eval (cubePoint x) A) (eval (cubePoint x) B) q 1 d := by
  simp only [geometricPoly, map_mul, eval_C, map_sum, map_pow, map_sub,
    map_one, ConditionedReciprocalApproximation.headApprox, one_mul]
  simp only [div_eq_inv_mul]

theorem geometricPoly_degree (A B : MvPolynomial (Fin n) ℝ)
    (hA : A.totalDegree ≤ 1) (hB : B.totalDegree ≤ 1) (q : ℝ) (d : ℕ) :
    (geometricPoly A B q d).totalDegree ≤ d + 1 := by
  have hbase : (1 - C q⁻¹ * B).totalDegree ≤ 1 := by
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · simp
    · exact (totalDegree_mul _ _).trans (by simpa using hB)
  have hsum : (∑ j ∈ Finset.range (d + 1), (1 - C q⁻¹ * B) ^ j).totalDegree ≤ d := by
    apply totalDegree_finsetSum_le
    intro j hj
    exact (totalDegree_pow _ _).trans (by
      have h := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      calc
        j * (1 - C q⁻¹ * B).totalDegree ≤ j * 1 := Nat.mul_le_mul_left j hbase
        _ ≤ d := by simpa using h)
  unfold geometricPoly
  exact (totalDegree_mul _ _).trans (by
    have hleft : (C q⁻¹ * A).totalDegree ≤ 1 :=
      (totalDegree_mul _ _).trans (by simpa using hA)
    omega)

theorem geometric_error (A B q epsilon : ℝ) (d : ℕ)
    (hB : B ≠ 0) (hq : q ≠ 0) (hepsilon : |1 - B / q| ≤ epsilon) :
    |A / B - ConditionedReciprocalApproximation.headApprox A B q 1 d| ≤
      |A / B| * epsilon ^ (d + 1) := by
  rw [ConditionedReciprocalApproximation.exact_error A B q 1 d hB hq one_ne_zero]
  simp only [one_mul, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg _) hepsilon _) (abs_nonneg _)

/-- If all denominators are uniformly close to positive constants, a margin
larger than the reciprocal truncation error forces small threshold degree.
The atoms, numerators, signs, and positive denominator scales are arbitrary. -/
theorem thresholdDegLE_of_near_constant_margin
    {J : Type*} [Fintype J] (atom : J → FracAtom n)
    (bias gamma epsilon : ℝ) (amplitude q : J → ℝ) (d : ℕ)
    (f : (Fin n → Bool) → Bool)
    (hepsilon : 0 ≤ epsilon) (hq : ∀ h, 0 < q h)
    (hnear : ∀ h x,
      |1 - eval (cubePoint x) (atom h).denPoly / q h| ≤ epsilon)
    (hamp : ∀ h x, |(atom h).eval x| ≤ amplitude h)
    (htotal : 0 < |bias| + ∑ h, amplitude h)
    (hmargin : ∀ x, gamma * (|bias| + ∑ h, amplitude h) ≤
      signedLabel f x * (bias + ∑ h, (atom h).eval x))
    (hgamma : epsilon ^ (d + 1) < gamma) :
    ThresholdDegLE f (d + 1) := by
  classical
  let P : MvPolynomial (Fin n) ℝ := C bias + ∑ h,
    geometricPoly (atom h).numPoly (atom h).denPoly (q h) d
  have heps : 0 ≤ epsilon ^ (d + 1) := pow_nonneg hepsilon _
  refine ⟨P, ?_, ?_⟩
  · dsimp [P]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · simp
    · exact totalDegree_finsetSum_le fun h _ ↦ geometricPoly_degree _ _
        (atom h).numPoly_totalDegree_le (atom h).denPoly_totalDegree_le _ _
  · intro x
    let score := bias + ∑ h, (atom h).eval x
    have herr : |score - eval (cubePoint x) P| ≤
        epsilon ^ (d + 1) * (∑ h, amplitude h) := by
      dsimp [score, P]
      simp only [map_add, eval_C, map_sum, add_sub_add_left_eq_sub,
        ← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ h, |(atom h).eval x -
            eval (cubePoint x) (geometricPoly (atom h).numPoly (atom h).denPoly (q h) d)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ h, epsilon ^ (d + 1) * amplitude h := by
          apply Finset.sum_le_sum
          intro h _
          rw [geometricPoly_eval, (atom h).eval_eq_numPoly_div_denPoly]
          exact (geometric_error _ _ _ _ d ((atom h).denPoly_pos x).ne'
            (hq h).ne' (hnear h x)).trans (by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_left
                (by simpa only [← (atom h).eval_eq_numPoly_div_denPoly] using hamp h x) heps)
        _ = _ := (Finset.mul_sum _ _ _).symm
    have herr' : |signedLabel f x * (score - eval (cubePoint x) P)| ≤
        epsilon ^ (d + 1) * (|bias| + ∑ h, amplitude h) := by
      rw [abs_mul, abs_signedLabel, one_mul]
      exact herr.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (abs_nonneg _)) heps)
    have hstrict : 0 < signedLabel f x * eval (cubePoint x) P := by
      have hg := mul_lt_mul_of_pos_right hgamma htotal
      have hm := hmargin x
      have hu := (abs_le.mp herr').2
      dsimp [score] at hu
      nlinarith
    cases hx : f x
    · rw [signedLabel_of_false hx] at hstrict
      constructor
      · intro hp
        linarith
      · intro hf
        exact (Bool.false_ne_true hf).elim
    · rw [signedLabel_of_true hx, one_mul] at hstrict
      exact ⟨fun _ ↦ rfl, fun _ ↦ hstrict⟩

/-- Every representation in the stated restricted denominator family obeys
the margin bound, regardless of its number of heads or signed cancellation. -/
theorem margin_le_of_threshold_degree_gap
    {J : Type*} [Fintype J] (atom : J → FracAtom n)
    (bias gamma epsilon : ℝ) (amplitude q : J → ℝ) (d : ℕ)
    (f : (Fin n → Bool) → Bool)
    (hepsilon : 0 ≤ epsilon) (hq : ∀ h, 0 < q h)
    (hnear : ∀ h x,
      |1 - eval (cubePoint x) (atom h).denPoly / q h| ≤ epsilon)
    (hamp : ∀ h x, |(atom h).eval x| ≤ amplitude h)
    (htotal : 0 < |bias| + ∑ h, amplitude h)
    (hmargin : ∀ x, gamma * (|bias| + ∑ h, amplitude h) ≤
      signedLabel f x * (bias + ∑ h, (atom h).eval x))
    (hdegree : ¬ ThresholdDegLE f (d + 1)) :
    gamma ≤ epsilon ^ (d + 1) := by
  by_contra h
  exact hdegree (thresholdDegLE_of_near_constant_margin atom bias gamma epsilon
    amplitude q d f hepsilon hq hnear hamp htotal hmargin (lt_of_not_ge h))

/-- The full parity truth table forces margin at most `epsilon ^ (n - 1)`
when every denominator is this close to a positive constant. This statement
does not impose the denominator restriction on other representations. -/
theorem parity_margin_le_of_near_constant
    {J : Type*} [Fintype J] (hn : 2 ≤ n) (atom : J → FracAtom n)
    (bias gamma epsilon : ℝ) (amplitude q : J → ℝ)
    (hepsilon : 0 ≤ epsilon) (hq : ∀ h, 0 < q h)
    (hnear : ∀ h x,
      |1 - eval (cubePoint x) (atom h).denPoly / q h| ≤ epsilon)
    (hamp : ∀ h x, |(atom h).eval x| ≤ amplitude h)
    (htotal : 0 < |bias| + ∑ h, amplitude h)
    (hmargin : ∀ x, gamma * (|bias| + ∑ h, amplitude h) ≤
      signedLabel (PARITY n) x * (bias + ∑ h, (atom h).eval x)) :
    gamma ≤ epsilon ^ (n - 1) := by
  classical
  have hdegree : ¬ ThresholdDegLE (PARITY n) ((n - 2) + 1) := by
    intro h
    have hex : ∃ d, ThresholdDegLE (PARITY n) d := ⟨(n - 2) + 1, h⟩
    have hle : thresholdDeg (PARITY n) ≤ (n - 2) + 1 := by
      rw [thresholdDeg, dite_eq_left hex]
      exact Nat.find_min' hex h
    rw [thresholdDeg_parity] at hle
    omega
  have h := margin_le_of_threshold_degree_gap atom bias gamma epsilon
    amplitude q (n - 2) (PARITY n) hepsilon hq hnear hamp htotal hmargin hdegree
  simpa only [show n - 2 + 1 = n - 1 by omega] using h

#print axioms thresholdDegLE_of_near_constant_margin
#print axioms margin_le_of_threshold_degree_gap
#print axioms parity_margin_le_of_near_constant

end HeadComplexity.NearConstantMarginObstruction
