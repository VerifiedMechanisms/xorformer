import HeadComplexity.Results.CountingLowerBound

set_option linter.style.header false

/-!
# Active denominator counting for localized construction attempts

These auxiliary scores permit an externally supplied finite set of active heads
at each input. They do not modify `HStar` or the attention model. Clearing only
the active positive denominators makes the parameter degree depend on overlap,
not on the total head count. The analytic Warren theorem remains an explicit
hypothesis, just as in `CountingLowerBound`.
-/

namespace HeadComplexity

open Finset MvPolynomial
open scoped BigOperators

variable {n H : ℕ}

/-- Clear only the denominators of the selected heads. -/
noncomputable def activeCountingClearedPoly (s : Finset (Fin H))
    (x : Fin n → Bool) : MvPolynomial (CountingParameter n H) ℝ :=
  X (Sum.inl ()) * ∏ h ∈ s, countingAffinePoly true h x +
    ∑ h ∈ s, countingAffinePoly false h x *
      ∏ g ∈ s.erase h, countingAffinePoly true g x

private theorem active_product_degree_le_card
    (s : Finset (Fin H)) (x : Fin n → Bool) :
    (∏ h ∈ s, countingAffinePoly true h x).totalDegree ≤ s.card := by
  refine (totalDegree_finsetProd _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1
    (fun h _ ↦ countingAffinePoly_totalDegree_le true h x)).trans ?_
  rw [smul_eq_mul, mul_one]

/-- The parameter degree is bounded by the number of active heads plus one. -/
theorem activeCountingClearedPoly_totalDegree_le
    (s : Finset (Fin H)) (x : Fin n → Bool) :
    (activeCountingClearedPoly s x).totalDegree ≤ s.card + 1 := by
  classical
  unfold activeCountingClearedPoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    have hp := active_product_degree_le_card s x
    rw [totalDegree_X]
    omega
  · refine totalDegree_finsetSum_le fun h hh ↦ ?_
    refine (totalDegree_mul _ _).trans ?_
    have hp := active_product_degree_le_card (s.erase h) x
    have ha := countingAffinePoly_totalDegree_le false h x
    rw [Finset.card_erase_of_mem hh] at hp
    omega

/-- Specialization is the positive active-denominator product times the masked score. -/
theorem eval_activeCountingClearedPoly
    (A : AffineFractionFamily n H) (c : ℝ)
    (s : Finset (Fin H)) (x : Fin n → Bool) :
    eval (countingParameterPoint A c) (activeCountingClearedPoly s x) =
      (∏ h ∈ s, eval (cubePoint x) (A.den h)) *
        (c + ∑ h ∈ s, eval (cubePoint x) (A.num h) /
          eval (cubePoint x) (A.den h)) := by
  classical
  simp only [activeCountingClearedPoly, map_add, map_mul, map_prod, map_sum,
    eval_X]
  simp_rw [eval_countingAffinePoly_false A c, eval_countingAffinePoly_true A c]
  change c * (∏ h ∈ s, eval (cubePoint x) (A.den h)) +
    (∑ h ∈ s, eval (cubePoint x) (A.num h) *
      ∏ g ∈ s.erase h, eval (cubePoint x) (A.den g)) = _
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl (fun h hh ↦ ?_)
    rw [← Finset.mul_prod_erase s
      (fun g ↦ eval (cubePoint x) (A.den g)) hh]
    field_simp [(A.den_pos h x).ne']

/-- A strict masked score is a strict polynomial sign pattern with the same labels. -/
theorem strictPolynomialSignPattern_of_active_score
    (A : AffineFractionFamily n H) (c : ℝ)
    (s : (Fin n → Bool) → Finset (Fin H))
    (f : (Fin n → Bool) → Bool)
    (hsign : ∀ x, if f x then
      0 < c + ∑ h ∈ s x, eval (cubePoint x) (A.num h) /
        eval (cubePoint x) (A.den h)
      else c + ∑ h ∈ s x, eval (cubePoint x) (A.num h) /
        eval (cubePoint x) (A.den h) < 0) :
    StrictPolynomialSignPattern (fun x ↦ activeCountingClearedPoly (s x) x) f := by
  refine ⟨countingParameterPoint A c, fun x ↦ ?_⟩
  rw [eval_activeCountingClearedPoly A c]
  have hp : 0 < ∏ h ∈ s x, eval (cubePoint x) (A.den h) :=
    Finset.prod_pos (fun h _ ↦ A.den_pos h x)
  have hs := hsign x
  split_ifs at hs ⊢
  · exact mul_pos hp hs
  · exact mul_neg_of_pos_of_neg hp hs

/-- Fixed-mask counting reduction. Warren's analytic estimate is explicit. -/
theorem active_strictPatterns_card_le_warren
    (hWarren : WarrenStrictSignPatternBound)
    (s : (Fin n → Bool) → Finset (Fin H)) (L : ℕ)
    (hoverlap : ∀ x, (s x).card ≤ L)
    (hp : 1 + 2 * H * (n + 1) ≤ 2 ^ n) :
    ((strictPolynomialSignPatterns
      (fun x ↦ activeCountingClearedPoly (s x) x)).ncard : ℝ) ≤
      (4 * Real.exp 1 * (L + 1) * (2 : ℝ) ^ n /
        (1 + 2 * H * (n + 1))) ^ (1 + 2 * H * (n + 1)) := by
  have h := hWarren (2 ^ n) (L + 1) (1 + 2 * H * (n + 1))
    (by omega) (by omega) hp (Fin n → Bool) (CountingParameter n H)
    (fun x ↦ activeCountingClearedPoly (s x) x)
    (by simp) card_countingParameter
    (fun x ↦ (activeCountingClearedPoly_totalDegree_le (s x) x).trans
      (Nat.add_le_add_right (hoverlap x) 1))
  exact_mod_cast h

end HeadComplexity
