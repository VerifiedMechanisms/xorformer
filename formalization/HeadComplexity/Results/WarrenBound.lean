import HeadComplexity.Polynomial.PolynomialSignCount
import HeadComplexity.Results.CountingLowerBound

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Unconditional strict Warren sign-pattern bound

This module proves the previously isolated counting interface. Its dependencies
are proved algebraic root counts, generic polynomial levels, and minimization;
no sign-pattern theorem is assumed.
-/

namespace HeadComplexity

open MvPolynomial
open PolynomialRootCount

/-- The number of strict sign patterns of a bounded-degree real polynomial
family satisfies Warren's quantitative estimate. -/
theorem strictPolynomialSignPatterns_card_le {I K : Type*} [Fintype I] [Fintype K]
    {d : ℕ} (hd : 0 < d) (hK : 0 < Fintype.card K)
    (hKI : Fintype.card K ≤ Fintype.card I)
    (P : I → MvPolynomial K ℝ) (hP : ∀ i, (P i).totalDegree ≤ d) :
    ((strictPolynomialSignPatterns P).ncard : ℝ) ≤
      (4 * Real.exp 1 * d * Fintype.card I / Fintype.card K) ^ Fintype.card K := by
  classical
  let T := strictPolynomialSignPatterns P
  let := Fintype.ofFinite T
  have hw (t : T) : ∃ θ : K → ℝ, ∀ i,
      if t.val i then 0 < eval θ (P i) else eval θ (P i) < 0 := t.property
  choose θ hθ using hw
  have hs (t : T) (i : I) : 0 < eval (θ t) (signedPolynomial (t.val i) (P i)) := by
    have h := hθ t i
    cases hb : t.val i <;> simpa [signedPolynomial, hb] using h
  have h := strict_sign_realizations_bound hd hK hKI P hP
    (fun t : T ↦ t.val) Subtype.val_injective θ hs
  simpa only [T, Set.fintypeCard_eq_ncard] using h

/-- A proof, rather than a hypothesis, of the repository's strict Warren interface. -/
theorem warrenStrictSignPatternBound : WarrenStrictSignPatternBound := by
  intro N d k hd hk hkN I K _ _ P hI hK hdegree
  have hk' : 0 < Fintype.card K := by omega
  have hkI : Fintype.card K ≤ Fintype.card I := by omega
  simpa only [hI, hK] using strictPolynomialSignPatterns_card_le hd hk' hkI P hdegree

/-- The coarse counting interface is now unconditional as well. -/
theorem coarseWarrenSignPatternBound : CoarseWarrenSignPatternBound :=
  coarseWarrenSignPatternBound_of_warren warrenStrictSignPatternBound

/-- Unconditional truth-table count for bounded head complexity. -/
theorem card_headComputableFunctions_le_counting {n H : ℕ}
    (hn : 1 ≤ n) (hH : 1 ≤ H) (hHpow : H ≤ 2 ^ n) :
    (headComputableFunctions n H).ncard ≤ 2 ^ (35 * n * n * H) :=
  card_headComputableFunctions_le_two_pow_of_warren warrenStrictSignPatternBound hn hH hHpow

/-- Unconditional finite worst-case lower bound from the counting estimate. -/
theorem exists_HStar_gt_of_counting {n H : ℕ}
    (hn : 1 ≤ n) (hH : 1 ≤ H) (hHpow : H ≤ 2 ^ n)
    (hsmall : 35 * n * n * H < 2 ^ n) :
    ∃ f : (Fin n → Bool) → Bool, H < HStar n f :=
  exists_HStar_gt_of_warren warrenStrictSignPatternBound hn hH hHpow hsmall

/-- Division form of the unconditional worst-case lower bound. -/
theorem worstCaseHeadComplexity_gt_div {n : ℕ} (hn : 1 ≤ n)
    (hsize : 35 * n * n ≤ 2 ^ n - 1) :
    (2 ^ n - 1) / (35 * n * n) < worstCaseHeadComplexity n :=
  worstCaseHeadComplexity_gt_div_of_warren warrenStrictSignPatternBound hn hsize

end HeadComplexity
