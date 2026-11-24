import HeadComplexity.Results.FiniteDifferenceUpperBound

set_option linter.style.header false

/-!
# Zero-constant reciprocal classifiers

Multiplication by one positive denominator removes one reciprocal head. The
remaining affine-ratio family has the exponential vanilla upper bound, giving
head-preserving simulation of three zero-constant reciprocal heads.
-/

namespace HeadComplexity

open scoped BigOperators

/-- A zero-constant sum of H+1 reciprocals is equivalent to H arbitrary
positive affine ratios with a free constant. -/
theorem vanilla_of_zero_constant_reciprocals {n H : ℕ}
    (r : Fin (H + 1) → AffineFraction n) (a : Fin (H + 1) → ℝ)
    (hden : ∀ h x, 0 < (r h).denominator x)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < ∑ h, a h / (r h).denominator x ↔ f x = true)) :
    computableWithSharedHeadsN n (2 ^ H - 1) f := by
  classical
  let last := Fin.last H
  let R (h : Fin H) : AffineFraction n := {
    A := fun i ↦ a h.castSucc * (r last).C i
    b := a h.castSucc * (r last).d
    C := (r h.castSucc).C
    d := (r h.castSucc).d }
  have hRden (h : Fin H) (x : Fin n → Bool) :
      (R h).denominator x = (r h.castSucc).denominator x := rfl
  have hRnum (h : Fin H) (x : Fin n → Bool) :
      (R h).numerator x = a h.castSucc * (r last).denominator x := by
    simp [R, AffineFraction.numerator, AffineFraction.denominator,
      mul_add, Finset.mul_sum, mul_assoc]
  apply FiniteDifference.computable_of_positive_denominators R (a last)
    (fun h x ↦ hden h.castSucc x) f
  intro x
  have hscore : a last + ∑ h, (R h).eval x =
      (r last).denominator x * ∑ h, a h / (r h).denominator x := by
    rw [Fin.sum_univ_castSucc, mul_add, Finset.mul_sum]
    have hterm (h : Fin H) : (R h).eval x =
        (r last).denominator x * (a h.castSucc / (r h.castSucc).denominator x) := by
      rw [AffineFraction.eval, hRnum, hRden]
      ring
    simp_rw [hterm]
    have hlast : (r last).denominator x * (a last / (r last).denominator x) = a last := by
      field_simp [(hden last x).ne']
    rw [hlast]
    ring
  rw [hscore, mul_pos_iff_of_pos_left (hden last x)]
  exact hf x

/-- Three zero-constant reciprocal heads need at most three vanilla heads. -/
theorem vanilla_three_of_zero_constant_reciprocals {n : ℕ}
    (r : Fin 3 → AffineFraction n) (a : Fin 3 → ℝ)
    (hden : ∀ h x, 0 < (r h).denominator x)
    (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (0 < ∑ h, a h / (r h).denominator x ↔ f x = true)) :
    computableWithSharedHeadsN n 3 f := by
  simpa using vanilla_of_zero_constant_reciprocals (H := 2) r a hden f hf

end HeadComplexity
