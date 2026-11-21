import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

open scoped BigOperators

/-- A normalized nonnegative mixture of functions which each put mass at
least one on a set also puts mass at least one on that set.  In the manual
head-model application the functions are subcube indicators. -/
theorem covering_mixture_mass {X I : Type*} [Fintype I]
    (S : Finset X) (weight : I → ℝ) (feature : I → X → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hnorm : ∑ i, weight i = 1)
    (hcover : ∀ i, 1 ≤ ∑ x ∈ S, feature i x) :
    1 ≤ ∑ x ∈ S, ∑ i, weight i * feature i x := by
  classical
  calc
    1 = ∑ i, weight i := hnorm.symm
    _ ≤ ∑ i, weight i * (∑ x ∈ S, feature i x) := by
      apply Finset.sum_le_sum
      intro i _
      simpa using mul_le_mul_of_nonneg_left (hcover i) (hweight i)
    _ = ∑ x ∈ S, ∑ i, weight i * feature i x := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm

/-- The value of a convex mixture of functions taking values in [0,1]. -/
theorem covering_mixture_bounds {X I : Type*} [Fintype I]
    (weight : I → ℝ) (feature : I → X → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hnorm : ∑ i, weight i = 1)
    (hfeature : ∀ i x, 0 ≤ feature i x ∧ feature i x ≤ 1) (x : X) :
    0 ≤ ∑ i, weight i * feature i x ∧
      ∑ i, weight i * feature i x ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hweight i) (hfeature i x).1
  · calc
      (∑ i, weight i * feature i x) ≤ ∑ i, weight i := by
        apply Finset.sum_le_sum
        intro i _
        simpa using mul_le_mul_of_nonneg_left (hfeature i x).2 (hweight i)
      _ = 1 := hnorm

/-- An explicit approximation obstruction from a cleared-score certificate.
The hypotheses expose all geometry: denominator mass on S, bounded positive
denominators, and signed isolation identities involving at most K points
outside S.  The manual proof obtains these from covering arrays and
(H+1)-face alternation.  This theorem is not a universal head lower bound. -/
theorem indicator_error_of_cleared_isolations {X : Type*}
    (S : Finset X) (T D : X → ℝ) (outside : X → Finset X)
    (coefficient : X → X → ℝ) (K : ℕ) (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (hepsilon_one : epsilon ≤ 1)
    (hD : ∀ x, 0 ≤ D x ∧ D x ≤ 1)
    (hmass : 1 ≤ ∑ x ∈ S, D x)
    (houtside : ∀ s ∈ S, ∀ x ∈ outside s, x ∉ S)
    (hcard : ∀ s ∈ S, (outside s).card ≤ K)
    (hcoeff : ∀ s ∈ S, ∀ x ∈ outside s, |coefficient s x| ≤ 1)
    (hisolation : ∀ s ∈ S,
      T s * D s = ∑ x ∈ outside s, coefficient s x * (T x * D x))
    (hinside_error : ∀ x ∈ S, |T x - 1| ≤ epsilon)
    (houtside_error : ∀ x, x ∉ S → |T x| ≤ epsilon) :
    1 / (1 + (S.card : ℝ) * K) ≤ epsilon := by
  classical
  have hpoint : ∀ s ∈ S, T s * D s ≤ epsilon * K := by
    intro s hs
    have habs : |T s * D s| ≤ epsilon * K := by
      rw [hisolation s hs]
      calc
        |∑ x ∈ outside s, coefficient s x * (T x * D x)| ≤
            ∑ x ∈ outside s, |coefficient s x * (T x * D x)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _x ∈ outside s, epsilon := by
          apply Finset.sum_le_sum
          intro x hx
          rw [abs_mul, abs_mul, abs_of_nonneg (hD x).1]
          have hTD : |T x| * D x ≤ epsilon := calc
            |T x| * D x ≤ epsilon * D x :=
              mul_le_mul_of_nonneg_right
                (houtside_error x (houtside s hs x hx)) (hD x).1
            _ ≤ epsilon * 1 := mul_le_mul_of_nonneg_left (hD x).2 hepsilon
            _ = epsilon := mul_one _
          calc
            |coefficient s x| * (|T x| * D x) ≤ 1 * (|T x| * D x) :=
              mul_le_mul_of_nonneg_right (hcoeff s hs x hx)
                (mul_nonneg (abs_nonneg _) (hD x).1)
            _ ≤ epsilon := by simpa using hTD
        _ = (outside s).card * epsilon := by simp
        _ ≤ (K : ℝ) * epsilon := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard s hs) hepsilon
        _ = epsilon * K := mul_comm _ _
    exact (le_abs_self _).trans habs
  have hsum_upper : (∑ s ∈ S, T s * D s) ≤ (S.card : ℝ) * (epsilon * K) := by
    calc
      (∑ s ∈ S, T s * D s) ≤ ∑ _s ∈ S, epsilon * K :=
        Finset.sum_le_sum hpoint
      _ = (S.card : ℝ) * (epsilon * K) := by simp
  have hsum_lower : 1 - epsilon ≤ ∑ s ∈ S, T s * D s := by
    calc
      1 - epsilon ≤ (1 - epsilon) * (∑ s ∈ S, D s) := by
        simpa using mul_le_mul_of_nonneg_left hmass (sub_nonneg.mpr hepsilon_one)
      _ = ∑ s ∈ S, (1 - epsilon) * D s := Finset.mul_sum _ _ _
      _ ≤ ∑ s ∈ S, T s * D s := by
        apply Finset.sum_le_sum
        intro s hs
        apply mul_le_mul_of_nonneg_right _ (hD s).1
        have := (abs_le.mp (hinside_error s hs)).1
        linarith
  have hden : (0 : ℝ) < 1 + (S.card : ℝ) * K := by positivity
  apply (div_le_iff₀ hden).mpr
  nlinarith [hsum_lower.trans hsum_upper]

end HeadComplexity
