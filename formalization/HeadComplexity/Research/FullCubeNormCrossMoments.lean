import HeadComplexity.Research.FullCubeNormOptimization

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace HeadComplexity.FullCubeNormCrossMoments
open scoped BigOperators

/-- Active unit constraints determine the signed second moment of the sum
of nonnegative head gaps. The support condition is stated algebraically. -/
theorem total_gap_second_moment {X : Type*} [Fintype X]
    (mu S : X → ℝ) (K : ℝ)
    (hmu : ∑ x, mu x = 1)
    (hfirst : ∑ x, mu x*S x = K)
    (hunit : ∀ x, mu x*(S x)^2 = mu x) :
    (∑ x, mu x*(K-S x)^2) = 1-K^2 := by
  calc
    (∑ x, mu x*(K-S x)^2) =
        K^2*(∑ x, mu x) - 2*K*(∑ x, mu x*S x) +
          ∑ x, mu x*(S x)^2 := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 1-K^2 := by simp only [hmu, hfirst, hunit]; ring

/-- Expanding the full gap square isolates the cross-head moments. -/
theorem sum_pair_moments {X J : Type*} [Fintype X] [Fintype J]
    (mu S : X → ℝ) (g : J → X → ℝ) (K : ℝ)
    (hmu : ∑ x, mu x = 1)
    (hfirst : ∑ x, mu x*S x = K)
    (hunit : ∀ x, mu x*(S x)^2 = mu x)
    (hgap : ∀ x, ∑ j, g j x = K-S x) :
    (∑ j, ∑ k, ∑ x, mu x*g j x*g k x) = 1-K^2 := by
  calc
    (∑ j, ∑ k, ∑ x, mu x*g j x*g k x) =
        ∑ x, mu x*(∑ j, g j x)^2 := by
      calc
        (∑ j, ∑ k, ∑ x, mu x*g j x*g k x) =
            ∑ j, ∑ x, ∑ k, mu x*g j x*g k x := by
          apply Finset.sum_congr rfl
          intro j _
          exact Finset.sum_comm
        _ = ∑ x, ∑ j, ∑ k, mu x*g j x*g k x := Finset.sum_comm
        _ = _ := by
          simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = 1-K^2 := by
      simp only [hgap]
      exact total_gap_second_moment mu S K hmu hfirst hunit

/-- Vanishing within-head moments and K>1 force a negative cross moment. -/
theorem exists_negative_cross {X J : Type*} [Fintype X] [Fintype J]
    (mu S : X → ℝ) (g : J → X → ℝ) (K : ℝ)
    (hmu : ∑ x, mu x = 1)
    (hfirst : ∑ x, mu x*S x = K)
    (hunit : ∀ x, mu x*(S x)^2 = mu x)
    (hgap : ∀ x, ∑ j, g j x = K-S x)
    (hdiag : ∀ j, (∑ x, mu x*(g j x)^2) = 0)
    (hK : 1 < K) :
    ∃ j k, j ≠ k ∧ (∑ x, mu x*g j x*g k x) < 0 := by
  classical
  by_contra hn
  push Not at hn
  have hnonneg : ∀ j k, 0 ≤ ∑ x, mu x*g j x*g k x := by
    intro j k
    by_cases h : j = k
    · subst k
      have he : (∑ x, mu x*g j x*g j x) = 0 := by
        simpa only [pow_two, mul_assoc] using hdiag j
      rw [he]
    · exact hn j k h
  have hs := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
    Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => hnonneg j k))
  rw [sum_pair_moments mu S g K hmu hfirst hunit hgap] at hs
  nlinarith

/-- A scalar countermodel to bounding the budget from these moments alone.
It is not asserted to be an original-model head representation. -/
def exampleMu (t : ℝ) : Fin 3 → ℝ := ![(t^2+1)/2, (t^2+1)/2, -t^2]
def exampleScore : Fin 3 → ℝ := ![1,1,-1]
def exampleGap (t : ℝ) : Fin 2 → Fin 3 → ℝ :=
  ![![t^2+t,t^2-t,t^2+1], ![t^2-t,t^2+t,t^2+1]]

theorem example_moments (t : ℝ) :
    (∑ x, exampleMu t x) = 1 ∧
    (∑ x, exampleMu t x*exampleScore x) = 2*t^2+1 ∧
    (∀ x, exampleMu t x*(exampleScore x)^2 = exampleMu t x) ∧
    (∀ x, (∑ j, exampleGap t j x) = 2*t^2+1-exampleScore x) ∧
    (∀ j, (∑ x, exampleMu t x*exampleGap t j x) = 0) ∧
    (∀ j, (∑ x, exampleMu t x*(exampleGap t j x)^2) = 0) := by
  constructor
  · norm_num [exampleMu, Fin.sum_univ_succ]; ring
  constructor
  · norm_num [exampleMu, exampleScore, Fin.sum_univ_succ]; ring
  constructor
  · intro x; fin_cases x <;> norm_num [exampleMu, exampleScore]
  constructor
  · intro x; fin_cases x <;> norm_num [exampleGap, exampleScore, Fin.sum_univ_succ] <;> ring
  constructor
  · intro j; fin_cases j <;> norm_num [exampleMu, exampleGap, Fin.sum_univ_succ] <;> ring
  · intro j; fin_cases j <;> norm_num [exampleMu, exampleGap, Fin.sum_univ_succ] <;> ring

theorem example_gap_nonnegative (t : ℝ) (ht : 1 ≤ t) :
    ∀ j x, 0 ≤ exampleGap t j x := by
  intro j x
  fin_cases j <;> fin_cases x <;> simp [exampleGap] <;> nlinarith

theorem example_cross (t : ℝ) :
    (∑ x, exampleMu t x*exampleGap t 0 x*exampleGap t 1 x) =
      -2*t^2*(t^2+1) := by
  norm_num [exampleMu, exampleGap, Fin.sum_univ_succ]
  ring

end HeadComplexity.FullCubeNormCrossMoments
