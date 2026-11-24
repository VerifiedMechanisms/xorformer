import HeadComplexity.Foundation.AlternatingMoments

set_option linter.style.header false

namespace HeadComplexity
namespace AlternatingMoments

open scoped BigOperators

/-- The alternating reciprocal sum has a product as its first nonzero term. -/
theorem reciprocal_power_expansion {ι : Type*}
    (s : Finset ι) (D : ι → ℝ) (B t : ℝ) (hB : B ≠ 0)
    (hden : ∀ I ∈ s.powerset, B + t * (∑ i ∈ I, D i) ≠ 0) :
    (∑ I ∈ s.powerset, (-1 : ℝ)^I.card / (B + t * (∑ i ∈ I, D i))) =
      ((-t)^s.card / B^(s.card + 1)) *
        ((-1 : ℝ)^s.card * (s.card.factorial : ℝ) * ∏ i ∈ s, D i) +
      (-t)^(s.card + 1) * ∑ I ∈ s.powerset,
        (-1 : ℝ)^I.card * (∑ i ∈ I, D i)^(s.card + 1) /
          (B^(s.card + 1) * (B + t * (∑ i ∈ I, D i))) := by
  classical
  have hterm (I : Finset ι) (hI : I ∈ s.powerset) :
      (-1 : ℝ)^I.card / (B + t * (∑ i ∈ I, D i)) =
      (∑ k ∈ Finset.range (s.card + 1),
        ((-t)^k / B^(k + 1)) * ((-1 : ℝ)^I.card * (∑ i ∈ I, D i)^k)) +
      (-t)^(s.card + 1) * ((-1 : ℝ)^I.card * (∑ i ∈ I, D i)^(s.card + 1) /
        (B^(s.card + 1) * (B + t * (∑ i ∈ I, D i)))) := by
    let A := (-1 : ℝ)^I.card
    let d := ∑ i ∈ I, D i
    change A / (B + t * d) =
      (∑ k ∈ Finset.range (s.card + 1), ((-t)^k / B^(k + 1)) * (A * d^k)) +
      (-t)^(s.card + 1) * (A * d^(s.card + 1) /
        (B^(s.card + 1) * (B + t * d)))
    have he := congrArg (fun v : ℝ ↦ A * v)
      (reciprocal_expansion B t d hB (hden I hI) (s.card + 1))
    rw [mul_add] at he
    have hmul : A * (∑ k ∈ Finset.range (s.card + 1), (-t)^k * d^k / B^(k + 1)) =
        ∑ k ∈ Finset.range (s.card + 1), A * ((-t)^k * d^k / B^(k + 1)) :=
      Finset.mul_sum _ _ _
    rw [hmul] at he
    convert he using 1
    · ring
    · congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        ring
      · ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_comm,
    ← Finset.mul_sum]
  congr 1
  have he : (∑ k ∈ Finset.range (s.card + 1),
      ∑ I ∈ s.powerset, ((-t)^k / B^(k + 1)) *
        ((-1 : ℝ)^I.card * (∑ i ∈ I, D i)^k)) =
      ∑ k ∈ Finset.range (s.card + 1), ((-t)^k / B^(k + 1)) * power s D k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [power, Finset.mul_sum]
  rw [he, Finset.sum_eq_single s.card]
  · rw [power_top]
  · intro k hk hne
    rw [power_below s D k (by have := Finset.mem_range.mp hk; omega), mul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

end AlternatingMoments
end HeadComplexity
