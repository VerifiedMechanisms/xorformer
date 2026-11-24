import HeadComplexity.Results.JointFamilyHaarSplit

set_option linter.style.header false

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

noncomputable def jointFamilySignedReadout {I J : Type*} [Fintype J]
    (source : J → I) (K : I → J → ℝ) (σ : I → ℝ) (c : J → ℝ) (i : I) : ℝ :=
  ∑ j, K i j * σ (source j) * c j

/-- Two sign words can share coefficients if the agreement class can solve
its own queries and the disagreement class can interpolate every query.
For the paired square/cube Cauchy system, the latter class needs only half
the source points.  The concrete rank calculation is a separate written
argument; this declaration checks the simultaneous strict-sign step. -/
theorem jointFamily_two_word_compatibility
    {I J : Type*} [Fintype J] (source : J → I) (K : I → J → ℝ)
    (σ τ : I → ℝ) (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    (hτ : ∀ i, τ i = 1 ∨ τ i = -1)
    (hP : ∃ c : J → ℝ,
      (∀ j, σ (source j) ≠ τ (source j) → c j = 0) ∧
      ∀ i, σ i = τ i → jointFamilySignedReadout source K σ c i = σ i)
    (hQ : ∀ y : I → ℝ, ∃ c : J → ℝ,
      (∀ j, σ (source j) = τ (source j) → c j = 0) ∧
      ∀ i, jointFamilySignedReadout source K σ c i = y i) :
    ∃ c : J → ℝ,
      (∀ i, 0 < σ i * jointFamilySignedReadout source K σ c i) ∧
      (∀ i, 0 < τ i * jointFamilySignedReadout source K τ c i) := by
  classical
  obtain ⟨a, ha, hpa⟩ := hP
  let f : I → ℝ := jointFamilySignedReadout source K σ a
  let y : I → ℝ := fun i ↦ if σ i = τ i then 0 else σ i * (|f i| + 1)
  obtain ⟨b, hb, hqb⟩ := hQ y
  have haτ (i : I) : jointFamilySignedReadout source K τ a i = f i := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : σ (source j) = τ (source j)
    · rw [h]
    · simp [ha j h]
  have hbτ (i : I) : jointFamilySignedReadout source K τ b i = -y i := by
    rw [← hqb i]
    simp only [jointFamilySignedReadout, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : σ (source j) = τ (source j)
    · simp [hb j h]
    · have hn : τ (source j) = -σ (source j) := by
        rcases hσ (source j) with hs | hs <;>
          rcases hτ (source j) with ht | ht <;> simp_all
      rw [hn]
      ring
  have hadd (word : I → ℝ) (i : I) :
      jointFamilySignedReadout source K word (a + b) i =
        jointFamilySignedReadout source K word a i +
          jointFamilySignedReadout source K word b i := by
    simp [jointFamilySignedReadout, mul_add, Finset.sum_add_distrib]
  refine ⟨a + b, ?_, ?_⟩
  · intro i
    rw [hadd, hqb]
    change 0 < σ i * (f i + y i)
    by_cases h : σ i = τ i
    · have hf : f i = σ i := hpa i h
      simp only [y, if_pos h, hf, add_zero]
      rcases hσ i with hs | hs <;> norm_num [hs]
    · simp only [y, if_neg h]
      have hab := neg_abs_le (f i)
      have hab' := le_abs_self (f i)
      rcases hσ i with hs | hs <;> rw [hs] <;> nlinarith
  · intro i
    rw [hadd, haτ, hbτ]
    by_cases h : σ i = τ i
    · have hf : f i = σ i := hpa i h
      simp only [y, if_pos h, hf, neg_zero, add_zero]
      rw [← h]
      rcases hσ i with hs | hs <;> norm_num [hs]
    · have hn : τ i = -σ i := by
        rcases hσ i with hs | hs <;> rcases hτ i with ht | ht <;> simp_all
      simp only [y, if_neg h]
      rw [hn]
      have hab := neg_abs_le (f i)
      have hab' := le_abs_self (f i)
      rcases hσ i with hs | hs <;> rw [hs] <;> nlinarith

/-- Exact paired-pole algebra: the pair sum supplies an independent cubic
Cauchy feature after scaling by the split gap. -/
theorem jointFamily_paired_square_cube_identity (x t a b : ℝ)
    (hx : x ≠ 0) (hm : x - t ≠ 0) (hp : x + t ≠ 0) :
    a / (x * (x + t)) - b / (x * (x - t)) - 2 / (x ^ 2 - t ^ 2) =
      (a - b - 2) / (x ^ 2 - t ^ 2) -
        t * (a + b) / (x * (x ^ 2 - t ^ 2)) := by
  have hs : x ^ 2 - t ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hp hm
  field_simp
  <;> ring

end HeadComplexity.AxisZeroGluing
