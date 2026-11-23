import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

/-- A Boolean selector identity. It makes no universal head-count claim. -/
theorem boolean_reciprocal_selector (B δ x : ℝ) (hx : x = 0 ∨ x = 1) :
    1 / (B + δ * x) = 1 / B + x * (1 / (B + δ) - 1 / B) := by
  rcases hx with rfl | rfl <;> simp

/-- Exact positive reciprocal averaging, corresponding to one Pólya urn step.
The admissibility hypotheses may be imposed separately; only the algebraic
nonzero conditions are needed for this identity. -/
theorem polya_reciprocal_identity {ι : Type*} [Fintype ι]
    (b x : ι → ℝ) (B δ : ℝ) (hx : ∀ i, x i = 0 ∨ x i = 1)
    (hB : B = 1 + ∑ i, b i * x i) (h0 : B ≠ 0) (hδ : B + δ ≠ 0) :
    (1 + ∑ i, b i) / B =
      (1 + δ) / (B + δ) + ∑ i, b i / (B + δ * x i) := by
  have hs : ∑ i, b i / (B + δ * x i) =
      (∑ i, b i) / B + (∑ i, b i * x i) * (1 / (B + δ) - 1 / B) := by
    calc
      ∑ i, b i / (B + δ * x i) =
          ∑ i, (b i / B + (b i * x i) * (1 / (B + δ) - 1 / B)) := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          b i / (B + δ * x i) = b i * (1 / (B + δ * x i)) := by ring
          _ = b i / B + (b i * x i) * (1 / (B + δ) - 1 / B) := by
            rw [boolean_reciprocal_selector B δ (x i) (hx i)]
            ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_mul]
  rw [hs]
  have hb : ∑ i, b i * x i = B - 1 := by linarith
  rw [hb]
  field_simp
  ring

/-- Affine choices of the weights give a quadratic-numerator sign compiler
with n+2 denominator forms. This equality itself allows arbitrary weights. -/
theorem polya_affine_selector_sum {ι : Type*} [Fintype ι]
    (a x : ι → ℝ) (B δ q : ℝ) (hx : ∀ i, x i = 0 ∨ x i = 1) :
    (∑ i, a i / (B + δ * x i)) - ((∑ i, a i) + q) / B + q / (B + δ) =
      (q + ∑ i, a i * x i) * (1 / (B + δ) - 1 / B) := by
  have hs : ∑ i, a i / (B + δ * x i) =
      (∑ i, a i) / B + (∑ i, a i * x i) * (1 / (B + δ) - 1 / B) := by
    calc
      ∑ i, a i / (B + δ * x i) =
          ∑ i, (a i / B + (a i * x i) * (1 / (B + δ) - 1 / B)) := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          a i / (B + δ * x i) = a i * (1 / (B + δ * x i)) := by ring
          _ = a i / B + (a i * x i) * (1 / (B + δ) - 1 / B) := by
            rw [boolean_reciprocal_selector B δ (x i) (hx i)]
            ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_mul]
  rw [hs]
  ring

end HeadComplexity
