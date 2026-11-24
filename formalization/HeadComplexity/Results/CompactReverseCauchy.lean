import HeadComplexity.Results.ReverseGridAxisRepair

set_option linter.style.header false

namespace HeadComplexity
namespace AxisZeroGluing

open scoped BigOperators

/-- A compact exterior Cauchy column with an arbitrary row numerator is one
strict reverse ratio, positive on the entire Boolean cube. -/
theorem exists_strict_reverse_cauchy_ratio {r s : ℕ} (δ : ℝ)
    (A D : Fin r → ℝ) (T : Fin s → ℝ)
    (hδ : 0 < δ) (hsize : ((r + s : ℕ) : ℝ) * δ < 1)
    (hD : ∀ i, 1 - δ < D i ∧ D i < 1)
    (hT : ∀ j, 0 < T j ∧ T j < δ) :
    ∃ Q : StrictReverseRatio (r + s),
      ∀ i j, Q.value (localGrid i j) = A i / (D i - T j) := by
  let b : Fin (r + s) → ℝ :=
    Fin.addCases (fun i ↦ D i - 1) (fun j ↦ -T j)
  have hb (k : Fin (r + s)) : -δ ≤ b k ∧ b k < 0 := by
    refine Fin.addCases ?_ ?_ k
    · intro i
      simp only [b, Fin.addCases_left]
      obtain ⟨hl, hu⟩ := hD i
      constructor <;> linarith
    · intro j
      simp only [b, Fin.addCases_right]
      obtain ⟨hl, hu⟩ := hT j
      constructor <;> linarith
  let Q : StrictReverseRatio (r + s) :=
    { a₀ := 0
      a := Fin.addCases A (fun _ ↦ 0)
      b₀ := 1
      b := b
      negative := fun k ↦ (hb k).2
      positive := by
        intro bits
        have hterm (k : Fin (r + s)) :
            -δ ≤ b k * boolToReal (bits k) := by
          cases bits k <;> simp [boolToReal] <;> linarith [(hb k).1]
        have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) ↦ hterm k)
        have hlower : -((r + s : ℕ) : ℝ) * δ ≤
            ∑ k, b k * boolToReal (bits k) := by
          simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_neg, neg_mul] using hsum
        change 0 < 1 + ∑ k, b k * boolToReal (bits k)
        linarith }
  refine ⟨Q, ?_⟩
  intro i j
  change affineValue 0 (Fin.addCases A (fun _ : Fin s ↦ (0 : ℝ))) (localGrid i j) /
    affineValue 1 b (localGrid i j) = _
  simp [affineValue, localGrid, b, Fin.sum_univ_add, boolToReal, sub_eq_add_neg,
    add_left_comm, add_comm]

end AxisZeroGluing
end HeadComplexity
