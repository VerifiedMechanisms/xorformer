import HeadComplexity.Results.ReverseSignedCauchy
import HeadComplexity.Results.ReverseMaskedBias

set_option linter.style.header false

/-!
# Exact assembly of signed Cauchy queries and shared row biases

The uniform factor from projective compactification is essential here.
Before compactification the paired construction has a query-dependent
factor, so adding unscaled row biases would not implement the same decoder.
No universal sign-decoding property is asserted.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

/-- Concatenation preserves the strict denominator conditions and both
exact axis identities. -/
noncomputable def ReverseAxisData.append {r s H G : ℕ}
    (L : ReverseAxisData r s H) (R : ReverseAxisData r s G) :
    ReverseAxisData r s (H + G) where
  a₀ := Fin.addCases L.a₀ R.a₀
  b₀ := Fin.addCases L.b₀ R.b₀
  a := Fin.addCases L.a R.a
  b := Fin.addCases L.b R.b
  positive := by
    intro h bits
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) h
    · simpa using L.positive i bits
    · simpa only [Fin.addCases_right] using R.positive i bits
  negative := by
    intro h k
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) h
    · simpa using L.negative i k
    · simpa only [Fin.addCases_right] using R.negative i k
  zero_left := by
    intro w
    simp only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      L.zero_left w, R.zero_left w, add_zero]
  zero_right := by
    intro z
    simp only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      L.zero_right z, R.zero_right z, add_zero]

theorem ReverseAxisData.append_score {r s H G : ℕ}
    (L : ReverseAxisData r s H) (R : ReverseAxisData r s G)
    (bits : Fin (r + s) → Bool) :
    (L.append R).score bits = L.score bits + R.score bits := by
  simp only [ReverseAxisData.append, ReverseAxisData.score, Fin.sum_univ_add,
    Fin.addCases_left, Fin.addCases_right]

/-- H moving poles and G arbitrary masked row biases cost 2H + 2G heads.
Every denominator is positive on the whole Boolean cube and has strictly
negative slopes. The realized score has one common positive factor ε. -/
theorem exists_compactified_signedCauchy_with_bias {r s H G : ℕ}
    (ε : ℝ) (p a : Fin H → Fin r → ℝ) (t : Fin s → ℝ)
    (positiveMask negativeMask : Fin H → Fin s → Bool)
    (b : Fin G → Fin r → ℝ) (biasMask : Fin G → Fin s → Bool)
    (hε : 0 < ε) (hp : ∀ h i, 0 < p h i) (ht : ∀ j, 0 < t j)
    (hpt : ∀ h i j, p h i < t j)
    (hbudget : ∀ h,
      (∑ i, p h i / (p h i + ε)) + (∑ j, ε / (t j + ε)) < 1) :
    ∃ L : ReverseAxisData r s ((H + H) + (G + G)), ∀ i j,
      L.score (localGrid i j) = ε *
        ((∑ h, ((if positiveMask h j then a h i / (t j - p h i) else 0) -
          (if negativeMask h j then a h i / (t j - p h i) else 0))) +
          ∑ g, if biasMask g j then b g i else 0) := by
  obtain ⟨L, hL⟩ := exists_compactified_signedCauchy_reverseAxisData
    ε p a t positiveMask negativeMask hε hp ht hpt hbudget
  obtain ⟨R, hR⟩ := exists_reverseAxis_masked_row_sum
    (fun g i ↦ ε * b g i) biasMask
  refine ⟨L.append R, ?_⟩
  intro i j
  rw [ReverseAxisData.append_score, hL, hR, mul_add]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  cases biasMask g j <;> simp

end HeadComplexity.AxisZeroGluing
