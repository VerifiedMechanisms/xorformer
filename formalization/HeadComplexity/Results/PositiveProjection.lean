import HeadComplexity.Atoms.PositiveProjection
import HeadComplexity.Results.PositiveWeightedSignDegree

set_option linter.style.header false

/-!
# Literal positive-projection form of theorem 69

The polynomial presentation is convenient for construction.  This module
rewrites the existing sandwich and exactness results using the equal ordered
image invariant `positiveProjectionSignChanges`.
-/

namespace HeadComplexity

variable {n : ℕ}

/-- Threshold degree, head complexity, and the literal ordered positive
projection change count form the theorem 69 sandwich. -/
theorem thresholdDeg_le_HStar_le_positiveProjectionSignChanges
    (f : (Fin n → Bool) → Bool) :
    thresholdDeg f ≤ HStar n f ∧
      HStar n f ≤ positiveProjectionSignChanges f := by
  rw [positiveProjectionSignChanges_eq_positiveWeightedSignDeg]
  exact thresholdDeg_le_HStar_le_positiveWeightedSignDeg f

/-- Matching threshold degree and ordered positive-projection changes determine
head complexity exactly. -/
theorem HStar_eq_thresholdDeg_of_eq_positiveProjectionSignChanges
    (f : (Fin n → Bool) → Bool)
    (h : thresholdDeg f = positiveProjectionSignChanges f) :
    HStar n f = thresholdDeg f := by
  apply HStar_eq_thresholdDeg_of_eq_positiveWeightedSignDeg
  rwa [← positiveProjectionSignChanges_eq_positiveWeightedSignDeg]

/-- Fixed-projection form: if threshold degree equals the alternation count of
one ordered positive projection, then that count is the exact head complexity. -/
theorem HStar_eq_of_thresholdDeg_eq_projectionAlternations
    (f : (Fin n → Bool) → Bool) (C : PositiveProjection f)
    (h : thresholdDeg f = C.alternations) :
    HStar n f = C.alternations := by
  apply Nat.le_antisymm
  · exact HStar_le_of_computableWithHeadsN
      (PositiveWeightedSignDegLE.computable
        ⟨C.lam, C.lam_pos, C.univariateThresholdDegLE⟩)
  · rw [← h]
    exact thresholdDeg_le_HStar f

/-- Literal ordered-projection form of the exact-two branch. -/
theorem HStar_eq_two_of_positiveProjectionSignChanges_le_two
    (f : (Fin n → Bool) → Bool)
    (hdeg : positiveProjectionSignChanges f ≤ 2)
    (hnconst : ¬ (∀ x y, f x = f y)) (hnLTF : ¬ isLTF f) :
    HStar n f = 2 := by
  apply HStar_eq_two_of_positiveWeightedSignDeg_le_two f
  · rwa [← positiveProjectionSignChanges_eq_positiveWeightedSignDeg]
  · exact hnconst
  · exact hnLTF

/-- Complete low-alternation classification in the literal ordered-projection
presentation. -/
theorem HStar_low_positiveProjection_classification
    (f : (Fin n → Bool) → Bool)
    (hdeg : positiveProjectionSignChanges f ≤ 2) :
    ((∀ x y, f x = f y) ∧ HStar n f = 0) ∨
      (¬ (∀ x y, f x = f y) ∧ isLTF f ∧ HStar n f = 1) ∨
      (¬ (∀ x y, f x = f y) ∧ ¬ isLTF f ∧ HStar n f = 2) := by
  by_cases hconst : ∀ x y, f x = f y
  · exact Or.inl ⟨hconst, (HStar_eq_zero_iff f).2 hconst⟩
  · by_cases hltf : isLTF f
    · exact Or.inr (Or.inl ⟨hconst, hltf, (HStar_eq_one_iff f).2 ⟨hconst, hltf⟩⟩)
    · exact Or.inr (Or.inr
        ⟨hconst, hltf,
          HStar_eq_two_of_positiveProjectionSignChanges_le_two f hdeg hconst hltf⟩)

end HeadComplexity
