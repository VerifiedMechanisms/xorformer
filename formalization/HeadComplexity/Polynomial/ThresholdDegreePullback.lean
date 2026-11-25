import HeadComplexity.Results.RoPEComparison

/-!
# Threshold degree under identification of input coordinates

Substituting one input coordinate for another is polynomial renaming, so it
cannot increase total degree. No injectivity or surjectivity is required.
-/

namespace HeadComplexity.ThresholdDegreePullback

open MvPolynomial

theorem thresholdDegLE_pullback {n N d : ℕ} (π : Fin N → Fin n)
    (f : (Fin N → Bool) → Bool) (hf : ThresholdDegLE f d) :
    ThresholdDegLE (fun x : Fin n → Bool ↦ f (x ∘ π)) d := by
  obtain ⟨P, hP, hs⟩ := hf
  refine ⟨rename π P, (totalDegree_rename_le π P).trans hP, fun x ↦ ?_⟩
  rw [eval_rename]
  exact hs (x ∘ π)

theorem thresholdDegLE_minimum {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ThresholdDegLE f (thresholdDeg f) := by
  classical
  have he : ∃ d, ThresholdDegLE f d :=
    ⟨PureRoPEHStar n f, thresholdDegLE_of_pureRoPEComputable (pureRoPEHStar_computable f)⟩
  rw [thresholdDeg, dif_pos he]
  exact Nat.find_spec he

theorem thresholdDeg_le_of_witness {n d : ℕ} (f : (Fin n → Bool) → Bool)
    (hf : ThresholdDegLE f d) : thresholdDeg f ≤ d := by
  classical
  have he : ∃ k, ThresholdDegLE f k := ⟨d, hf⟩
  rw [thresholdDeg, dif_pos he]
  exact Nat.find_min' he hf

theorem thresholdDeg_pullback_le {n N : ℕ} (π : Fin N → Fin n)
    (f : (Fin N → Bool) → Bool) :
    thresholdDeg (fun x : Fin n → Bool ↦ f (x ∘ π)) ≤ thresholdDeg f :=
  thresholdDeg_le_of_witness _ (thresholdDegLE_pullback π f (thresholdDegLE_minimum f))

end HeadComplexity.ThresholdDegreePullback
