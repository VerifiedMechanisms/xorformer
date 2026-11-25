import HeadComplexity.Results.VanillaInputRestriction
import HeadComplexity.Results.RoPEArchitecturalComparison

set_option linter.style.header false

/-!
# Exact invariance under adjoining ignored Boolean inputs

Every class uses finite positive attention masses, the original shared token
embeddings, and the strict positive threshold. The identities hold at all
input lengths and all head budgets, including zero.
-/

namespace HeadComplexity.InputPadding

theorem vanilla_classifier_iff {n H : ℕ} (k : ℕ) (f : (Fin n → Bool) → Bool) :
    computableWithSharedHeadsN (n + k) H (classifier k f) ↔
      computableWithSharedHeadsN n H f :=
  ⟨vanilla_of_classifier, vanilla_computable k f⟩

theorem sharedHStar_classifier {n : ℕ} (k : ℕ) (f : (Fin n → Bool) → Bool) :
    SharedHStar (n + k) (classifier k f) = SharedHStar n f := by
  classical
  have hp : (fun H ↦ computableWithSharedHeadsN (n + k) H (classifier k f)) =
      (fun H ↦ computableWithSharedHeadsN n H f) :=
    funext fun H ↦ propext (vanilla_classifier_iff k f)
  unfold SharedHStar
  simp only [hp]

theorem HStar_classifier {n : ℕ} (k : ℕ) (f : (Fin n → Bool) → Bool) :
    HStar (n + k) (classifier k f) = HStar n f := by
  rw [← SharedHStar_eq_HStar, ← SharedHStar_eq_HStar, sharedHStar_classifier]

theorem standard_classifier_iff {n H : ℕ} (k : ℕ) (f : (Fin n → Bool) → Bool) :
    rectangularStandardPureRotaryComputable (n + k) H (classifier k f) ↔
      rectangularStandardPureRotaryComputable n H f := by
  rw [rectangularStandardPureRotaryComputable_iff_scalar,
    rectangularStandardPureRotaryComputable_iff_scalar, pure_classifier_iff]

theorem free_classifier_iff {n H : ℕ} (k : ℕ) (f : (Fin n → Bool) → Bool) :
    rectangularFreePureRotaryComputable (n + k) H (classifier k f) ↔
      rectangularFreePureRotaryComputable n H f := by
  rw [rectangularFreePureRotaryComputable_iff_scalar,
    rectangularFreePureRotaryComputable_iff_scalar, pure_classifier_iff]

theorem standardHStar_classifier {n : ℕ} (k : ℕ) (f : (Fin n → Bool) → Bool) :
    StandardPureRoPEHStar (n + k) (classifier k f) = StandardPureRoPEHStar n f := by
  rw [standardPureRoPEHStar_eq_scalar, standardPureRoPEHStar_eq_scalar, pureHStar_classifier]

theorem freeHStar_classifier {n : ℕ} (k : ℕ) (f : (Fin n → Bool) → Bool) :
    FreePureRoPEHStar (n + k) (classifier k f) = FreePureRoPEHStar n f := by
  rw [freePureRoPEHStar_eq_scalar, freePureRoPEHStar_eq_scalar, pureHStar_classifier]

end HeadComplexity.InputPadding
