import HeadComplexity.Results.AffineFractionNormalForm

set_option linter.style.header false

/-! # Coefficient boundaries and different representations of the same score -/

namespace HeadComplexity.AffineFractionExamples

open AffineFraction
open scoped BigOperators InnerProductSpace

/-- Check positivity at all four inputs, independently of slope signs. -/
private theorem denominator_pos_two_iff (r : AffineFraction 2) :
    (∀ x, 0 < r.denominator x) ↔
      0 < r.d ∧ 0 < r.d + r.C 0 ∧ 0 < r.d + r.C 1 ∧ 0 < r.d + r.C 0 + r.C 1 := by
  simp [denominator, Fin.sum_univ_two, Fin.forall_fin_succ_pi,
    Bool.forall_bool, boolToReal, add_assoc, and_left_comm, and_assoc]

theorem positive_denominator (A : Fin 2 → ℝ) (b : ℝ) :
    (⟨A, b, ![1, 2], 1⟩ : AffineFraction 2).Admissible := by
  norm_num [Admissible, UniformSign, denominator_pos_two_iff, Fin.forall_fin_two]

theorem negative_denominator (A : Fin 2 → ℝ) (b : ℝ) :
    (⟨A, b, ![-1, -1], 3⟩ : AffineFraction 2).Admissible := by
  norm_num [Admissible, UniformSign, denominator_pos_two_iff, Fin.forall_fin_two]

theorem constant_positive (b : ℝ) :
    (⟨![1, 2], b, 0, 1⟩ : AffineFraction 2).Admissible := by
  norm_num [Admissible, UniformSign, denominator_pos_two_iff, Fin.forall_fin_two]

theorem constant_negative (b : ℝ) :
    (⟨![-1, -2], b, 0, 1⟩ : AffineFraction 2).Admissible := by
  norm_num [Admissible, UniformSign, denominator_pos_two_iff, Fin.forall_fin_two]

theorem constant_zero (b : ℝ) :
    (⟨0, b, 0, 1⟩ : AffineFraction 2).Admissible := by
  norm_num [Admissible, UniformSign, denominator_pos_two_iff, Fin.forall_fin_two]

theorem mixed_denominator (A : Fin 2 → ℝ) :
    ¬(⟨A, 0, ![1, -1], 3⟩ : AffineFraction 2).Admissible := by
  norm_num [Admissible, UniformSign, denominator_pos_two_iff, Fin.forall_fin_two]

theorem partially_zero_denominator (A : Fin 2 → ℝ) :
    ¬(⟨A, 0, ![1, 0], 1⟩ : AffineFraction 2).Admissible := by
  norm_num [Admissible, UniformSign, denominator_pos_two_iff, Fin.forall_fin_two]

theorem vanishing_denominator (A : Fin 2 → ℝ) :
    ¬(⟨A, 0, ![-1, -1], 2⟩ : AffineFraction 2).Admissible := by
  norm_num [Admissible, UniformSign, denominator_pos_two_iff, Fin.forall_fin_two]

theorem partially_zero_numerator :
    ¬(⟨![1, 0], 0, 0, 1⟩ : AffineFraction 2).Admissible := by
  norm_num [Admissible, UniformSign, denominator_pos_two_iff, Fin.forall_fin_two]

theorem difference_constant_not_admissible :
    ¬(⟨![1, -1], 0, 0, 1⟩ : AffineFraction 2).Admissible := by
  norm_num [Admissible, UniformSign, denominator_pos_two_iff, Fin.forall_fin_two]

/-- The inadmissible constant-denominator score has an admissible representation. -/
theorem difference_ratio (x : Fin 2 → Bool) :
    (⟨![2, -2], 0, ![1, 1], 1⟩ : AffineFraction 2).eval x =
      boolToReal (x 0) - boolToReal (x 1) := by
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [eval, numerator, denominator, Fin.sum_univ_two, boolToReal, h0, h1]

theorem difference_is_atom : ∃ φ : FracAtom 2, ∀ x,
    φ.eval x = boolToReal (x 0) - boolToReal (x 1) := by
  let r : AffineFraction 2 := ⟨![2, -2], 0, ![1, 1], 1⟩
  have hr : r.Admissible := by
    norm_num [r, Admissible, UniformSign, denominator_pos_two_iff, Fin.forall_fin_two]
  obtain ⟨φ, hφ⟩ := r.exists_atom hr
  exact ⟨φ, fun x ↦ by rw [φ.eval_eq, hφ]; exact difference_ratio x⟩

/-- Zero dimensions require exactly a positive constant denominator. -/
theorem dimension_zero (r : AffineFraction 0) :
    (∃ φ : FracAtom 0, φ.toAffineFraction = r) ↔ 0 < r.d := by
  rw [realizable_iff, admissible_zero]

/-- The free constant is realized exactly even with no attention heads. -/
theorem constant_score_zero_heads (n : ℕ) (c : ℝ) :
    ∃ d, ∃ M : SharedHeadFamily n d 0, ∃ (w : Vec d) (τ : ℝ),
      ∀ x, ⟪w, M.attnUpdate x⟫_ℝ - τ = c := by
  apply (shared_score_iff_affineFraction 0 (fun _ ↦ c)).mpr
  exact ⟨Fin.elim0, c, fun h ↦ Fin.elim0 h, fun _ ↦ by simp⟩

/-- Preserve the magnitude and offset of the score, beyond its Boolean sign. -/
theorem difference_plus_constant_is_shared_score (c : ℝ) :
    ∃ d, ∃ M : SharedHeadFamily 2 d 1, ∃ (w : Vec d) (τ : ℝ),
      ∀ x, ⟪w, M.attnUpdate x⟫_ℝ - τ =
        c + (boolToReal (x 0) - boolToReal (x 1)) := by
  apply (shared_score_iff_affineFraction 1 _).mpr
  refine ⟨fun _ ↦ ⟨![2, -2], 0, ![1, 1], 1⟩, c, ?_, ?_⟩
  · intro h
    norm_num [Admissible, UniformSign, denominator_pos_two_iff, Fin.forall_fin_two]
  · intro x
    simpa only [Fin.sum_univ_one] using congrArg (c + ·) (difference_ratio x)

end HeadComplexity.AffineFractionExamples
