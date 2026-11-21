import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

open Matrix

variable {J : Type*} [Fintype J]

/-- A Boolean moment matrix cannot be nonzero and positive semidefinite
when its distinguished row annihilates a strictly positive vector. -/
theorem booleanMoment_eq_zero_of_posSemidef
    (M : Matrix J J ℝ) (o : J) (b : J → ℝ)
    (hb : ∀ i, 0 < b i)
    (hd : ∀ i, M i i = M o i)
    (hk : ∑ i, M o i * b i = 0)
    (hM : M.PosSemidef) : M = 0 := by
  classical
  have hz : ∑ i, b i * M i i = 0 := by
    calc
      ∑ i, b i * M i i = ∑ i, M o i * b i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hd i, mul_comm]
      _ = 0 := hk
  have hd0 : ∀ i, M i i = 0 := by
    intro i
    have he : b i * M i i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg (hb j).le hM.diag_nonneg)).mp hz i (Finset.mem_univ i)
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt (hb i))
  apply hM.trace_eq_zero_iff.mp
  simp [Matrix.trace, hd0]

/-- A nonzero matrix satisfying the Boolean moment identities is neither
positive nor negative semidefinite. For symmetric matrices the next
theorem expresses this using quadratic forms. -/
theorem booleanMoment_not_semidefinite
    (M : Matrix J J ℝ) (o : J) (b : J → ℝ)
    (hb : ∀ i, 0 < b i)
    (hd : ∀ i, M i i = M o i)
    (hk : ∑ i, M o i * b i = 0)
    (hne : M ≠ 0) : ¬ M.PosSemidef ∧ ¬ (-M).PosSemidef := by
  constructor
  · intro hp
    exact hne (booleanMoment_eq_zero_of_posSemidef M o b hb hd hk hp)
  · intro hn
    have hn0 : -M = 0 := booleanMoment_eq_zero_of_posSemidef (-M) o b hb
      (by intro i; simpa only [Matrix.neg_apply] using congrArg Neg.neg (hd i))
      (by simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, hk,
        neg_zero]) hn
    exact hne (neg_eq_zero.mp hn0)

/-- Indefiniteness of the residual moment matrix does not assert
indefiniteness of the full squared-loss Hessian. -/
theorem booleanMoment_has_opposite_quadratic_signs
    (M : Matrix J J ℝ) (o : J) (b : J → ℝ)
    (hb : ∀ i, 0 < b i)
    (hd : ∀ i, M i i = M o i)
    (hk : ∑ i, M o i * b i = 0)
    (hs : M.IsHermitian) (hne : M ≠ 0) :
    (∃ v : J → ℝ, v ⬝ᵥ (M *ᵥ v) < 0) ∧
      (∃ v : J → ℝ, 0 < v ⬝ᵥ (M *ᵥ v)) := by
  classical
  obtain ⟨hp, hn⟩ := booleanMoment_not_semidefinite M o b hb hd hk hne
  constructor
  · by_contra h
    push Not at h
    apply hp
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hs
    intro v
    simpa using h v
  · by_contra h
    push Not at h
    apply hn
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hs.neg
    intro v
    simpa only [star_trivial, Matrix.neg_mulVec, dotProduct_neg, neg_nonneg]
      using h v

end HeadComplexity
