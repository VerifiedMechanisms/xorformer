import HeadComplexity.Polynomial.ThreeHeadMeanGap
import HeadComplexity.Polynomial.ReplicatedMeanGrid

set_option linter.style.header false

/-! # Untied vanilla heads preserve the exact Boolean classifier after group averaging -/

namespace HeadComplexity.ThreeHeadMeanSign

noncomputable section

open MvPolynomial ThreeHeadMeanGap PureRoPEReplication PureRoPEReplicationStrict
open PureCubicRawKernel MeanGridCubic MeanGridSymmetrization
open scoped BigOperators

theorem centered_affine_eval {n m : ℕ} (b : ℝ) (a : Fin (n * m) → ℝ)
    (x : Fin (n * m) → Bool) :
    eval (fun p : Fin n × Fin m ↦ PureRoPECenteredConstruction.spin (x (finProdFinEquiv p)))
      (affine (b + ∑ p : Fin n × Fin m, a (finProdFinEquiv p) / 2)
        (fun p ↦ a (finProdFinEquiv p) / 2)) =
      b + ∑ i, a i * boolToReal (x i) := by
  simp only [affine, map_add, eval_C, map_sum, map_mul, eval_X]
  rw [add_assoc, ← Finset.sum_add_distrib,
    ← (finProdFinEquiv (m := n) (n := m)).sum_comp]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  cases hx : x (finProdFinEquiv p) <;>
    norm_num [PureRoPECenteredConstruction.spin, boolToReal, hx]

theorem spinCleared_eval {m : ℕ} (r : Fin 3 → AffineFraction (14 * m)) (c : ℝ)
    (hr : ∀ h, (r h).Admissible) (x : Fin (14 * m) → Bool) :
    eval (fun p : Fin 14 × Fin m ↦ PureRoPECenteredConstruction.spin (x (finProdFinEquiv p)))
      (spinCleared r c) =
    ((r 0).denominator x * (r 1).denominator x * (r 2).denominator x) *
      (c + ∑ h, (r h).eval x) := by
  have hn (h : Fin 3) : eval
      (fun p : Fin 14 × Fin m ↦ PureRoPECenteredConstruction.spin (x (finProdFinEquiv p)))
      (affine (numConstant r h) (numSlopes r h)) = (r h).numerator x :=
    centered_affine_eval _ _ _
  have hd (h : Fin 3) : eval
      (fun p : Fin 14 × Fin m ↦ PureRoPECenteredConstruction.spin (x (finProdFinEquiv p)))
      (affine (denConstant r h) (denSlopes r h)) = (r h).denominator x :=
    centered_affine_eval _ _ _
  simp only [spinCleared, cleared, map_add, map_mul, eval_C, hn, hd]
  exact ThreeHeadCubicFace.cleared_eq c (fun h ↦ (r h).numerator x)
    (fun h ↦ (r h).denominator x) (fun h ↦ ((hr h).1 x).ne')

theorem spinCleared_positive_iff {m : ℕ} (r : Fin 3 → AffineFraction (14 * m)) (c : ℝ)
    (hr : ∀ h, (r h).Admissible) (x : Fin (14 * m) → Bool) :
    (0 < eval
      (fun p : Fin 14 × Fin m ↦ PureRoPECenteredConstruction.spin (x (finProdFinEquiv p)))
      (spinCleared r c)) ↔ 0 < c + ∑ h, (r h).eval x := by
  rw [spinCleared_eval r c hr x]
  exact mul_pos_iff_of_pos_left (mul_pos (mul_pos ((hr 0).1 x) ((hr 1).1 x)) ((hr 2).1 x))

def permuteInput {n m : ℕ} (x : Fin (n * m) → Bool)
    (σ : Fin n → Equiv.Perm (Fin m)) (j : Fin (n * m)) : Bool :=
  let p := (finProdFinEquiv (m := n) (n := m)).symm j
  x (finProdFinEquiv (p.1, σ p.1 p.2))

theorem means_permuteInput {n m : ℕ} (x : Fin (n * m) → Bool)
    (σ : Fin n → Equiv.Perm (Fin m)) : means (permuteInput x σ) = means x := by
  funext i
  simp only [means, permuteInput, Equiv.symm_apply_apply]
  congr 1
  exact Equiv.sum_comp (σ i)
    (fun r ↦ PureRoPECenteredConstruction.spin (x (finProdFinEquiv (i, r))))

theorem unshifted_permuteInput {m : ℕ} (x : Fin (14 * m) → Bool)
    (σ : Fin 14 → Equiv.Perm (Fin m)) :
    unshiftedFunction (permuteInput x σ) = unshiftedFunction x := by
  unfold unshiftedFunction
  rw [← eval_rawTarget_means, ← eval_rawTarget_means, means_permuteInput]

/-- Averaging applies to every admissible vanilla representation, without
requiring tied parameters or strict negative scores. -/
theorem meanCleared_sign {m : ℕ} (hm : 2 < m)
    (r : Fin 3 → AffineFraction (14 * m)) (c : ℝ)
    (hr : ∀ h, (r h).Admissible)
    (hclass : ∀ x : Fin (14 * m) → Bool,
      (0 < c + ∑ h, (r h).eval x ↔ unshiftedFunction x = true))
    (x : Fin (14 * m) → Bool) :
    0 < eval (means x) (meanCleared r c) ↔ unshiftedFunction x = true := by
  let z : Fin 14 × Fin m → ℝ :=
    fun p ↦ PureRoPECenteredConstruction.spin (x (finProdFinEquiv p))
  have hz (p) : z p ^ 2 = 1 := by
    dsimp [z, PureRoPECenteredConstruction.spin]
    split_ifs <;> norm_num
  have hmean : (fun i ↦ (∑ r, z (i, r)) / m) = means x := rfl
  rw [meanCleared, ← hmean,
    ← average_polynomial_eq hm (spinCleared r c) (spinCleared_degree r c) z hz]
  apply average_sign
  intro σ
  have he : (fun p : Fin 14 × Fin m ↦ z (p.1, σ p.1 p.2)) =
      fun p ↦ PureRoPECenteredConstruction.spin (permuteInput x σ (finProdFinEquiv p)) := by
    funext p
    simp [z, permuteInput]
  rw [he, spinCleared_positive_iff r c hr, hclass, unshifted_permuteInput]

end
end HeadComplexity.ThreeHeadMeanSign
