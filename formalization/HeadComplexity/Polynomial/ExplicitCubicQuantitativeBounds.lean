import HeadComplexity.Polynomial.ExplicitCubicRawObstruction
import HeadComplexity.Polynomial.FiniteGridPole
import HeadComplexity.Results.PureRoPEReplicationStrict
import Mathlib.LinearAlgebra.Matrix.Block

set_option linter.style.header false

/-!
# Exact quantitative bounds for the explicit cubic Hessian

The first six coefficient rows have an explicit triangular factorization. The
resulting determinant and bounded pole point give a uniform positive minor.
-/

namespace HeadComplexity.ExplicitCubicQuantitativeBounds
noncomputable section
open scoped BigOperators Matrix
open PureRoPEReplication GenericCubicHessianPullback ExplicitCubicRawObstruction

private def lower : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1,0,0,0,0,0; 1,1,0,0,0,0; 1,2,1,0,0,0;
     1,3,3,1,0,0; 1,4,6,4,1,0; 1,5,10,10,5,1]

private def upper : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1/10000,1/10000,1/10000,-3367/8000000000,-50609/16000000000,-759343/32000000000;
     0,1/10000,3/10000,7/1000000000,3/200000000,31/1000000000;
     0,0,1/5000,3/250000000,1/20000000,9/50000000;
     0,0,0,3/500000000,3/50000000,39/100000000;
     0,0,0,0,3/125000000,9/25000000;
     0,0,0,0,0,3/25000000]

private theorem lower_triangular : lower.BlockTriangular OrderDual.toDual := by
  intro i j h
  change i < j at h
  fin_cases i <;> fin_cases j <;> norm_num [lower] at *

private theorem upper_triangular : upper.BlockTriangular id := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [upper] at *

set_option maxHeartbeats 4000000 in
-- Verify all 36 entries of the rational triangular factorization directly.
private theorem firstMinor_factorization :
    firstMinor.submatrix finSumFinEquiv.symm finSumFinEquiv.symm = lower * upper := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstMinor, firstSix, slopes, baseS, baseB, lower, upper,
      Matrix.mul_apply, Matrix.submatrix_apply, Fin.sum_univ_succ,
      finSumFinEquiv, Fin.addCases]

def vandermondeBound : ℝ := 34560 / 10 ^ 39

theorem vandermondeBound_pos : 0 < vandermondeBound := by norm_num [vandermondeBound]

theorem firstMinor_det : firstMinor.det = vandermondeBound := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv.symm firstMinor,
    firstMinor_factorization, Matrix.det_mul,
    Matrix.det_of_lowerTriangular lower lower_triangular,
    Matrix.det_of_upperTriangular upper_triangular]
  norm_num [lower, upper, Fin.prod_univ_succ, vandermondeBound]

theorem value_abs_le_two_sum {n : ℕ} (a w : Fin n → ℝ) (hw : ∀ i, |w i| ≤ 2) :
    |FiniteGridPole.value a w| ≤ 2 * ∑ i, |a i| := by
  calc
    _ ≤ ∑ i, |a i * w i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |w i| := by simp_rw [abs_mul]
    _ ≤ ∑ i, |a i| * 2 := Finset.sum_le_sum
      (fun i _ ↦ mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem latent_values_lt_two (w : Fin 14 → ℝ) (hw : ∀ i, |w i| ≤ 2) (h : Fin 3) :
    |linearValue (baseS h) w| < 2 ∧ |linearValue (baseB h) w| < 2 := by
  have hS : ∑ i, |baseS h i| < 1 := by
    have hp (i : Fin 14) : 0 ≤ baseS h i := (abs_nonneg (baseB h i)).trans (base_mass h i).le
    simpa only [abs_of_nonneg (hp _)] using base_sum h
  have hB := PureRoPEReplicationStrict.sum_abs_baseB_lt_one h
  have hs := value_abs_le_two_sum (baseS h) w hw
  have hb := value_abs_le_two_sum (baseB h) w hw
  change |FiniteGridPole.value (baseS h) w| < 2 ∧ |FiniteGridPole.value (baseB h) w| < 2
  constructor <;> linarith

theorem slopes_abs_le_one (i : Fin 14) (h : Fin 3 ⊕ Fin 3) :
    |slopes baseS baseB i h| ≤ 1 := by
  rcases h with h | h <;> fin_cases h <;> fin_cases i <;>
    norm_num [slopes, baseS, baseB]

theorem latent_hessian_entry_le_two (s b : Fin 3 → ℝ)
    (hs : ∀ i, |s i| ≤ 2) (hb : ∀ i, |b i| ≤ 2) (i j : Fin 3 ⊕ Fin 3) :
    |GenericCubicHessian.hessian s b i j| ≤ 2 := by
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp_all [GenericCubicHessian.hessian, GenericCubicHessian.offDiagonal,
      Matrix.fromBlocks, Matrix.transpose_apply]

theorem pullback_entry_le_seventy_two {n : ℕ}
    (V : Matrix (Fin n) (Fin 3 ⊕ Fin 3) ℝ)
    (H : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ)
    (hV : ∀ i j, |V i j| ≤ 1) (hH : ∀ i j, |H i j| ≤ 2) (i j : Fin n) :
    |(V * H * Vᵀ) i j| ≤ 72 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  calc
    _ ≤ ∑ k, |∑ l, V i l * H l k * V j k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ∑ l, |V i l * H l k * V j k| :=
      Finset.sum_le_sum (fun k _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ k : Fin 3 ⊕ Fin 3, ∑ l : Fin 3 ⊕ Fin 3, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      calc
        _ = |V i l| * |H l k| * |V j k| := by rw [abs_mul, abs_mul]
        _ ≤ 1 * 2 * 1 := by gcongr <;> first | exact hV _ _ | exact hH _ _
        _ = 2 := by norm_num
    _ = 72 := by norm_num

theorem target_hessian_entry_le_seventy_two (w : Fin 14 → ℝ)
    (hw : ∀ i, |w i| ≤ 2) (i j : Fin 14) :
    |polynomialHessian (cubic baseS baseB) w i j| ≤ 72 := by
  rw [hessian_pullback]
  apply pullback_entry_le_seventy_two _ _ slopes_abs_le_one
  intro p q
  exact latent_hessian_entry_le_two _ _
    (fun h ↦ (latent_values_lt_two w hw h).1.le)
    (fun h ↦ (latent_values_lt_two w hw h).2.le) p q

def targetMinor (w : Fin 14 → ℝ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  (polynomialHessian (cubic baseS baseB) w).submatrix firstSix firstSix

def minorGap : ℝ := 4 * vandermondeBound ^ 2 * (FiniteGridPole.explicitDelta / 12) ^ 6

theorem minorGap_pos : 0 < minorGap := by
  have hv := vandermondeBound_pos
  have hd := FiniteGridPole.explicitDelta_pos
  dsimp only [minorGap]
  positivity

theorem targetMinor_abs_det (w : Fin 14 → ℝ) :
    |(targetMinor w).det| = 4 * vandermondeBound ^ 2 *
      (|linearValue (baseB 0) w| * |linearValue (baseB 1) w| *
        |linearValue (baseB 2) w|) ^ 2 := by
  rw [targetMinor, cross_hessian_det]
  change |-4 * firstMinor.det * firstMinor.det *
    (linearValue (baseB 0) w * linearValue (baseB 1) w * linearValue (baseB 2) w) ^ 2| = _
  rw [firstMinor_det]
  simp only [abs_mul, abs_pow, abs_of_pos vandermondeBound_pos]
  rw [show |(-4 : ℝ)| = 4 by norm_num]
  ring

theorem targetMinor_abs_det_lower (w : Fin 14 → ℝ)
    (hB : ∀ h, FiniteGridPole.explicitDelta / 12 ≤ |linearValue (baseB h) w|) :
    minorGap ≤ |(targetMinor w).det| := by
  rw [targetMinor_abs_det]
  have hd : 0 ≤ FiniteGridPole.explicitDelta / 12 := by
    exact div_nonneg FiniteGridPole.explicitDelta_pos.le (by norm_num)
  have hp : (FiniteGridPole.explicitDelta / 12) ^ 3 ≤
      |linearValue (baseB 0) w| * |linearValue (baseB 1) w| *
        |linearValue (baseB 2) w| := by
    calc
      _ = (FiniteGridPole.explicitDelta / 12) * (FiniteGridPole.explicitDelta / 12) *
          (FiniteGridPole.explicitDelta / 12) := by ring
      _ ≤ _ := by gcongr <;> exact hB _
  dsimp only [minorGap]
  have hs : (FiniteGridPole.explicitDelta / 12) ^ 6 ≤
      (|linearValue (baseB 0) w| * |linearValue (baseB 1) w| *
        |linearValue (baseB 2) w|) ^ 2 := by
    calc
      _ = ((FiniteGridPole.explicitDelta / 12) ^ 3) ^ 2 := by ring
      _ ≤ _ := by gcongr
  exact mul_le_mul_of_nonneg_left hs (by positivity)

/-- At every normalized nonnegative competitor pole, the concrete target has
a uniformly nonzero six-coordinate minor and uniformly bounded entries. -/
theorem exists_pole_with_bounded_nonsingular_minor (d : Fin 14 → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hs : ∑ i, d i = 1) :
    ∃ w : Fin 14 → ℝ, FiniteGridPole.value d w = 0 ∧
      (∀ i, |w i| ≤ 2) ∧
      (∀ i j, |targetMinor w i j| ≤ 72) ∧ minorGap ≤ |(targetMinor w).det| := by
  obtain ⟨w, hp, hw, hB⟩ := FiniteGridPole.explicit_bounded_pole_point d hd hs
  refine ⟨w, hp, hw, ?_, targetMinor_abs_det_lower w hB⟩
  intro i j
  exact target_hessian_entry_le_seventy_two w hw (firstSix i) (firstSix j)

end
end HeadComplexity.ExplicitCubicQuantitativeBounds
