import HeadComplexity.Polynomial.FiniteGridAvoidance
import HeadComplexity.Results.PureRoPEReplication

set_option linter.style.header false

/-!
# Quantitative avoidance on every normalized nonnegative pole

Project the five-point cube onto the kernel of a nonnegative linear functional
whose coefficient sum is one. Uniformly mixed forms retain a large coefficient
after projection, so all three stay uniformly nonzero at one bounded pole point.
-/

namespace HeadComplexity.FiniteGridPole
noncomputable section
open scoped BigOperators

def value {n : ℕ} (a z : Fin n → ℝ) : ℝ := ∑ i, a i * z i

def project {n : ℕ} (d z : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ z i - value d z

def projectedCoefficients {n : ℕ} (b d : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ b i - (∑ j, b j) * d i

theorem value_project {n : ℕ} (b d z : Fin n → ℝ) :
    value b (project d z) = value (projectedCoefficients b d) z := by
  simp only [value, project, projectedCoefficients, mul_sub, sub_mul,
    Finset.sum_sub_distrib, ← Finset.sum_mul, mul_assoc, ← Finset.mul_sum]

theorem project_on_pole {n : ℕ} (d z : Fin n → ℝ) (hd : ∑ i, d i = 1) :
    value d (project d z) = 0 := by
  simp only [value, project, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hd]
  ring

theorem value_abs_le_one {n : ℕ} (d z : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hs : ∑ i, d i = 1) (hz : ∀ i, |z i| ≤ 1) :
    |value d z| ≤ 1 := by
  calc
    |value d z| ≤ ∑ i, |d i * z i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, d i * |z i| := by simp_rw [abs_mul, abs_of_nonneg (hd _)]
    _ ≤ ∑ i, d i := Finset.sum_le_sum (fun i _ ↦ by nlinarith [hd i, hz i])
    _ = 1 := hs

theorem project_abs_le_two {n : ℕ} (d z : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hs : ∑ i, d i = 1) (hz : ∀ i, |z i| ≤ 1) (i : Fin n) :
    |project d z i| ≤ 2 := by
  have hv := value_abs_le_one d z hd hs hz
  have ht : |z i - value d z| ≤ |z i| + |value d z| := by
    simpa using abs_sub_le (z i) 0 (value d z)
  dsimp only [project]
  linarith [hz i]

theorem projected_coefficient_large {n : ℕ} (b d : Fin n → ℝ) (δ : ℝ)
    (hd : ∀ i, 0 ≤ d i) (hb : ∃ i j, δ ≤ b i ∧ b j ≤ -δ) :
    ∃ j, δ ≤ |projectedCoefficients b d j| := by
  obtain ⟨i, j, hi, hj⟩ := hb
  by_cases hs : 0 ≤ ∑ k, b k
  · refine ⟨j, ?_⟩
    have hm := mul_nonneg hs (hd j)
    have ha := neg_le_abs (projectedCoefficients b d j)
    dsimp only [projectedCoefficients] at ha ⊢
    linarith
  · refine ⟨i, ?_⟩
    have hm : (∑ k, b k) * d i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) (hd i)
    have ha := le_abs_self (projectedCoefficients b d i)
    dsimp only [projectedCoefficients] at ha ⊢
    linarith

/-- The uniform finite-grid point used before the quantitative Hessian estimate.
The direction may have zero coordinates; no strict positivity is required. -/
theorem exists_bounded_pole_point {n : ℕ} (B : Fin 3 → Fin (n + 1) → ℝ)
    (d : Fin (n + 1) → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hd : ∀ i, 0 ≤ d i) (hs : ∑ i, d i = 1)
    (hB : ∀ h, ∃ i j, δ ≤ B h i ∧ B h j ≤ -δ) :
    ∃ w : Fin (n + 1) → ℝ, value d w = 0 ∧
      (∀ i, |w i| ≤ 2) ∧ ∀ h, δ / 12 ≤ |value (B h) w| := by
  have hc (h : Fin 3) : ∃ j, δ ≤ |projectedCoefficients (B h) d j| :=
    projected_coefficient_large (B h) d δ hd (hB h)
  obtain ⟨z, _, hz, hlarge⟩ := FiniteGridAvoidance.exists_cube_point_avoids_three
    (fun h ↦ projectedCoefficients (B h) d) δ hδ hc
  refine ⟨project d z, project_on_pole d z hs, project_abs_le_two d z hd hs hz, ?_⟩
  intro h
  rw [value_project]
  exact hlarge h

/-- A single rational lower bound for both signs in all three explicit forms. -/
def explicitDelta : ℝ := 3367 / 8000000000

theorem explicitDelta_pos : 0 < explicitDelta := by norm_num [explicitDelta]

theorem baseB_uniformly_mixed (h : Fin 3) :
    ∃ i j, explicitDelta ≤ PureRoPEReplication.baseB h i ∧
      PureRoPEReplication.baseB h j ≤ -explicitDelta := by
  refine ⟨13, 0, ?_⟩
  fin_cases h <;> norm_num [PureRoPEReplication.baseB, explicitDelta]

/-- The concrete target has a uniformly bounded nonsingular pole point for
every nonnegative normalized competing denominator direction. -/
theorem explicit_bounded_pole_point (d : Fin 14 → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hs : ∑ i, d i = 1) :
    ∃ w : Fin 14 → ℝ, value d w = 0 ∧
      (∀ i, |w i| ≤ 2) ∧
      ∀ h, explicitDelta / 12 ≤ |value (PureRoPEReplication.baseB h) w| :=
  exists_bounded_pole_point PureRoPEReplication.baseB d explicitDelta
    explicitDelta_pos hd hs baseB_uniformly_mixed

end
end HeadComplexity.FiniteGridPole
