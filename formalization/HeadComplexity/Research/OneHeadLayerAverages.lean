import HeadComplexity.Atoms.PositiveAffineRatio
import HeadComplexity.Atoms.AtomicMargin
import HeadComplexity.Research.OneHeadMarginOptimum
import Mathlib.Tactic

set_option linter.style.header false

noncomputable section
namespace HeadComplexity.OneHeadLayerAverages
open Finset
open scoped BigOperators

abbrev Cube := Fin 5 → Bool

def thresholdTwo (x : Cube) : Bool :=
  decide (2 ≤ (Finset.univ.filter fun i => x i = true).card)

def singletonRow (j : Fin 5) : Cube := fun i => decide (i = j)
def pairRow (j : Fin 5) : Cube := fun i => decide (i = j ∨ i = j + 1)
def meanSlope (u : Fin 5 → ℝ) : ℝ := (∑ i, u i) / 5

@[simp] theorem label_zero : thresholdTwo (fun _ => false) = false := by decide
@[simp] theorem label_one : thresholdTwo (fun _ => true) = true := by decide
@[simp] theorem label_singleton (j : Fin 5) : thresholdTwo (singletonRow j) = false := by
  fin_cases j <;> decide
@[simp] theorem label_pair (j : Fin 5) : thresholdTwo (pairRow j) = true := by
  fin_cases j <;> decide

theorem sum_affine_singleton (c : ℝ) (u : Fin 5 → ℝ) :
    (∑ j, affineValue c u (singletonRow j)) = 5 * c + ∑ i, u i := by
  norm_num [affineValue, singletonRow, Fin.sum_univ_succ, boolToReal]
  ring

theorem sum_affine_pair (c : ℝ) (u : Fin 5 → ℝ) :
    (∑ j, affineValue c u (pairRow j)) = 5 * c + 2 * ∑ i, u i := by
  norm_num [affineValue, pairRow, Fin.sum_univ_succ, boolToReal]
  ring

theorem mean_affine_singleton (c : ℝ) (u : Fin 5 → ℝ) :
    (∑ j, affineValue c u (singletonRow j)) / 5 = c + meanSlope u := by
  rw [sum_affine_singleton]
  unfold meanSlope
  ring

theorem mean_affine_pair (c : ℝ) (u : Fin 5 → ℝ) :
    (∑ j, affineValue c u (pairRow j)) / 5 = c + 2 * meanSlope u := by
  rw [sum_affine_pair]
  unfold meanSlope
  ring

theorem affine_zero (c : ℝ) (u : Fin 5 → ℝ) :
    affineValue c u (fun _ => false) = c := by
  simp [affineValue, boolToReal]

theorem affine_one (c : ℝ) (u : Fin 5 → ℝ) :
    affineValue c u (fun _ => true) = c + 5 * meanSlope u := by
  simp [affineValue, boolToReal, meanSlope]
  ring

theorem affine_uniformSlope (a b : ℝ) (x : Cube) :
    affineValue a (fun _ => b) x =
      a + b * ((Finset.univ.filter fun i => x i = true).card : ℝ) := by
  unfold affineValue
  rw [← Finset.mul_sum]
  congr 1
  simp [boolToReal]

theorem label_true_iff (x : Cube) :
    thresholdTwo x = true ↔ 2 ≤ (Finset.univ.filter fun i => x i = true).card := by
  simp [thresholdTwo]

/-- The sharp affine ratio has a unit label gap and the stated norm bound at
all six Hamming layers. -/
theorem witness_layer_bounds (k : Fin 6) :
    let K := (11 + 4 * Real.sqrt 6) / 5
    let d := (K - 3) / 4
    let A := -K + (2 + 3 * d) * (k.val : ℝ)
    let B := 1 + d * (k.val : ℝ)
    0 < B ∧ |A / B| ≤ K ∧
      1 ≤ (if 2 ≤ k.val then (1 : ℝ) else -1) * (A / B) := by
  have hs : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have hs1 : 1 < Real.sqrt 6 := by nlinarith
  have hd : 0 < (((11 + 4 * Real.sqrt 6) / 5 - 3) / 4 : ℝ) := by linarith
  have hB : 0 < 1 + (((11 + 4 * Real.sqrt 6) / 5 - 3) / 4) *
      (k.val : ℝ) := by positivity
  fin_cases k <;> dsimp at hB ⊢
  all_goals
    refine ⟨hB, ?_, ?_⟩
    · rw [abs_le, le_div_iff₀ hB, div_le_iff₀ hB]
      constructor <;> norm_num <;> nlinarith
    · norm_num at hB ⊢
      first
      | nlinarith
      | rw [le_div_iff₀ hB]; norm_num; nlinarith
      | rw [← neg_div, le_div_iff₀ hB]; norm_num; nlinarith

/-- Five cyclic rows in each middle layer give the four scalar constraints;
no averaging of ratios or permutation-group argument is used. -/
theorem four_rows_of_affine_constraints (a c K : ℝ) (u v : Fin 5 → ℝ)
    (hB : ∀ x : Cube, 0 < affineValue c v x)
    (hneg : ∀ x : Cube, thresholdTwo x = false →
      -K * affineValue c v x ≤ affineValue a u x ∧
      affineValue a u x ≤ -affineValue c v x)
    (hpos : ∀ x : Cube, thresholdTwo x = true →
      affineValue c v x ≤ affineValue a u x ∧
      affineValue a u x ≤ K * affineValue c v x) :
    0 < c ∧ 0 < c + 5 * meanSlope v ∧
      -K * c ≤ a ∧ a + meanSlope u ≤ -(c + meanSlope v) ∧
      c + 2 * meanSlope v ≤ a + 2 * meanSlope u ∧
      a + 5 * meanSlope u ≤ K * (c + 5 * meanSlope v) := by
  have h0 := hneg (fun _ => false) label_zero
  have h5 := hpos (fun _ => true) label_one
  have h1 : (∑ j, affineValue a u (singletonRow j)) ≤
      -(∑ j, affineValue c v (singletonRow j)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun j _ => (hneg _ (label_singleton j)).2
  have h2 : (∑ j, affineValue c v (pairRow j)) ≤
      ∑ j, affineValue a u (pairRow j) :=
    Finset.sum_le_sum fun j _ => (hpos _ (label_pair j)).1
  have hm1 := div_le_div_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 5)
  have hm2 := div_le_div_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ 5)
  rw [neg_div, mean_affine_singleton, mean_affine_singleton] at hm1
  rw [mean_affine_pair, mean_affine_pair] at hm2
  refine ⟨?_, ?_, ?_, hm1, hm2, ?_⟩
  · simpa [affine_zero] using hB (fun _ => false)
  · simpa [affine_one] using hB (fun _ => true)
  · simpa [affine_zero] using h0.1
  · simpa [affine_one] using h5.2

/-- Every cube-positive affine ratio representing the threshold has the sharp
norm budget. This permits arbitrary denominator slope signs. -/
theorem affine_ratio_budget (a0 b0 K : ℝ) (a b : Fin 5 → ℝ)
    (hB : ∀ x : Cube, 0 < affineValue b0 b x)
    (hnorm : ∀ x : Cube, |affineValue a0 a x / affineValue b0 b x| ≤ K)
    (hgap : ∀ x : Cube, 1 ≤ signedLabel thresholdTwo x *
      (affineValue a0 a x / affineValue b0 b x)) :
    (11 + 4 * Real.sqrt 6) / 5 ≤ K := by
  have hneg : ∀ x : Cube, thresholdTwo x = false →
      -K * affineValue b0 b x ≤ affineValue a0 a x ∧
      affineValue a0 a x ≤ -affineValue b0 b x := by
    intro x hx
    have hlow := (abs_le.mp (hnorm x)).1
    have hg := hgap x
    rw [signedLabel_of_false hx, neg_one_mul] at hg
    refine ⟨(le_div_iff₀ (hB x)).mp hlow, ?_⟩
    have hd : affineValue a0 a x / affineValue b0 b x ≤ -1 := by linarith
    simpa using (div_le_iff₀ (hB x)).mp hd
  have hpos : ∀ x : Cube, thresholdTwo x = true →
      affineValue b0 b x ≤ affineValue a0 a x ∧
      affineValue a0 a x ≤ K * affineValue b0 b x := by
    intro x hx
    have hg := hgap x
    rw [signedLabel_of_true hx, one_mul] at hg
    exact ⟨by simpa using (le_div_iff₀ (hB x)).mp hg,
      (div_le_iff₀ (hB x)).mp (abs_le.mp (hnorm x)).2⟩
  obtain ⟨hc, h5p, h0, h1, h2, h5⟩ :=
    four_rows_of_affine_constraints a0 b0 K a b hB hneg hpos
  exact OneHeadMarginOptimum.four_row_budget_sharp a0 (meanSlope a)
    b0 (meanSlope b) K hc h5p h0 h1 h2 h5

end HeadComplexity.OneHeadLayerAverages
