import HeadComplexity.Atoms.PositiveAffineRatio
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Fixed-direction reciprocal and exponential sign separation

This is an auxiliary obstruction, not an improved worst-case head lower bound.
Two admissible reciprocal heads realize an explicit four-bit Boolean table.
For every real scale, the corresponding two exponential directions, with
arbitrary affine numerators and arbitrary bias, cannot realize that table.
-/

namespace HeadComplexity.RadialSpanSeparation

abbrev Cube := Fin 4 → Bool

noncomputable def total (x : Cube) : ℝ :=
  boolToReal (x 0) + boolToReal (x 1) + boolToReal (x 2) + boolToReal (x 3)

noncomputable def delta (x : Cube) : ℝ :=
  boolToReal (x 0) + boolToReal (x 1)

noncomputable def difference (x : Cube) : ℝ :=
  boolToReal (x 0) - boolToReal (x 1)

def target (x : Cube) : Bool :=
  (x 0 && !x 1 && (x 2 || x 3)) || (!x 0 && x 1 && !x 2 && !x 3)

noncomputable def reciprocalScore (x : Cube) : ℝ :=
  (-22 * difference x) / (1 + total x / 4) +
    (26 * difference x - 1 / 4) / (1 + (total x + delta x) / 4)

noncomputable def numeratorConstants : Fin 2 → ℝ := ![0, -(1 / 4)]

noncomputable def numeratorSlopes : Fin 2 → Fin 4 → ℝ :=
  ![![-22, 22, 0, 0], ![26, -26, 0, 0]]

noncomputable def denominatorSlopes : Fin 2 → Fin 4 → ℝ :=
  ![![1 / 4, 1 / 4, 1 / 4, 1 / 4], ![1 / 2, 1 / 2, 1 / 4, 1 / 4]]

theorem denominatorSlopes_pos (h : Fin 2) (i : Fin 4) :
    0 < denominatorSlopes h i := by
  fin_cases h <;> fin_cases i <;> norm_num [denominatorSlopes]

theorem denominator_pos (h : Fin 2) (x : Cube) :
    0 < affineValue 1 (denominatorSlopes h) x :=
  affineValue_pos 1 (denominatorSlopes h) (by norm_num)
    (denominatorSlopes_pos h) x

theorem reciprocalScore_eq (x : Cube) :
    (∑ h : Fin 2, affineValue (numeratorConstants h) (numeratorSlopes h) x /
      affineValue 1 (denominatorSlopes h) x) = reciprocalScore x := by
  simp [Fin.sum_univ_succ, affineValue, numeratorConstants, numeratorSlopes,
    denominatorSlopes, reciprocalScore, difference, total, delta]
  congr 1 <;> congr 1 <;> ring

theorem reciprocalScore_strict (x : Cube) : reciprocalScore x ≠ 0 := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    norm_num [reciprocalScore, difference, total, delta, boolToReal, h0, h1, h2, h3]

theorem reciprocalScore_sign (x : Cube) :
    0 < reciprocalScore x ↔ target x = true := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    norm_num [reciprocalScore, target, difference, total, delta, boolToReal,
      h0, h1, h2, h3]

/-- This conclusion is about the original shared-attention head model. -/
theorem target_computableWith_two_heads : computableWithHeadsN 4 2 target := by
  apply computableWithHeadsN_of_positiveAffineRatios
    numeratorConstants numeratorSlopes (fun _ ↦ 1) denominatorSlopes
    (fun _ ↦ by norm_num) denominatorSlopes_pos 0
  intro x
  simpa only [zero_add, reciprocalScore_eq] using reciprocalScore_sign x

def leftZero : Cube := ![true, false, false, false]
def rightZero : Cube := ![false, true, false, false]
def leftOne : Cube := ![true, false, true, false]
def rightOne : Cube := ![false, true, true, false]

noncomputable def exponentialScore (t c u₀ : ℝ) (u : Fin 4 → ℝ)
    (v₀ : ℝ) (v : Fin 4 → ℝ) (x : Cube) : ℝ :=
  c + affineValue u₀ u x * Real.exp (-t * total x) +
    affineValue v₀ v x * Real.exp (-t * (total x + delta x))

/-- On these two equal-statistic prefix rows, the difference changes only
by a positive scalar as the third bit changes. -/
theorem exponential_rectangle_identity (t c u₀ : ℝ) (u : Fin 4 → ℝ)
    (v₀ : ℝ) (v : Fin 4 → ℝ) :
    exponentialScore t c u₀ u v₀ v leftOne -
      exponentialScore t c u₀ u v₀ v rightOne =
    Real.exp (-t) * (exponentialScore t c u₀ u v₀ v leftZero -
      exponentialScore t c u₀ u v₀ v rightZero) := by
  have e₂ : Real.exp (-t * 2) = Real.exp (-t) * Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e₃ : Real.exp (-t * 3) = Real.exp (-t) * Real.exp (-t * 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  norm_num [exponentialScore, affineValue, Fin.sum_univ_succ,
    leftOne, rightOne, leftZero, rightZero, total, delta, boolToReal]
  simp only [← neg_mul]
  rw [e₃, e₂]
  ring

/-- No choice of affine numerators or output bias repairs these fixed
exponential directions, even under the original weak false-label convention. -/
theorem not_exponentialScore_represents_target (t c u₀ : ℝ)
    (u : Fin 4 → ℝ) (v₀ : ℝ) (v : Fin 4 → ℝ) :
    ¬ (∀ x : Cube, 0 < exponentialScore t c u₀ u v₀ v x ↔ target x = true) := by
  intro h
  have hlz : exponentialScore t c u₀ u v₀ v leftZero ≤ 0 := by
    apply le_of_not_gt
    simpa [target, leftZero] using h leftZero
  have hrz : 0 < exponentialScore t c u₀ u v₀ v rightZero := by
    exact (h rightZero).mpr (by simp [target, rightZero])
  have hlo : 0 < exponentialScore t c u₀ u v₀ v leftOne := by
    exact (h leftOne).mpr (by simp [target, leftOne])
  have hro : exponentialScore t c u₀ u v₀ v rightOne ≤ 0 := by
    apply le_of_not_gt
    simpa [target, rightOne] using h rightOne
  have hz : exponentialScore t c u₀ u v₀ v leftZero -
      exponentialScore t c u₀ u v₀ v rightZero < 0 := by linarith
  have hp := mul_neg_of_pos_of_neg (Real.exp_pos (-t)) hz
  have hid := exponential_rectangle_identity t c u₀ u v₀ v
  linarith

#print axioms target_computableWith_two_heads
#print axioms not_exponentialScore_represents_target

end HeadComplexity.RadialSpanSeparation
