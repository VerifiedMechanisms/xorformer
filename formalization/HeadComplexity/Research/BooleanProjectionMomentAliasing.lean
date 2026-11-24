import HeadComplexity.Atoms.UniformApproximation

set_option linter.style.header false

/-!
# Boolean projections do not determine ordinary mixed moments

Two distinct positive three-point direction clouds have the same projected
multiset in every Boolean direction. Thus every scalar moment, and every
reciprocal evaluation, agrees on the entire Boolean cube. Their ordinary mixed
cubic moments differ. This is an exact obstruction to replacing Boolean
collision-moment identities by full multivariate moment identities.
-/

noncomputable section

namespace HeadComplexity.BooleanProjectionMomentAliasing

open Finset
open scoped BigOperators

def positiveFirst : Fin 3 → ℝ := ![3, 2, 1]
def positiveSecond : Fin 3 → ℝ := ![2, 1, 3]
def negativeFirst : Fin 3 → ℝ := ![1, 3, 2]
def negativeSecond : Fin 3 → ℝ := ![2, 1, 3]

def projection (p q : ℝ) (x : Fin 2 → Bool) : ℝ :=
  p * boolToReal (x 0) + q * boolToReal (x 1)

/-- The two direction clouds have identical projection multisets on all four
Boolean directions. The statement permits every scalar function, not just
polynomials. -/
theorem scalar_function_identity (F : ℝ → ℝ) (a ε : ℝ) (x : Fin 2 → Bool) :
    (∑ h, F (a + ε * projection (positiveFirst h) (positiveSecond h) x)) =
      ∑ h, F (a + ε * projection (negativeFirst h) (negativeSecond h) x) := by
  cases hx₀ : x 0 <;> cases hx₁ : x 1 <;>
    simp [Fin.sum_univ_three, positiveFirst, positiveSecond, negativeFirst,
      negativeSecond, projection, boolToReal, hx₀, hx₁] <;> ring_nf

/-- All Boolean-projection moments agree, including arbitrarily high orders. -/
theorem all_projection_moments (q : ℕ) (a ε : ℝ) (x : Fin 2 → Bool) :
    (∑ h, (a + ε * projection (positiveFirst h) (positiveSecond h) x) ^ q) =
      ∑ h, (a + ε * projection (negativeFirst h) (negativeSecond h) x) ^ q :=
  scalar_function_identity (fun t ↦ t ^ q) a ε x

/-- The ordinary mixed cubic moment is not determined by these identities. -/
theorem mixed_moment_21_difference :
    (∑ h, positiveFirst h ^ 2 * positiveSecond h) -
      (∑ h, negativeFirst h ^ 2 * negativeSecond h) = 2 := by
  norm_num [Fin.sum_univ_three, positiveFirst, positiveSecond, negativeFirst,
    negativeSecond]

theorem mixed_moment_12_difference :
    (∑ h, positiveFirst h * positiveSecond h ^ 2) -
      (∑ h, negativeFirst h * negativeSecond h ^ 2) = -2 := by
  norm_num [Fin.sum_univ_three, positiveFirst, positiveSecond, negativeFirst,
    negativeSecond]

/-- Before restricting to Boolean inputs, the cubic projection discrepancy is
a nonzero polynomial in the Boolean vanishing ideal. -/
theorem cubic_projection_difference (x y : ℝ) :
    (∑ h, (positiveFirst h * x + positiveSecond h * y) ^ 3) -
      (∑ h, (negativeFirst h * x + negativeSecond h * y) ^ 3) =
        6 * x * y * (x - y) := by
  norm_num [Fin.sum_univ_three, positiveFirst, positiveSecond, negativeFirst,
    negativeSecond]
  ring

private theorem positive_direction (h : Fin 3) (i : Fin 2) :
    0 < (![positiveFirst h, positiveSecond h] : Fin 2 → ℝ) i := by
  fin_cases h <;> fin_cases i <;>
    norm_num [positiveFirst, positiveSecond]

private theorem negative_direction (h : Fin 3) (i : Fin 2) :
    0 < (![negativeFirst h, negativeSecond h] : Fin 2 → ℝ) i := by
  fin_cases h <;> fin_cases i <;>
    norm_num [negativeFirst, negativeSecond]

def positiveAtom (ε : ℝ) (hε : 0 < ε) (h : Fin 3) : FracAtom 2 :=
  FracAtom.ofPositiveAffineRatio 1 (fun _ ↦ 0) 1
    (fun i ↦ ε * (![positiveFirst h, positiveSecond h] : Fin 2 → ℝ) i)
    one_pos (fun i ↦ mul_pos hε (positive_direction h i))

def negativeAtom (ε : ℝ) (hε : 0 < ε) (h : Fin 3) : FracAtom 2 :=
  FracAtom.ofPositiveAffineRatio (-1) (fun _ ↦ 0) 1
    (fun i ↦ ε * (![negativeFirst h, negativeSecond h] : Fin 2 → ℝ) i)
    one_pos (fun i ↦ mul_pos hε (negative_direction h i))

theorem positiveAtom_eval (ε : ℝ) (hε : 0 < ε) (h : Fin 3)
    (x : Fin 2 → Bool) :
    (positiveAtom ε hε h).eval x =
      1 / (1 + ε * projection (positiveFirst h) (positiveSecond h) x) := by
  rw [positiveAtom, FracAtom.ofPositiveAffineRatio_eval]
  simp only [affineValue, Fin.sum_univ_two, zero_mul, add_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  simp only [projection]
  ring

theorem negativeAtom_eval (ε : ℝ) (hε : 0 < ε) (h : Fin 3)
    (x : Fin 2 → Bool) :
    (negativeAtom ε hε h).eval x =
      -(1 / (1 + ε * projection (negativeFirst h) (negativeSecond h) x)) := by
  rw [negativeAtom, FracAtom.ofPositiveAffineRatio_eval]
  simp only [affineValue, Fin.sum_univ_two, zero_mul, add_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, neg_div]
  congr 2
  simp only [projection]
  ring

/-- Six genuine original heads cancel identically. Their denominators have
strictly positive coefficients for every positive separation scale. -/
theorem six_genuine_heads_cancel (ε : ℝ) (hε : 0 < ε) (x : Fin 2 → Bool) :
    (∑ h, (positiveAtom ε hε h).eval x) +
      (∑ h, (negativeAtom ε hε h).eval x) = 0 := by
  simp only [positiveAtom_eval, negativeAtom_eval, Finset.sum_neg_distrib]
  rw [scalar_function_identity (fun t ↦ 1 / t) 1 ε x]
  ring

end HeadComplexity.BooleanProjectionMomentAliasing
