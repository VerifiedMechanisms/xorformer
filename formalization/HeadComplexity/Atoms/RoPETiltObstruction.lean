import HeadComplexity.Atoms.RoPE

set_option linter.style.header false

/-!
# An oriented value tilt need not preserve a pure classifier

The original pure classifier is just the second input bit and is trivially
vanilla-computable with one head. The example rules out only the proposed
single-family tilt argument, not any head-complexity equality.
-/

namespace HeadComplexity.RoPETiltObstruction

open scoped BigOperators

noncomputable def exampleAtom : PureRoPEAtom 2 where
  a := ![100, 1]
  b := ![1, 200]
  γ := 1
  η := 0
  v₀ := 0
  v₁ := 1
  ha := by intro i; fin_cases i <;> norm_num
  hb := by intro i; fin_cases i <;> norm_num
  hγ := by norm_num

theorem original_classifier (x : Fin 2 → Bool) :
    (0 < exampleAtom.eval x - 1 / 2 ↔ x 1 = true) := by
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  rw [hx]
  cases x 0 <;> cases x 1 <;>
    norm_num [exampleAtom, PureRoPEAtom.eval, Fin.sum_univ_two]

/-- The sign-aligned difference quotient of the tilted partition function has
the simple affine numerator on the right. -/
theorem partition_difference (A B r : ℝ) (hr : r ≠ 1) :
    ((A + r ^ 2 * B) - r * (A + B)) / (r - 1) = r * B - A := by
  field_simp
  ring

/-- Uniform orientation of the tilted denominator forces one of two explicit
misclassifications of the difference-quotient classifier. -/
theorem tilt_misclassifies (r : ℝ) (hr : 0 < r)
    (horient : AffineFraction.UniformSign ![r ^ 2 - 100, 200 * r ^ 2 - 1]) :
    (0 < r - 2) ∨ (200 * r - 101 < 0) := by
  rcases horient with hp | hn | hz
  · have h := hp 0
    simp only [Matrix.cons_val_zero] at h
    left
    nlinarith
  · have h := hn 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
    right
    nlinarith [sq_nonneg (r - 1 / 10)]
  · have h0 := hz 0
    have h1 := hz 1
    simp only [Matrix.cons_val_zero] at h0
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
    exfalso
    nlinarith

/-- In fact no oriented tilt gives the correct labels at both mixed inputs. -/
theorem no_classifier_preserving_oriented_tilt (r : ℝ) (hr : 0 < r)
    (horient : AffineFraction.UniformSign ![r ^ 2 - 100, 200 * r ^ 2 - 1]) :
    ¬ (¬ (0 < r - 2) ∧ 0 < 200 * r - 101) := by
  intro h
  rcases tilt_misclassifies r hr horient with hp | hn
  · exact h.1 hp
  · exact (not_lt_of_gt hn) h.2

/-- The derivative classifier at the tilted endpoint fails as well. -/
theorem derivative_tilt_misclassifies (w : ℝ) (_hw : 0 < w)
    (horient : AffineFraction.UniformSign ![w - 100, 200 * w - 1]) :
    (0 < w - 2) ∨ (200 * w - 101 < 0) := by
  rcases horient with hp | hn | hz
  · have h := hp 0
    simp only [Matrix.cons_val_zero] at h
    left
    linarith
  · have h := hn 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
    right
    linarith
  · have h0 := hz 0
    have h1 := hz 1
    simp only [Matrix.cons_val_zero] at h0
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
    exfalso
    linarith

end HeadComplexity.RoPETiltObstruction
