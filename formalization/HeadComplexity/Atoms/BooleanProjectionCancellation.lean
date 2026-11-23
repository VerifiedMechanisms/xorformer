import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.whitespace false

/-! Exact six-point switching identities. The general vanishing ideal and
moment-curve construction are proved in the accompanying written note. -/
namespace HeadComplexity.BooleanProjectionCancellation

def moment (j : ℕ) (x y : ℝ) : ℝ :=
  (2*x+y)^j-(x+2*y)^j-(2*x)^j+(2*y)^j+x^j-y^j

theorem moment_zero (x y : ℝ) : moment 0 x y = 0 := by
  simp [moment]

theorem moment_one (x y : ℝ) : moment 1 x y = 0 := by
  unfold moment
  ring

theorem moment_two (x y : ℝ) : moment 2 x y = 0 := by
  unfold moment
  ring

theorem moment_three (x y : ℝ) : moment 3 x y = 6*x*y*(x-y) := by
  unfold moment
  ring

theorem switch_expansion (z w : ℝ) :
    (z-1)*(w-1)*(z-w) = z^2*w-z*w^2-z^2+w^2+z-w := by
  ring

theorem generator_boolean_line (t x y : ℝ)
    (hx : x=0 ∨ x=1) (hy : y=0 ∨ y=1) :
    (t*x)*(t*y)*(t*x-t*y) = 0 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

noncomputable def score (D ε x y : ℝ) : ℝ :=
  1/(D+ε*(2*x+y))-1/(D+ε*(x+2*y))-1/(D+2*ε*x)+
    1/(D+2*ε*y)+1/(D+ε*x)-1/(D+ε*y)

theorem score_boolean (D ε x y : ℝ)
    (hx : x=0 ∨ x=1) (hy : y=0 ∨ y=1) : score D ε x y = 0 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp [score] <;> ring

theorem score_nonformal : score 1 1 (1/2) (1/3) = -89/5460 := by
  norm_num [score]

theorem coherent_perturbation_positive {I : Type*}
    (b v : I → ℝ) (ε : ℝ) (hb : ∀ i, 0 < b i)
    (hv : ∀ i, 0 ≤ v i) (hε : 0 ≤ ε) : ∀ i, 0 < b i+ε*v i := by
  intro i
  exact add_pos_of_pos_of_nonneg (hb i) (mul_nonneg hε (hv i))

end HeadComplexity.BooleanProjectionCancellation
