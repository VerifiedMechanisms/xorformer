import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.style.header false

namespace HeadComplexity.ThreeHeadCrossGroupCertificate

/-- Three strictly positive denominator slope rows. -/
def denominator : Fin 3 → Fin 6 → ℚ :=
  ![![2, 2, 1, 3, 2, 2], ![2, 2, 2, 2, 1, 3], ![1, 3, 3, 3, 1, 1]]

/-- Arbitrary numerator slope rows for the squarefree coefficient certificate. -/
def numerator : Fin 3 → Fin 6 → ℚ :=
  ![![-20/3, -116/15, -4, -56/5, -20/3, -20/3],
    ![-76/21, -4/3, -4/3, -4/3, -44/21, 0],
    ![45/7, 203/15, 40/3, 68/5, 36/7, 0]]

/-- The coefficient of three distinct variables in the raw cleared cubic. -/
def coefficient (i j k : Fin 6) : ℚ :=
  numerator 0 i * (denominator 1 j * denominator 2 k + denominator 1 k * denominator 2 j) +
  numerator 0 j * (denominator 1 i * denominator 2 k + denominator 1 k * denominator 2 i) +
  numerator 0 k * (denominator 1 i * denominator 2 j + denominator 1 j * denominator 2 i) +
  numerator 1 i * (denominator 0 j * denominator 2 k + denominator 0 k * denominator 2 j) +
  numerator 1 j * (denominator 0 i * denominator 2 k + denominator 0 k * denominator 2 i) +
  numerator 1 k * (denominator 0 i * denominator 2 j + denominator 0 j * denominator 2 i) +
  numerator 2 i * (denominator 0 j * denominator 1 k + denominator 0 k * denominator 1 j) +
  numerator 2 j * (denominator 0 i * denominator 1 k + denominator 0 k * denominator 1 i) +
  numerator 2 k * (denominator 0 i * denominator 1 j + denominator 0 j * denominator 1 i)

/-- The twenty increasing triples of coordinates. -/
def triples : Fin 20 → Fin 6 × Fin 6 × Fin 6 :=
  ![(0,1,2), (0,1,3), (0,1,4), (0,1,5), (0,2,3),
    (0,2,4), (0,2,5), (0,3,4), (0,3,5), (0,4,5),
    (1,2,3), (1,2,4), (1,2,5), (1,3,4), (1,3,5),
    (1,4,5), (2,3,4), (2,3,5), (2,4,5), (3,4,5)]

/-- Coefficients of `(x₁-x₀)(x₃-x₂)(x₅-x₄)` on the increasing triples. -/
def target : Fin 20 → ℚ :=
  ![0,0,0,0,0,-1,1,1,-1,0,0,1,-1,-1,1,0,0,0,0,0]

theorem denominator_positive : ∀ h i, 0 < denominator h i := by
  decide +kernel

/-- Exact projection equality, not an equality of raw cubic polynomials and
not a Boolean head-count lower bound. -/
theorem squarefree_coefficients : ∀ r, let t := triples r
    coefficient t.1 t.2.1 t.2.2 = target r := by
  decide +kernel

end HeadComplexity.ThreeHeadCrossGroupCertificate
