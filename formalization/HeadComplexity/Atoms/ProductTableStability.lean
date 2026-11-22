import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

set_option linter.style.header false
set_option maxHeartbeats 2000000

/-! Exact obstruction to stability of the generating polynomial of the Boolean
value table of a product of coefficient-positive affine denominators. -/
namespace HeadComplexity.ProductTableStability
open scoped BigOperators
noncomputable section

def slopes : Fin 4 → Fin 4 → ℤ := ![
  ![10, 10, 1, 1], ![1, 1, 10, 10],
  ![10, 1, 10, 1], ![1, 10, 1, 10]]

def bit (v : ℕ) (i : Fin 4) : ℤ := (v / 2^i.val % 2 : ℕ)

def denominator (h : Fin 4) (v : Fin 16) : ℤ :=
  1 + ∑ i : Fin 4, slopes h i * bit v.val i

def tableValue (v : Fin 16) : ℤ := ∏ h : Fin 4, denominator h v

def coefficientData : Fin 16 → ℤ :=
  ![1, 484, 484, 9072, 484, 9072, 20736, 81796,
    484, 20736, 9072, 81796, 9072, 81796, 81796, 279841]

theorem slopes_positive : ∀ h i, 0 < slopes h i := by decide +kernel
theorem denominators_positive : ∀ h v, 0 < denominator h v := by decide +kernel
theorem tableValue_eq_data : ∀ v, tableValue v = coefficientData v := by decide +kernel

def generating (z : Fin 4 → ℂ) : ℂ :=
  ∑ v : Fin 16, (tableValue v : ℂ) *
    ∏ i : Fin 4, if bit v.val i = 1 then z i else 1

def explicitPolynomial (z : Fin 4 → ℂ) : ℂ :=
  1 + 484 * (z 0 + z 1 + z 2 + z 3) +
    9072 * (z 0 * z 1 + z 0 * z 2 + z 1 * z 3 + z 2 * z 3) +
    20736 * (z 0 * z 3 + z 1 * z 2) +
    81796 * (z 0 * z 1 * z 2 + z 0 * z 1 * z 3 +
      z 0 * z 2 * z 3 + z 1 * z 2 * z 3) +
    279841 * z 0 * z 1 * z 2 * z 3

theorem generating_eq_explicit (z : Fin 4 → ℂ) : generating z = explicitPolynomial z := by
  simp only [generating, tableValue_eq_data]
  norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ, coefficientData, bit, explicitPolynomial]
  ring

def sliceA (t : ℂ) : ℂ := 1 + 968 * t + 20736 * t^2
def sliceB (t : ℂ) : ℂ := 484 + 18144 * t + 81796 * t^2
def sliceD (t : ℂ) : ℂ := 20736 + 163592 * t + 279841 * t^2

theorem generating_slice (z t w : ℂ) :
    generating ![z, t, t, w] = sliceA t + sliceB t * (z + w) + sliceD t * z * w := by
  rw [generating_eq_explicit]
  norm_num [explicitPolynomial, sliceA, sliceB, sliceD]
  ring

def middle : ℂ := 1 / 10 + (1 / 10000) * Complex.I
def lastPoint : ℂ :=
  -1252875804328031226236292 / 16013505298103043438130897 +
    (23924656286642536357360 / 16013505298103043438130897) * Complex.I
def witness : Fin 4 → ℂ := ![Complex.I, middle, middle, lastPoint]

theorem witness_im_positive : ∀ i, 0 < (witness i).im := by
  intro i
  fin_cases i <;> norm_num [witness, middle, lastPoint]

theorem generating_witness_zero : generating witness = 0 := by
  rw [show witness = ![Complex.I, middle, middle, lastPoint] from rfl, generating_slice]
  apply Complex.ext <;>
    norm_num [sliceA, sliceB, sliceD, middle, lastPoint, pow_two,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]

/-- A completely explicit failure of upper-half-plane nonvanishing. -/
theorem exists_upper_half_plane_zero :
    ∃ z : Fin 4 → ℂ, (∀ i, 0 < (z i).im) ∧ generating z = 0 :=
  ⟨witness, witness_im_positive, generating_witness_zero⟩

def weight (v : Fin 16) : ℚ :=
  (tableValue v : ℚ) * (1 / 10 : ℚ) ^ (∑ i : Fin 4, (v.val / 2^i.val % 2))
def partition : ℚ := ∑ v : Fin 16, weight v
def moment (i : Fin 4) : ℚ := ∑ v : Fin 16, weight v * (bit v.val i : ℚ)
def pairMoment (i j : Fin 4) : ℚ :=
  ∑ v : Fin 16, weight v * (bit v.val i : ℚ) * (bit v.val j : ℚ)

theorem partition_value : partition = 13273681 / 10000 := by decide +kernel

theorem covariance_numerator_value :
    pairMoment 0 3 * partition - moment 0 * moment 3 = 1231117189 / 50000 := by
  decide +kernel

theorem covariance_positive :
    0 < pairMoment 0 3 / partition - (moment 0 / partition) * (moment 3 / partition) := by
  have hp : 0 < partition := by rw [partition_value]; norm_num
  have h := covariance_numerator_value
  have heq : pairMoment 0 3 / partition - (moment 0 / partition) * (moment 3 / partition) =
      (pairMoment 0 3 * partition - moment 0 * moment 3) / partition^2 := by
    field_simp
  rw [heq, h]
  positivity

end
end HeadComplexity.ProductTableStability
