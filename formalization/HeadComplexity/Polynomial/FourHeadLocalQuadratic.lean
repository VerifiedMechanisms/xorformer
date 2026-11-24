import HeadComplexity.Polynomial.PositiveHalfRankCross
import HeadComplexity.Polynomial.FourHeadSelectorQuadratic
import HeadComplexity.Results.AffineFractionNormalForm

set_option linter.style.header false

/-!
# A finite local obstruction to four vanilla heads

Only 404 of the 131072 inputs are prescribed. The remaining labels can be chosen
arbitrarily. This provides an all-vanilla lower-bound target for exact pure-head
search without requiring a global symmetry of the target function.
-/

namespace HeadComplexity.FourHeadLocalPattern

noncomputable section

open Finset PureRoPEThreeHead FourHeadSelectorQuadratic
open scoped BigOperators

def join (t : Bool) (x : Fin 16 → Bool) : Fin 17 → Bool :=
  Fin.append x (fun _ : Fin 1 ↦ t)

def left : Fin 8 → Fin 16 := ![0, 2, 4, 6, 8, 10, 12, 14]
def right : Fin 8 → Fin 16 := ![1, 3, 5, 7, 9, 11, 13, 15]
def zeroInput : Fin 16 → Bool := fun _ ↦ false
def singleInput (i : Fin 16) : Fin 16 → Bool := Function.update zeroInput i true
def doubleInput (i j : Fin 16) : Fin 16 → Bool := Function.update (singleInput i) j true

def OrbitLabel (f : (Fin 17 → Bool) → Bool) (x : Fin 16 → Bool) (b : Bool) : Prop :=
  f (join true x) = b ∧ f (join false x) = !b ∧
    f (join true (flip x)) = b ∧ f (join false (flip x)) = !b

def LocalPattern (f : (Fin 17 → Bool) → Bool) : Prop :=
  OrbitLabel f zeroInput false ∧
    (∀ i, OrbitLabel f (singleInput i) true) ∧
    (∀ i j : Fin 8, i ≠ j → OrbitLabel f (doubleInput (left i) (right j)) false) ∧
    (∀ i j : Fin 8, i ≠ j → OrbitLabel f (doubleInput (right i) (right j)) false)

def productScore (q : ℝ) (A B : Fin 4 → Fin 16 → ℝ) (x : Fin 16 → Bool) : ℝ :=
  q + ∑ h, linear (A h) x * linear (B h) x

def crossCoefficient (A B : Fin 4 → Fin 16 → ℝ) (i j : Fin 8) : ℝ :=
  ∑ h, (A h (left i) * B h (right j) + B h (left i) * A h (right j))

theorem product_face_difference (q : ℝ) (A B : Fin 4 → Fin 16 → ℝ)
    (i j : Fin 16) (hij : i ≠ j) :
    productScore q A B zeroInput + productScore q A B (doubleInput i j) -
      productScore q A B (singleInput i) - productScore q A B (singleInput j) =
      4 * ∑ h, (A h i * B h j + B h i * A h j) := by
  simp only [productScore, singleInput, doubleInput, linear_update,
    Function.update_of_ne (Ne.symm hij), zeroInput, spin, Bool.false_eq_true,
    ite_false, ite_true, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 16000000 in
-- Normalize the eight quadratic slice identities in their affine coefficients.
theorem column_identity (q : ℝ) (A B : Fin 4 → Fin 16 → ℝ) (j : Fin 8) :
    4 * (∑ i, crossCoefficient A B i j) =
      5 * productScore q A B (singleInput (right j)) - 5 * productScore q A B zeroInput +
      ∑ k : Fin 8, if k = j then 0 else
        productScore q A B (singleInput (right k)) -
          productScore q A B (doubleInput (right j) (right k)) := by
  fin_cases j <;>
    simp [productScore, singleInput, doubleInput, crossCoefficient, left, right,
      linear, spin, zeroInput, Fin.sum_univ_succ] <;> ring

theorem quadratic_obstruction (q : ℝ) (A B : Fin 4 → Fin 16 → ℝ)
    (hB : ∀ h, (∀ i, 0 < B h i) ∨ (∀ i, B h i = 0))
    (hz : productScore q A B zeroInput < 0)
    (hs : ∀ i, 0 < productScore q A B (singleInput i))
    (hc : ∀ i j : Fin 8, i ≠ j → productScore q A B (doubleInput (left i) (right j)) < 0)
    (hp : ∀ i j : Fin 8, i ≠ j → productScore q A B (doubleInput (right i) (right j)) < 0) :
    False := by
  apply PositiveHalfRankCross.obstruction
    (fun h i ↦ A h (left i)) (fun h i ↦ B h (left i))
    (fun h j ↦ A h (right j)) (fun h j ↦ B h (right j))
  · intro h
    rcases hB h with h | h
    · exact Or.inl (fun i ↦ h _)
    · exact Or.inr (fun i ↦ h _)
  · intro h
    rcases hB h with h | h
    · exact Or.inl (fun i ↦ h _)
    · exact Or.inr (fun i ↦ h _)
  · intro i j hij
    have hidx : left i ≠ right j := by fin_cases i <;> fin_cases j <;> decide
    have he := product_face_difference q A B (left i) (right j) hidx
    have h1 := hs (left i)
    have h2 := hs (right j)
    have h3 := hc i j hij
    linarith
  · intro j
    change 0 < ∑ i, crossCoefficient A B i j
    have he := column_identity q A B j
    have hsum : 0 ≤ ∑ k : Fin 8, if k = j then 0 else
        productScore q A B (singleInput (right k)) -
          productScore q A B (doubleInput (right j) (right k)) := by
      apply Finset.sum_nonneg
      intro k _
      split_ifs with h
      · exact le_refl 0
      · linarith [hs (right k), hp j k (Ne.symm h)]
    linarith [hs (right j)]

end

end HeadComplexity.FourHeadLocalPattern
