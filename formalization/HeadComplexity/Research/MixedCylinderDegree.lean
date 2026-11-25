import HeadComplexity.Research.LinearCylinderCompiler
import HeadComplexity.Polynomial.ParityThresholdDegree

set_option linter.style.header false

/-!
A mixed affine-cylinder block has degree at most its literal count plus one.
Consequently a strict parity score needs a block fixing all but at most one
coordinate. Applied after coordinate restriction, this is the algebraic
ingredient of the mixed-cylinder face-count obstruction.
-/

noncomputable section

namespace HeadComplexity.MixedCylinderDegree

open Finset MvPolynomial
open scoped BigOperators

variable {n : ℕ}

def cylinderPolynomial (Cyl : CubeCylinder n) : MvPolynomial (Fin n) ℝ :=
  (∏ i ∈ Cyl.positive, X i) * ∏ i ∈ Cyl.negative, (1 - X i)

def affinePolynomial (a : ℝ) (u : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  C a + ∑ i, C (u i) * X i

theorem eval_cylinderPolynomial (Cyl : CubeCylinder n) (x : Fin n → Bool) :
    eval (cubePoint x) (cylinderPolynomial Cyl) = Cyl.eval x := by
  simp [cylinderPolynomial, CubeCylinder.eval, cubePoint]

theorem eval_affinePolynomial (a : ℝ) (u : Fin n → ℝ) (x : Fin n → Bool) :
    eval (cubePoint x) (affinePolynomial a u) = affineValue a u x := by
  simp [affinePolynomial, affineValue, cubePoint]

theorem cylinderPolynomial_degree (Cyl : CubeCylinder n) :
    (cylinderPolynomial Cyl).totalDegree ≤ Cyl.positive.card + Cyl.negative.card := by
  unfold cylinderPolynomial
  refine (totalDegree_mul _ _).trans (Nat.add_le_add ?_ ?_)
  · refine (totalDegree_finsetProd _ _).trans ?_
    simp
  · refine (totalDegree_finsetProd _ _).trans ?_
    calc
      _ ≤ ∑ _i ∈ Cyl.negative, 1 := sum_le_sum fun i _ ↦ by
        refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · simp
        · simp
      _ = _ := by simp

theorem affinePolynomial_degree (a : ℝ) (u : Fin n → ℝ) :
    (affinePolynomial a u).totalDegree ≤ 1 := by
  unfold affinePolynomial
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simp)

theorem block_degree (Cyl : CubeCylinder n) (a : ℝ) (u : Fin n → ℝ) :
    (cylinderPolynomial Cyl * affinePolynomial a u).totalDegree ≤
      Cyl.positive.card + Cyl.negative.card + 1 :=
  (totalDegree_mul _ _).trans
    (Nat.add_le_add (cylinderPolynomial_degree Cyl) (affinePolynomial_degree a u))

/-- This theorem permits arbitrary real coefficients and arbitrary cancellation
among the blocks. It is a statement about a sign representation, not equality
with a prescribed target score. -/
theorem thresholdDegLE_of_cylinder_score
    {J : Type*} [Fintype J] (Cyl : J → CubeCylinder n)
    (a : J → ℝ) (u : J → Fin n → ℝ) (bias : ℝ) (d : ℕ)
    (hdeg : ∀ j, (Cyl j).positive.card + (Cyl j).negative.card + 1 ≤ d)
    (f : (Fin n → Bool) → Bool)
    (hstrict : StrictSignRepresentsScore
      (fun x ↦ bias + ∑ j, (Cyl j).eval x * affineValue (a j) (u j) x) f) :
    ThresholdDegLE f d := by
  classical
  let P := C bias + ∑ j, cylinderPolynomial (Cyl j) * affinePolynomial (a j) (u j)
  refine ⟨P, ?_, ?_⟩
  · refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
    exact totalDegree_finsetSum_le fun j _ ↦ (block_degree (Cyl j) (a j) (u j)).trans
      (hdeg j)
  · intro x
    have heval : eval (cubePoint x) P =
        bias + ∑ j, (Cyl j).eval x * affineValue (a j) (u j) x := by
      simp [P, eval_cylinderPolynomial, eval_affinePolynomial]
    rw [heval]
    exact (hstrict x).1

theorem parity_degree_le_of_cylinder_score
    {J : Type*} [Fintype J] (Cyl : J → CubeCylinder n)
    (a : J → ℝ) (u : J → Fin n → ℝ) (bias : ℝ) (d : ℕ)
    (hdeg : ∀ j, (Cyl j).positive.card + (Cyl j).negative.card + 1 ≤ d)
    (hstrict : StrictSignRepresentsScore
      (fun x ↦ bias + ∑ j, (Cyl j).eval x * affineValue (a j) (u j) x) (PARITY n)) :
    n ≤ d := by
  have h := thresholdDegLE_of_cylinder_score Cyl a u bias d hdeg (PARITY n) hstrict
  rw [PARITY_eq_symmetricFn] at h
  have hh := signChanges_le_of_ThresholdDegLE h
  simpa only [signChanges_parity] using hh

theorem exists_large_cylinder_of_parity_score
    {J : Type*} [Fintype J] (Cyl : J → CubeCylinder n)
    (a : J → ℝ) (u : J → Fin n → ℝ) (bias : ℝ) (hn : 0 < n)
    (hstrict : StrictSignRepresentsScore
      (fun x ↦ bias + ∑ j, (Cyl j).eval x * affineValue (a j) (u j) x) (PARITY n)) :
    ∃ j, n ≤ (Cyl j).positive.card + (Cyl j).negative.card + 1 := by
  by_contra h
  push Not at h
  have hd : ∀ j, (Cyl j).positive.card + (Cyl j).negative.card + 1 ≤ n - 1 := by
    intro j
    exact Nat.le_sub_one_of_lt (h j)
  have hh := parity_degree_le_of_cylinder_score Cyl a u bias (n - 1) hd hstrict
  omega

end HeadComplexity.MixedCylinderDegree
