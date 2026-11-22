import HeadComplexity.Atoms.PolynomialPositiveGrid
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-! Polynomial clearing transfers a single nonsingular reciprocal-cube witness
to an explicitly finite grid inside a positive parameter interval. -/
namespace HeadComplexity.PositiveRationalTransfer

open Polynomial Finset
open scoped BigOperators

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

noncomputable def rationalMatrix (c : I → V) (E : I → I → ℝ)
    (B : V → I → ℝ[X]) (t : ℝ) : Matrix I I ℝ :=
  fun x y ↦ E x y / ((B (c y) x).eval t) ^ 3

noncomputable def clearedMatrix (c : I → V) (E : I → I → ℝ)
    (B : V → I → ℝ[X]) : Matrix I I ℝ[X] :=
  fun x y ↦ C (E x y) * ∏ v ∈ Finset.univ.erase (c y), B v x ^ 3

noncomputable def rowProduct (B : V → I → ℝ[X]) (t : ℝ) (x : I) : ℝ :=
  ∏ v, ((B v x).eval t) ^ 3

omit [Fintype I] [DecidableEq I] in
theorem cleared_entry_eval (c : I → V) (E : I → I → ℝ)
    (B : V → I → ℝ[X]) (t : ℝ) (hB : ∀ v x, (B v x).eval t ≠ 0)
    (x y : I) :
    (clearedMatrix c E B x y).eval t =
      rowProduct B t x * rationalMatrix c E B t x y := by
  simp only [clearedMatrix, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_pow, rowProduct, rationalMatrix]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun v ↦ ((B v x).eval t) ^ 3) (Finset.mem_univ (c y))]
  field_simp [hB (c y) x]

theorem cleared_det_eval (c : I → V) (E : I → I → ℝ)
    (B : V → I → ℝ[X]) (t : ℝ) (hB : ∀ v x, (B v x).eval t ≠ 0) :
    (clearedMatrix c E B).det.eval t =
      (∏ x, rowProduct B t x) * (rationalMatrix c E B t).det := by
  have hmap := (Polynomial.evalRingHom t).map_det (clearedMatrix c E B)
  change (clearedMatrix c E B).det.eval t = _ at hmap
  rw [hmap]
  have hmatrix : (Polynomial.evalRingHom t).mapMatrix (clearedMatrix c E B) =
      Matrix.of (fun x y ↦ rowProduct B t x * rationalMatrix c E B t x y) := by
    ext x y
    exact cleared_entry_eval c E B t hB x y
  rw [hmatrix, Matrix.det_mul_column]

theorem cleared_det_nonzero (c : I → V) (E : I → I → ℝ)
    (B : V → I → ℝ[X]) (w : ℝ) (hB : ∀ v x, (B v x).eval w ≠ 0)
    (hw : (rationalMatrix c E B w).det ≠ 0) :
    (clearedMatrix c E B).det ≠ 0 := by
  intro hzero
  have heval := cleared_det_eval c E B w hB
  rw [hzero, Polynomial.eval_zero] at heval
  have hprod : (∏ x, rowProduct B w x) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro x _
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    exact pow_ne_zero _ (hB v x)
  exact (mul_ne_zero hprod hw) heval.symm

/-- A nonsingular witness outside the positive interval is enough: the
determinant polynomial is tested on a degree-plus-one grid inside it. -/
theorem exists_positive_nonsingular (c : I → V) (E : I → I → ℝ)
    (B : V → I → ℝ[X]) (w : ℝ) (hB : ∀ v x, (B v x).eval w ≠ 0)
    (hw : (rationalMatrix c E B w).det ≠ 0)
    (s : ℝ) (hs : 0 < s)
    (hpositive : ∀ t : ℝ, 0 < t → t * s < 1 → ∀ v x, 0 < (B v x).eval t) :
    ∃ j : Fin ((clearedMatrix c E B).det.natDegree + 1),
      let t := PolynomialPositiveGrid.grid (clearedMatrix c E B).det.natDegree s j
      0 < t ∧ t * s < 1 ∧ (∀ v x, 0 < (B v x).eval t) ∧
        (rationalMatrix c E B t).det ≠ 0 := by
  have hpoly := cleared_det_nonzero c E B w hB hw
  obtain ⟨j, hjpos, hjsmall, hjnonzero⟩ :=
    PolynomialPositiveGrid.exists_grid_nonzero (clearedMatrix c E B).det hpoly
      (clearedMatrix c E B).det.natDegree le_rfl s hs
  refine ⟨j, hjpos, hjsmall, hpositive _ hjpos hjsmall, ?_⟩
  rw [cleared_det_eval c E B _
    (fun v x ↦ (hpositive _ hjpos hjsmall v x).ne')] at hjnonzero
  exact (mul_ne_zero_iff.mp hjnonzero).2

end HeadComplexity.PositiveRationalTransfer
