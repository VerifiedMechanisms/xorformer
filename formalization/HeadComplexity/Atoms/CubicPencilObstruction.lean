import HeadComplexity.Atoms.TwoHeadPencil
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option linter.style.header false

/-!
# A quadratic obstruction to one exact cubic denominator-pencil induction

This module concerns exact polynomial identities on real coordinates. It does
not assert a Boolean head-count separation. In the endpoint-shifted three-head
cubic `z * (c*b + d*a) + w*a*b`, imposing `w = -t*z` leaves the quadratic
`c*b + d*a - t*a*b`. Its polarization matrix is nonsingular for every `t`, so it
cannot factor into two affine forms. This rules out the proposed exact-factor
step when two new denominators are constrained to the first head's pencil.
-/

namespace HeadComplexity.CubicPencilObstruction

open scoped BigOperators

noncomputable def quad (t : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  x 2 * x 1 + x 3 * x 0 - t * x 0 * x 1

noncomputable def affine (c : ℝ) (u x : Fin 4 → ℝ) : ℝ :=
  c + ∑ i, u i * x i

noncomputable def polarization (F : (Fin 4 → ℝ) → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => F (fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0)) -
    F (fun k => if k = i then 1 else 0) - F (fun k => if k = j then 1 else 0) + F 0

private theorem affine_basis (c : ℝ) (u : Fin 4 → ℝ) (i : Fin 4) :
    affine c u (fun k => if k = i then 1 else 0) = c + u i := by
  simp [affine, mul_ite]

private theorem affine_basis_add (c : ℝ) (u : Fin 4 → ℝ) (i j : Fin 4) :
    affine c u (fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0)) =
      c + u i + u j := by
  simp [affine, mul_add, Finset.sum_add_distrib, mul_ite, add_assoc]

private theorem affine_zero (c : ℝ) (u : Fin 4 → ℝ) : affine c u 0 = c := by
  simp [affine]

/-- A product of two affine forms has polarization rank at most two. The
four-dimensional determinant identity is checked directly. -/
theorem affineProduct_polarization_det (c d : ℝ) (u v : Fin 4 → ℝ) :
    Matrix.det (polarization (fun x => affine c u x * affine d v x)) = 0 := by
  have hp : polarization (fun x => affine c u x * affine d v x) =
      fun i j => u i * v j + v i * u j := by
    ext i j
    simp only [polarization, affine_basis_add, affine_basis, affine_zero]
    ring
  rw [hp, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply]
  dsimp
  norm_num
  ring

/-- The quadratic left after fixing a denominator in the first head's pencil
has nonsingular polarization, independently of the pencil parameter. -/
theorem quad_polarization_det (t : ℝ) : Matrix.det (polarization (quad t)) = 1 := by
  have hp : polarization (quad t) =
      !![0, -t, 0, 1; -t, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [polarization, quad, Fin.ext_iff]
  rw [hp, Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply]
  dsimp
  norm_num [Fin.succAbove, Fin.ext_iff]
  exact Or.inr rfl

/-- No two affine forms multiply to this quadratic on all real inputs. This
is not a statement about preserving only signs on a Boolean cube. -/
theorem quad_not_affine_product (t c d : ℝ) (u v : Fin 4 → ℝ) :
    ¬ (∀ x, quad t x = affine c u x * affine d v x) := by
  intro h
  have hf : quad t = fun x => affine c u x * affine d v x := funext h
  have ha := affineProduct_polarization_det c d u v
  have hq := quad_polarization_det t
  rw [hf] at hq
  linarith

noncomputable def affineSix (c : ℝ) (u x : Fin 6 → ℝ) : ℝ :=
  c + ∑ i, u i * x i

noncomputable def cubic (x : Fin 6 → ℝ) : ℝ :=
  x 4 * (x 2 * x 1 + x 3 * x 0) + x 5 * x 0 * x 1

private noncomputable def slice (t : ℝ) (x : Fin 4 → ℝ) : Fin 6 → ℝ :=
  ![x 0, x 1, x 2, x 3, 1, -t]

private noncomputable def slopeFour (u : Fin 6 → ℝ) : Fin 4 → ℝ :=
  ![u 0, u 1, u 2, u 3]

private theorem affineSix_slice (c t : ℝ) (u : Fin 6 → ℝ) (x : Fin 4 → ℝ) :
    affineSix c u (slice t x) = affine (c + u 4 - t * u 5) (slopeFour u) x := by
  simp only [affineSix, affine, Fin.sum_univ_succ, slice, slopeFour]
  dsimp
  ring

private theorem affine_mul (k c : ℝ) (u x : Fin 4 → ℝ) :
    affine (k * c) (fun i => k * u i) x = k * affine c u x := by
  simp only [affine, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The full exact cubic identity fails whenever two proposed denominator
factors are `w + t*z` and `w + s*z`. All three new numerators and the remaining
denominator may be arbitrary affine forms in all six real coordinates. This
is an exact-polynomial route obstruction, not a Boolean sign lower bound. -/
theorem cubic_not_two_denominators_in_pencil (t s c₁ c₂ c₃ d : ℝ)
    (u₁ u₂ u₃ v : Fin 6 → ℝ) :
    ¬ (∀ x : Fin 6 → ℝ, cubic x =
      affineSix c₁ u₁ x * (x 5 + s * x 4) * affineSix d v x +
      affineSix c₂ u₂ x * (x 5 + t * x 4) * affineSix d v x +
      affineSix c₃ u₃ x * (x 5 + t * x 4) * (x 5 + s * x 4)) := by
  intro h
  apply quad_not_affine_product t (c₁ + u₁ 4 - t * u₁ 5)
    ((s - t) * (d + v 4 - t * v 5)) (slopeFour u₁)
    (fun i => (s - t) * slopeFour v i)
  intro x
  rw [affine_mul]
  have hs := h (slice t x)
  simp only [affineSix_slice] at hs
  simp only [cubic, slice] at hs
  dsimp at hs
  have he : -t + t * 1 = 0 := by ring
  rw [he] at hs
  simp only [mul_zero, zero_mul, add_zero, one_mul] at hs
  unfold quad
  nlinarith [hs]

end HeadComplexity.CubicPencilObstruction
