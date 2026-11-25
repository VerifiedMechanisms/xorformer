import HeadComplexity.Polynomial.VanillaGeneralCentered
import HeadComplexity.Polynomial.RoPEGeneralDerivative

set_option linter.style.header false

/-!
# Block-supported derivatives of the actual vanilla affine factors

These identities instantiate the derivative hypotheses in the general
factor-rank argument directly from the centered vanilla parameters.
-/

noncomputable section

namespace HeadComplexity.VanillaBlockDerivatives

open MvPolynomial RoPECrossBlockCoefficients RoPEGeneralDerivative
open scoped BigOperators

theorem directional_affine {σ : Type*} [Fintype σ]
    (v : σ → ℝ) (a : ℝ) (A : σ → ℝ) :
    directional v (affine a A) = C (∑ i, A i * v i) := by
  simp only [affine, map_add, map_sum, directional_C, Derivation.leibniz,
    directional_X, smul_eq_mul, mul_zero, add_zero, zero_add, ← map_mul]

def blockDirection {β ι : Type*} [DecidableEq β] (b : β) (v : ι → ℝ) :
    β × ι → ℝ := fun p ↦ if p.1 = b then v p.2 else 0

def blockDirectionLinear {β ι : Type*} [DecidableEq β] (b : β) :
    (ι → ℝ) →ₗ[ℝ] (β × ι → ℝ) where
  toFun := blockDirection b
  map_add' v w := by funext p; simp [blockDirection]; split_ifs <;> simp
  map_smul' c v := by funext p; simp [blockDirection]

theorem directional_block_affine {β ι : Type*} [Fintype β] [Fintype ι]
    [DecidableEq β] (b : β) (v : ι → ℝ) (a : ℝ) (A : β × ι → ℝ) :
    directional (blockDirection b v) (affine a A) = C (∑ i, A (b, i) * v i) := by
  rw [directional_affine]
  congr 1
  simp only [Fintype.sum_prod_type, blockDirection]
  simp_rw [mul_ite, mul_zero]
  simp

variable {H : ℕ} {β ι : Type*} [Fintype β] [Fintype ι] [DecidableEq β]

def denominatorRows (a : VanillaGeneralCentered.Data H (β × ι)) (b : β) :
    Matrix (Fin H) ι ℝ := fun h i ↦ a.denominatorSlope h (b, i)

def numeratorRows (a : VanillaGeneralCentered.Data H (β × ι)) (b : β) :
    Matrix (Fin H) ι ℝ := fun h i ↦ a.numeratorSlope h (b, i)

theorem denominator_derivative (a : VanillaGeneralCentered.Data H (β × ι))
    (b : β) (v : ι → ℝ) (h : Fin H) :
    directional (blockDirection b v)
      (affine (a.denominatorConstant h) (a.denominatorSlope h)) =
      C ((denominatorRows a b).mulVec v h) :=
  directional_block_affine b v _ _

theorem numerator_derivative (a : VanillaGeneralCentered.Data H (β × ι))
    (b : β) (v : ι → ℝ) (h : Fin H) :
    directional (blockDirection b v)
      (affine (a.numeratorConstant h) (a.numeratorSlope h)) =
      C ((numeratorRows a b).mulVec v h) :=
  directional_block_affine b v _ _

theorem denominator_derivative_of_kernel
    (a : VanillaGeneralCentered.Data H (β × ι)) (b : β) (v : ι → ℝ)
    (hv : (denominatorRows a b).mulVec v = 0) (h : Fin H) :
    directional (blockDirection b v)
      (affine (a.denominatorConstant h) (a.denominatorSlope h)) = 0 := by
  rw [denominator_derivative, hv]
  simp

end HeadComplexity.VanillaBlockDerivatives
