import HeadComplexity.Polynomial.RoPEGroupSymmetrization
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.MvPolynomial.Funext

set_option linter.style.header false

/-! # Polynomial and topological equivalences from affine coordinates -/

namespace HeadComplexity.AffineCoordinateEquivalence

open scoped BigOperators
open MvPolynomial

variable {σ τ : Type*} [Fintype σ]

noncomputable def polynomial (L : (σ → ℝ) →ₗ[ℝ] (τ → ℝ))
    (c : τ → ℝ) (i : τ) : MvPolynomial σ ℝ := by
  classical
  exact C (c i) + ∑ j, C (L (fun k ↦ if j = k then 1 else 0) i) * X j

theorem eval_polynomial (L : (σ → ℝ) →ₗ[ℝ] (τ → ℝ))
    (c : τ → ℝ) (x : σ → ℝ) :
    (fun i ↦ eval x (polynomial L c i)) = L x + c := by
  classical
  funext i
  rw [LinearMap.pi_apply_eq_sum_univ L x]
  simp only [polynomial, map_add, map_sum, map_mul, eval_C, eval_X,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  simp_rw [mul_comm]
  ring

theorem polynomial_totalDegree (L : (σ → ℝ) →ₗ[ℝ] (τ → ℝ))
    (c : τ → ℝ) (i : τ) : (polynomial L c i).totalDegree ≤ 1 := by
  classical
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_mul _ _).trans (by simp)

variable [Fintype τ]

noncomputable def substitutionEquiv
    (e : (σ → ℝ) ≃ₗ[ℝ] (τ → ℝ)) (c : τ → ℝ) :
    MvPolynomial τ ℝ ≃ₐ[ℝ] MvPolynomial σ ℝ where
  toFun := aeval (polynomial e.toLinearMap c)
  invFun := aeval (polynomial e.symm.toLinearMap (-(e.symm c)))
  left_inv P := by
    apply MvPolynomial.funext
    intro y
    rw [RoPEGroupSymmetrization.eval_affine_substitution, eval_polynomial,
      RoPEGroupSymmetrization.eval_affine_substitution, eval_polynomial]
    simp
  right_inv P := by
    apply MvPolynomial.funext
    intro x
    rw [RoPEGroupSymmetrization.eval_affine_substitution, eval_polynomial,
      RoPEGroupSymmetrization.eval_affine_substitution, eval_polynomial]
    simp
  map_mul' := (aeval (polynomial e.toLinearMap c)).map_mul
  map_add' := (aeval (polynomial e.toLinearMap c)).map_add
  commutes' := (aeval (polynomial e.toLinearMap c)).commutes

theorem eval_substitutionEquiv
    (e : (σ → ℝ) ≃ₗ[ℝ] (τ → ℝ)) (c : τ → ℝ)
    (P : MvPolynomial τ ℝ) (x : σ → ℝ) :
    eval x (substitutionEquiv e c P) = eval (e x + c) P := by
  change eval x (aeval _ P) = _
  rw [RoPEGroupSymmetrization.eval_affine_substitution, eval_polynomial]
  rfl

theorem eval_substitutionEquiv_symm
    (e : (σ → ℝ) ≃ₗ[ℝ] (τ → ℝ)) (c : τ → ℝ)
    (P : MvPolynomial σ ℝ) (y : τ → ℝ) :
    eval y ((substitutionEquiv e c).symm P) = eval (e.symm (y - c)) P := by
  change eval y (aeval _ P) = _
  rw [RoPEGroupSymmetrization.eval_affine_substitution, eval_polynomial]
  change eval (e.symm y - e.symm c) P = eval (e.symm (y - c)) P
  rw [map_sub]

theorem substitutionEquiv_totalDegree
    (e : (σ → ℝ) ≃ₗ[ℝ] (τ → ℝ)) (c : τ → ℝ) (P : MvPolynomial τ ℝ) :
    (substitutionEquiv e c P).totalDegree = P.totalDegree := by
  have hf : (substitutionEquiv e c P).totalDegree ≤ P.totalDegree :=
    RoPEGroupSymmetrization.affine_substitution_degree P _ (polynomial_totalDegree _ _)
  have hb := RoPEGroupSymmetrization.affine_substitution_degree
    (substitutionEquiv e c P) (polynomial e.symm.toLinearMap (-(e.symm c)))
    (polynomial_totalDegree _ _)
  change ((substitutionEquiv e c).symm (substitutionEquiv e c P)).totalDegree ≤ _ at hb
  rw [AlgEquiv.symm_apply_apply] at hb
  exact Nat.le_antisymm hf hb

noncomputable def coordinateHomeomorph
    (e : (σ → ℝ) ≃ₗ[ℝ] (τ → ℝ)) (c : τ → ℝ) :
    (σ → ℝ) ≃ₜ (τ → ℝ) where
  toFun x := e x + c
  invFun y := e.symm (y - c)
  left_inv x := by simp
  right_inv y := by simp
  continuous_toFun := e.toContinuousLinearEquiv.continuous.add continuous_const
  continuous_invFun := e.symm.toContinuousLinearEquiv.continuous.comp
    (continuous_id.sub continuous_const)

theorem coordinateHomeomorph_apply
    (e : (σ → ℝ) ≃ₗ[ℝ] (τ → ℝ)) (c : τ → ℝ) (x : σ → ℝ) :
    coordinateHomeomorph e c x = e x + c := rfl

end HeadComplexity.AffineCoordinateEquivalence
