module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Coordinates of affine maps on finite powers

A scalar-valued affine map on a finite power is determined by its value at zero and the
coordinates of its linear part.
-/

@[expose] public section

namespace AffineMap

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The coefficients of the linear part in the coordinate basis. -/
def coeff (f : (ι → R) →ᵃ[R] R) : ι → R :=
  (dotProductEquiv R ι).symm f.linear

/-- The value at zero and the linear coefficients of an affine map. -/
def constCoeffEquiv (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι] :
    ((ι → R) →ᵃ[R] R) ≃ₗ[R] R × (ι → R) :=
  (toConstProdLinearMap R).trans
    ((LinearEquiv.refl R R).prodCongr (dotProductEquiv R ι).symm)

/-- The constant coordinate of an affine map is its value at zero. -/
@[simp]
theorem constCoeffEquiv_apply_fst (f : (ι → R) →ᵃ[R] R) :
    (constCoeffEquiv R ι f).1 = f 0 := rfl

/-- The second coordinate of an affine map is the coefficient vector of its linear part. -/
@[simp]
theorem constCoeffEquiv_apply_snd (f : (ι → R) →ᵃ[R] R) :
    (constCoeffEquiv R ι f).2 = f.coeff := rfl

/-- Evaluate an affine map by adding its constant to the dot product of its coefficients and
input. -/
theorem apply_eq_add_dotProduct (f : (ι → R) →ᵃ[R] R) (x : ι → R) :
    f x = f 0 + f.coeff ⬝ᵥ x := by
  have h := congrArg (fun g : Module.Dual R (ι → R) ↦ g x)
    ((dotProductEquiv R ι).apply_symm_apply f.linear)
  change f.coeff ⬝ᵥ x = f.linear x at h
  rw [h, add_comm]
  exact congrFun f.decomp x

/-- The affine map reconstructed from a constant and coefficients takes the given constant at
zero. -/
@[simp]
theorem constCoeffEquiv_symm_apply_zero (p : R × (ι → R)) :
    (constCoeffEquiv R ι).symm p 0 = p.1 := by
  simpa only [constCoeffEquiv_apply_fst] using
    congrArg Prod.fst ((constCoeffEquiv R ι).apply_symm_apply p)

/-- Reconstructing an affine map from a constant and coefficients recovers the given
coefficients. -/
@[simp]
theorem coeff_constCoeffEquiv_symm (p : R × (ι → R)) :
    ((constCoeffEquiv R ι).symm p).coeff = p.2 := by
  simpa only [constCoeffEquiv_apply_snd] using
    congrArg Prod.snd ((constCoeffEquiv R ι).apply_symm_apply p)

/-- The reconstructed affine map evaluates to the supplied constant plus the coefficient dot
product. -/
theorem constCoeffEquiv_symm_apply (p : R × (ι → R)) (x : ι → R) :
    (constCoeffEquiv R ι).symm p x = p.1 + p.2 ⬝ᵥ x := by
  rw [apply_eq_add_dotProduct, constCoeffEquiv_symm_apply_zero, coeff_constCoeffEquiv_symm]

end AffineMap
