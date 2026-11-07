module

public import HeadComplexity.LinearAlgebra.AffineSpace.Coordinates
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Affine maps as multivariate polynomials

Scalar-valued affine maps on a finite power evaluate as multivariate polynomials of degree at
most one, and every polynomial of degree at most one arises this way.
-/

@[expose] public section

variable {R ι : Type*} [CommRing R] [Fintype ι]

namespace AffineMap

open MvPolynomial

variable [DecidableEq ι]

/-- The multivariate polynomial with the same constant and linear coefficients as the map. -/
noncomputable def toMvPolynomial (f : (ι → R) →ᵃ[R] R) : MvPolynomial ι R :=
  C (f 0) + ∑ i, C (f.coeff i) * X i

/-- The polynomial constructed from an affine map agrees with that map at every point. -/
@[simp]
theorem eval_toMvPolynomial (f : (ι → R) →ᵃ[R] R) (x : ι → R) :
    eval x f.toMvPolynomial = f x := by
  rw [f.apply_eq_add_dotProduct x]
  simp [toMvPolynomial, dotProduct]

/-- The polynomial of an affine map has total degree at most one. -/
theorem totalDegree_toMvPolynomial_le_one (f : (ι → R) →ᵃ[R] R) :
    f.toMvPolynomial.totalDegree ≤ 1 := by
  nontriviality R using Subsingleton.eq_zero f.toMvPolynomial
  refine (totalDegree_add _ _).trans <| max_le (by simp) <| totalDegree_finsetSum_le ?_
  exact fun i _ ↦ (totalDegree_mul _ _).trans (by simp)

end AffineMap

namespace MvPolynomial

/-- A polynomial of total degree at most one is the sum of its constant term and its linear
terms. -/
theorem eq_C_add_sum_C_mul_X_of_totalDegree_le_one (p : MvPolynomial ι R)
    (hp : p.totalDegree ≤ 1) :
    p = C (p.coeff 0) + ∑ i, C (p.coeff (Finsupp.single i 1)) * X i := by
  classical
  ext d
  by_cases h0 : d = 0
  · subst d
    simp [coeff_sum, coeff_C_mul, coeff_X]
  by_cases h1 : ∃ i, d = Finsupp.single i 1
  · obtain ⟨i, rfl⟩ := h1
    simp [coeff_sum, coeff_C_mul, coeff_X, Finsupp.single_left_inj one_ne_zero, Ne.symm h0]
  suffices 1 < ∑ i ∈ d.support, d i by
    rw [coeff_eq_zero_of_totalDegree_lt (hp.trans_lt this)]
    simp [coeff_sum, coeff_C_mul, coeff_X, Ne.symm h0, fun i ↦ Ne.symm (fun hi ↦ h1 ⟨i, hi⟩)]
  by_contra! hle
  exact h1 ((Finsupp.sum_eq_one_iff d).mp (le_antisymm hle (Finset.sum_pos
    (fun i hi ↦ Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))
    (Finsupp.support_nonempty_iff.mpr h0))))

/-- Every polynomial of total degree at most one is the polynomial of an affine map. -/
theorem exists_affineMap_toMvPolynomial_eq_of_totalDegree_le_one [DecidableEq ι]
    (p : MvPolynomial ι R)
    (hp : p.totalDegree ≤ 1) :
    ∃ f : (ι → R) →ᵃ[R] R, f.toMvPolynomial = p := by
  refine ⟨(AffineMap.constCoeffEquiv R ι).symm
    (p.coeff 0, fun i ↦ p.coeff (Finsupp.single i 1)), ?_⟩
  simpa [AffineMap.toMvPolynomial] using (p.eq_C_add_sum_C_mul_X_of_totalDegree_le_one hp).symm

end MvPolynomial
