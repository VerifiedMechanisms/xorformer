import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Derivatives of multivariate polynomial evaluations
-/

namespace HeadComplexity.PolynomialRootCount

open MvPolynomial

variable {ι : Type*} [Fintype ι]

/-- The formal Jacobian of a polynomial, as a continuous linear functional. -/
noncomputable def evalDerivative (p : MvPolynomial ι ℝ) (x : ι → ℝ) :
    (ι → ℝ) →L[ℝ] ℝ := ∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj i

/-- Evaluation has the strict derivative given by the formal partial derivatives. -/
theorem hasStrictFDerivAt_eval (p : MvPolynomial ι ℝ) (x : ι → ℝ) :
    HasStrictFDerivAt (fun z ↦ eval z p) (evalDerivative p x) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simpa [evalDerivative] using hasStrictFDerivAt_const (𝕜 := ℝ) a x
  | add p q hp hq =>
    convert hp.add hq using 1
    · simp only [map_add]; rfl
    · simp [evalDerivative, map_add, add_smul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    have h := hp.mul (hasStrictFDerivAt_apply (𝕜 := ℝ) j x)
    convert h using 1
    · simp only [map_mul, eval_X]; rfl
    · ext y
      simp [evalDerivative, pderiv_X, Pi.single_apply, apply_ite, ite_mul,
        add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- Independent rows of a square matrix give an invertible continuous linear map. -/
theorem matrix_continuous_equiv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : LinearIndependent ℝ A) :
    ∃ e : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ), ∀ x, e x = A.mulVec x := by
  have hu : IsUnit A := Matrix.linearIndependent_row_iff_isUnit.mp hA
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hu
  have hsurj := LinearMap.surjective_of_injective (f := A.mulVecLin) hinj
  exact ⟨(LinearEquiv.ofBijective A.mulVecLin ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
    fun _ ↦ rfl⟩

omit [Fintype ι] in
/-- Formal partial differentiation lowers a positive total-degree bound. -/
theorem totalDegree_pderiv_le {d : ℕ} (p : MvPolynomial ι ℝ)
    (hp : p.totalDegree ≤ d + 1) (i : ι) : (pderiv i p).totalDegree ≤ d := by
  classical
  rw [totalDegree]
  apply Finset.sup_le
  intro m hm
  have hc := mem_support_iff.mp hm
  rw [coeff_pderiv] at hc
  have hm' : m + Finsupp.single i 1 ∈ p.support :=
    mem_support_iff.mpr (mul_ne_zero_iff.mp hc).1
  have hb := (le_totalDegree hm').trans hp
  change Finsupp.degree (m + Finsupp.single i 1) ≤ d + 1 at hb
  rw [map_add, Finsupp.degree_single] at hb
  change Finsupp.degree m ≤ d
  omega

end HeadComplexity.PolynomialRootCount
