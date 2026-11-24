import HeadComplexity.Research.WeightedNormalizedCounting
import Mathlib.Algebra.MvPolynomial.PDeriv

set_option linter.style.header false

/-!
An ordinary first-jet moment relation forces a Cayley--Bacharach property of
its reduced support, losing at most a factor of two in the order. In particular
this does not assume or assert that Boolean projection moment cancellation is
ordinary polynomial moment cancellation.
-/

noncomputable section
namespace HeadComplexity.FirstJetCayleyBacharach
open Finset MvPolynomial
open scoped BigOperators

variable {n H : ℕ}

/-- Evaluation plus a directional first derivative at a pole. -/
def jet (p v : Fin n → ℝ) (c : ℝ) (P : MvPolynomial (Fin n) ℝ) : ℝ :=
  c * eval p P + ∑ i, v i * eval p (pderiv i P)

/-- Squaring a vanishing polynomial kills every first jet at that point. -/
theorem jet_square_zero (p v : Fin n → ℝ) (c : ℝ)
    (P : MvPolynomial (Fin n) ℝ) (hP : eval p P = 0) :
    jet p v c (P ^ 2) = 0 := by
  simp [jet, hP]

/-- The same vanishing holds after multiplication by any further polynomial. -/
theorem jet_square_mul_zero (p v : Fin n → ℝ) (c : ℝ)
    (P Q : MvPolynomial (Fin n) ℝ) (hP : eval p P = 0) :
    jet p v c (P ^ 2 * Q) = 0 := by
  simp [jet, hP]

/-- A coordinate vanishing at the selected point isolates one derivative. -/
theorem jet_square_coordinate (p v : Fin n → ℝ) (c : ℝ)
    (P : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    jet p v c (P ^ 2 * (X i - C (p i))) = (eval p P) ^ 2 * v i := by
  classical
  simp only [jet, map_mul, map_pow, map_sub, eval_X, eval_C, sub_self,
    mul_zero, pderiv_mul, pderiv_pow, map_add, map_natCast, map_sub,
    pderiv_C, sub_zero, zero_add]
  simp [pderiv_X, Pi.single_apply, mul_comm]

/-- When the direction is zero, the jet is a scalar point evaluation. -/
theorem jet_direction_zero (p : Fin n → ℝ) (c : ℝ)
    (P : MvPolynomial (Fin n) ℝ) :
    jet p 0 c P = c * eval p P := by
  simp [jet]

/-- The reduced affine Cayley--Bacharach property at degree `s`,
including distinctness of the indexed support. -/
def ReducedCB (p : Fin H → Fin n → ℝ) (s : ℕ) : Prop :=
  Function.Injective p ∧ ∀ h (P : MvPolynomial (Fin n) ℝ), P.totalDegree ≤ s →
    (∀ g, g ≠ h → eval (p g) P = 0) → eval (p h) P = 0

/-- A relation among nonzero first jets annihilating every ordinary polynomial
of degree at most `D` forces reduced Cayley--Bacharach at each `s` with
`2*s+1 ≤ D`. All coefficients and directions are arbitrary real numbers. -/
theorem reducedCB_of_ordinary_firstJet_relation
    (p v : Fin H → Fin n → ℝ) (c : Fin H → ℝ) (D s : ℕ)
    (hinj : Function.Injective p)
    (hessential : ∀ h, c h ≠ 0 ∨ v h ≠ 0)
    (hmoment : ∀ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ D →
      ∑ h, jet (p h) (v h) (c h) P = 0)
    (horder : 2 * s + 1 ≤ D) : ReducedCB p s := by
  classical
  refine ⟨hinj, ?_⟩
  intro h P hP hvanish
  have hP2 : (P ^ 2).totalDegree ≤ D := by
    have hd := totalDegree_pow P 2
    omega
  by_cases hv : v h = 0
  · have hc : c h ≠ 0 := (hessential h).resolve_right (not_not_intro hv)
    have hm := hmoment (P ^ 2) hP2
    have hsum : (∑ g, jet (p g) (v g) (c g) (P ^ 2)) =
        c h * (eval (p h) P) ^ 2 := by
      rw [sum_eq_single h]
      · simp [hv, jet_direction_zero]
      · intro g _ hgh
        exact jet_square_zero _ _ _ _ (hvanish g hgh)
      · simp
    rw [hsum] at hm
    exact sq_eq_zero_iff.mp (mul_eq_zero.mp hm |>.resolve_left hc)
  · obtain ⟨i, hi⟩ : ∃ i, v h i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv (funext hall)
    let Q : MvPolynomial (Fin n) ℝ := P ^ 2 * (X i - C (p h i))
    have hlin : (X i - C (p h i) : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 := by
      exact (totalDegree_sub _ _).trans (by simp)
    have hQ : Q.totalDegree ≤ D := by
      have hm := totalDegree_mul (P ^ 2) (X i - C (p h i))
      have hs := totalDegree_pow P 2
      dsimp [Q]
      omega
    have hm := hmoment Q hQ
    have hsum : (∑ g, jet (p g) (v g) (c g) Q) =
        (eval (p h) P) ^ 2 * v h i := by
      rw [sum_eq_single h]
      · exact jet_square_coordinate _ _ _ _ _
      · intro g _ hgh
        exact jet_square_mul_zero _ _ _ _ _ (hvanish g hgh)
      · simp
    rw [hsum] at hm
    exact sq_eq_zero_iff.mp (mul_eq_zero.mp hm |>.resolve_right hi)

/-- The standard integer half-order formulation. -/
theorem reducedCB_half_order
    (p v : Fin H → Fin n → ℝ) (c : Fin H → ℝ) (D : ℕ) (hD : 1 ≤ D)
    (hinj : Function.Injective p)
    (hessential : ∀ h, c h ≠ 0 ∨ v h ≠ 0)
    (hmoment : ∀ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ D →
      ∑ h, jet (p h) (v h) (c h) P = 0) :
    ReducedCB p ((D - 1) / 2) := by
  apply reducedCB_of_ordinary_firstJet_relation p v c D _ hinj hessential hmoment
  omega

end HeadComplexity.FirstJetCayleyBacharach
