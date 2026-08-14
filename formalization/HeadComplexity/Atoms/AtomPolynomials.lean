import HeadComplexity.Atoms.FracAtom
import HeadComplexity.Polynomial.ModelToPolynomial

set_option linter.style.header false

/-!
# Polynomial presentation of fractional atoms

Every fractional atom is the quotient of an affine numerator polynomial by an
affine denominator polynomial.  The denominator is positive on the Boolean
cube.  These definitions and lemmas form the reusable bridge between the atom
normal form and polynomial clearing arguments.
-/

namespace HeadComplexity

open Finset MvPolynomial
open scoped BigOperators

namespace FracAtom

/-- The affine denominator polynomial of a fractional atom. -/
noncomputable def denPoly (φ : FracAtom n) : MvPolynomial (Fin n) ℝ :=
  C φ.γ + ∑ i, affineAt i (φ.ρ i) (φ.ρ i * φ.α)

/-- The affine numerator polynomial of a fractional atom. -/
noncomputable def numPoly (φ : FracAtom n) : MvPolynomial (Fin n) ℝ :=
  C φ.η + ∑ i, affineAt i (φ.ρ i * φ.m i)
    (φ.ρ i * φ.α * (φ.m i + φ.δ))

theorem denPoly_eval (φ : FracAtom n) (x : Fin n → Bool) :
    MvPolynomial.eval (cubePoint x) φ.denPoly = φ.γ + ∑ i, φ.wt x i := by
  simp only [denPoly, map_add, eval_C, map_sum, affineAt_eval]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold wt
  cases x i <;> simp

theorem numPoly_eval (φ : FracAtom n) (x : Fin n → Bool) :
    MvPolynomial.eval (cubePoint x) φ.numPoly =
      φ.η + ∑ i, φ.wt x i * (φ.m i + if x i then φ.δ else 0) := by
  simp only [numPoly, map_add, eval_C, map_sum, affineAt_eval]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  cases hx : x i
  · simp [wt, hx]
  · simp [wt, hx]

theorem denPoly_totalDegree_le (φ : FracAtom n) : φ.denPoly.totalDegree ≤ 1 := by
  unfold denPoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_C]
    omega
  · exact totalDegree_finsetSum_le (fun i _ => affineAt_totalDegree_le _ _ _)

theorem numPoly_totalDegree_le (φ : FracAtom n) : φ.numPoly.totalDegree ≤ 1 := by
  unfold numPoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_C]
    omega
  · exact totalDegree_finsetSum_le (fun i _ => affineAt_totalDegree_le _ _ _)

theorem eval_eq_numPoly_div_denPoly (φ : FracAtom n) (x : Fin n → Bool) :
    φ.eval x = MvPolynomial.eval (cubePoint x) φ.numPoly /
      MvPolynomial.eval (cubePoint x) φ.denPoly := by
  unfold FracAtom.eval
  rw [numPoly_eval, denPoly_eval]

theorem denPoly_pos (φ : FracAtom n) (x : Fin n → Bool) :
    0 < MvPolynomial.eval (cubePoint x) φ.denPoly := by
  rw [denPoly_eval]
  exact φ.denom_pos x

end FracAtom

end HeadComplexity
