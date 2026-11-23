import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

open scoped BigOperators
open Polynomial

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]
variable {n : ℕ}

local instance : DecidableEq R[X] := Classical.decEq _

/-- Substitution on a Boolean projection curve. The coefficient variable
is left formal, so this asserts a polynomial identity, not a numerical test. -/
noncomputable def booleanProjectionEval (x : Fin n → Bool) :
    MvPolynomial (Fin n) R[X] →+* R[X] :=
  MvPolynomial.eval fun i => if x i then Polynomial.X else 1

/-- A generator vanishing on every Boolean projection curve. -/
noncomputable def booleanProjectionGenerator (i : Fin n) :
    MvPolynomial (Fin n) R[X] :=
  (MvPolynomial.X i - 1) *
    (MvPolynomial.X i - MvPolynomial.C Polynomial.X)

private theorem polynomial_X_ne_one : (Polynomial.X : R[X]) ≠ 1 := by
  simpa using Polynomial.X_ne_C (1 : R)

private theorem booleanProjectionGenerator_eq_prod (i : Fin n) :
    booleanProjectionGenerator (R := R) i =
      ∏ r ∈ ({1, Polynomial.X} : Finset R[X]),
        (MvPolynomial.X i - MvPolynomial.C r) := by
  classical
  simp [booleanProjectionGenerator, Ne.symm polynomial_X_ne_one]

omit [IsDomain R] in
private theorem booleanProjectionEval_generator (x : Fin n → Bool) (i : Fin n) :
    booleanProjectionEval x (booleanProjectionGenerator (R := R) i) = 0 := by
  simp only [booleanProjectionEval, booleanProjectionGenerator, map_mul, map_sub,
    MvPolynomial.eval_X, map_one, MvPolynomial.eval_C]
  cases x i <;> simp

private theorem projection_grid_vanishing
    (P : MvPolynomial (Fin n) R[X])
    (h : ∀ x : Fin n → Bool, booleanProjectionEval x P = 0)
    (v : Fin n → R[X])
    (hv : ∀ i, v i ∈ ({1, Polynomial.X} : Finset R[X])) :
    MvPolynomial.eval v P = 0 := by
  classical
  let x : Fin n → Bool := fun i => decide (v i = Polynomial.X)
  have hx : (fun i => if x i then Polynomial.X else 1) = v := by
    funext i
    by_cases hi : v i = Polynomial.X
    · simp [x, hi]
    · have hi' : v i = 1 := by
        simpa [hi] using hv i
      simp [x, hi', Ne.symm polynomial_X_ne_one]
  simpa only [booleanProjectionEval, hx] using h x

/-- Exact kernel theorem for the Boolean projection curves, including the
degree control supplied by the combinatorial Nullstellensatz. This does
not bound the support of the coefficient polynomials or the number of heads. -/
theorem booleanProjection_vanishing_iff_linearCombination
    (P : MvPolynomial (Fin n) R[X]) :
    (∀ x : Fin n → Bool, booleanProjectionEval x P = 0) ↔
      ∃ q : Fin n →₀ MvPolynomial (Fin n) R[X],
        (∀ i, (booleanProjectionGenerator i * q i).totalDegree ≤ P.totalDegree) ∧
        P = Finsupp.linearCombination (MvPolynomial (Fin n) R[X])
          booleanProjectionGenerator q := by
  classical
  constructor
  · intro h
    obtain ⟨q, hq, heq⟩ :=
      MvPolynomial.combinatorial_nullstellensatz_exists_linearCombination
        (fun _ : Fin n => ({1, Polynomial.X} : Finset R[X]))
        (fun _ => by simp) P (projection_grid_vanishing P h)
    have hg : (fun i : Fin n =>
        ∏ r ∈ ({1, Polynomial.X} : Finset R[X]),
          (MvPolynomial.X i - MvPolynomial.C r)) =
        booleanProjectionGenerator := by
      funext i
      exact (booleanProjectionGenerator_eq_prod i).symm
    refine ⟨q, ?_, ?_⟩
    · intro i
      have hgi := congrFun hg i
      have hqi := hq i
      rw [hgi] at hqi
      exact hqi
    · rw [hg] at heq
      exact heq
  · rintro ⟨q, _, heq⟩ x
    rw [heq, Finsupp.linearCombination_apply, map_finsuppSum, Finsupp.sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [smul_eq_mul, map_mul, booleanProjectionEval_generator, mul_zero]

/-- A polynomial multilinear in the projection variables is determined
by its values on all Boolean projection curves. -/
theorem booleanProjection_multilinear_ext
    (P Q : MvPolynomial (Fin n) R[X])
    (hP : ∀ i, P.degreeOf i ≤ 1)
    (hQ : ∀ i, Q.degreeOf i ≤ 1)
    (h : ∀ x : Fin n → Bool, booleanProjectionEval x P = booleanProjectionEval x Q) :
    P = Q := by
  classical
  apply sub_eq_zero.mp
  apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset
    (P - Q) (fun _ : Fin n => ({1, Polynomial.X} : Finset R[X]))
  · intro i
    have hd := MvPolynomial.degreeOf_sub_le i P Q
    have hm : max (P.degreeOf i) (Q.degreeOf i) ≤ 1 := max_le (hP i) (hQ i)
    have hc : ({1, Polynomial.X} : Finset R[X]).card = 2 := by
      simp [Ne.symm polynomial_X_ne_one]
    rw [hc]
    omega
  · apply projection_grid_vanishing
    intro x
    rw [map_sub, h x, sub_self]

end

end HeadComplexity
