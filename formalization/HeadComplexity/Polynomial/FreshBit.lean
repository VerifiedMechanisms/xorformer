import HeadComplexity.Polynomial.StrictSign
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Degrees

set_option linter.style.header false

/-!
# Polynomials with one fresh Boolean coordinate

This module treats the first coordinate of `Fin (m + 1)` as a fresh bit and
the successor coordinates as an `m`-bit input.  It supplies polynomial lifting,
specialization to either fresh-bit slice, and the degree-lowering difference of
the two slices.  The last construction is the algebraic core of the theorem
that XOR with a fresh bit raises threshold degree by one.
-/

namespace HeadComplexity

open Finset MvPolynomial

variable {m : ℕ}

/-- Prepend a fresh Boolean coordinate to an `m`-bit input. -/
def consBit (z : Bool) (y : Fin m → Bool) : Fin (m + 1) → Bool :=
  Fin.cases z y

/-- Remove the first coordinate of an `(m+1)`-bit input. -/
def tailBits (x : Fin (m + 1) → Bool) : Fin m → Bool :=
  fun i ↦ x i.succ

@[simp] theorem consBit_zero (z : Bool) (y : Fin m → Bool) :
    consBit z y 0 = z := by
  simp [consBit]

@[simp] theorem consBit_succ (z : Bool) (y : Fin m → Bool) (i : Fin m) :
    consBit z y i.succ = y i := by
  simp [consBit]

@[simp] theorem tailBits_consBit (z : Bool) (y : Fin m → Bool) :
    tailBits (consBit z y) = y := by
  funext i
  simp [tailBits]

@[simp] theorem consBit_head_tail (x : Fin (m + 1) → Bool) :
    consBit (x 0) (tailBits x) = x := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp [tailBits]

/-- Lift a polynomial on the tail coordinates to one which ignores the fresh
first coordinate. -/
noncomputable def liftFreshPolynomial
    (P : MvPolynomial (Fin m) ℝ) : MvPolynomial (Fin (m + 1)) ℝ :=
  rename Fin.succ P

@[simp] theorem liftFreshPolynomial_eval
    (P : MvPolynomial (Fin m) ℝ) (z : Bool) (y : Fin m → Bool) :
    eval (cubePoint (consBit z y)) (liftFreshPolynomial P) =
      eval (cubePoint y) P := by
  rw [liftFreshPolynomial, eval_rename]
  congr 1

theorem liftFreshPolynomial_totalDegree_le
    (P : MvPolynomial (Fin m) ℝ) :
    (liftFreshPolynomial P).totalDegree ≤ P.totalDegree :=
  totalDegree_rename_le Fin.succ P

/-- Multiply a tail polynomial by `1 - 2z`, the sign switch associated with
XOR by the fresh bit. -/
noncomputable def freshXorPolynomial
    (P : MvPolynomial (Fin m) ℝ) : MvPolynomial (Fin (m + 1)) ℝ :=
  (C 1 - C 2 * X 0) * liftFreshPolynomial P

@[simp] theorem freshXorPolynomial_eval
    (P : MvPolynomial (Fin m) ℝ) (z : Bool) (y : Fin m → Bool) :
    eval (cubePoint (consBit z y)) (freshXorPolynomial P) =
      (if z then -1 else 1) * eval (cubePoint y) P := by
  cases z
  · simp [freshXorPolynomial, cubePoint, boolToReal]
  · simp [freshXorPolynomial, cubePoint, boolToReal]
    ring

theorem freshXorPolynomial_totalDegree_le
    (P : MvPolynomial (Fin m) ℝ) (d : ℕ) (hP : P.totalDegree ≤ d) :
    (freshXorPolynomial P).totalDegree ≤ d + 1 := by
  unfold freshXorPolynomial
  have hfactor :
      ((C 1 : MvPolynomial (Fin (m + 1)) ℝ) - C 2 * X 0).totalDegree ≤ 1 := by
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · simp
    · refine (totalDegree_mul _ _).trans ?_
      simp
  have hlift : (liftFreshPolynomial P).totalDegree ≤ d :=
    (liftFreshPolynomial_totalDegree_le P).trans hP
  have := (totalDegree_mul
    (C 1 - C 2 * X (0 : Fin (m + 1))) (liftFreshPolynomial P)).trans
      (Nat.add_le_add hfactor hlift)
  omega

/-- View an `(m+1)`-variable polynomial as a univariate polynomial in its
fresh first coordinate, with `m`-variable coefficients. -/
noncomputable def asFreshPolynomial
    (P : MvPolynomial (Fin (m + 1)) ℝ) :
    Polynomial (MvPolynomial (Fin m) ℝ) :=
  finSuccEquiv ℝ m P

/-- Specialize the fresh coordinate of a polynomial to a Boolean value. -/
noncomputable def freshSlicePolynomial (z : Bool)
    (P : MvPolynomial (Fin (m + 1)) ℝ) : MvPolynomial (Fin m) ℝ :=
  Polynomial.eval (C (boolToReal z)) (asFreshPolynomial P)

@[simp] theorem freshSlicePolynomial_eval (z : Bool)
    (P : MvPolynomial (Fin (m + 1)) ℝ) (y : Fin m → Bool) :
    eval (cubePoint y) (freshSlicePolynomial z P) =
      eval (cubePoint (consBit z y)) P := by
  rw [freshSlicePolynomial, asFreshPolynomial,
    eval_polynomial_eval_finSuccEquiv]
  apply congrArg (fun v ↦ eval v P)
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [cubePoint, consBit]
  · simp [cubePoint, consBit]

/-- Every coefficient in the fresh-variable presentation has total degree no
larger than the original polynomial. -/
private theorem totalDegree_coeff_asFreshPolynomial_le
    (P : MvPolynomial (Fin (m + 1)) ℝ) (i : ℕ) :
    ((asFreshPolynomial P).coeff i).totalDegree ≤ P.totalDegree := by
  by_cases hi : (asFreshPolynomial P).coeff i = 0
  · simp [hi]
  · exact le_trans (Nat.le_add_right _ i)
      (totalDegree_coeff_finSuccEquiv_add_le P i hi)

/-- Specializing a fresh Boolean coordinate does not increase total degree. -/
theorem freshSlicePolynomial_totalDegree_le (z : Bool)
    (P : MvPolynomial (Fin (m + 1)) ℝ) :
    (freshSlicePolynomial z P).totalDegree ≤ P.totalDegree := by
  classical
  unfold freshSlicePolynomial
  rw [Polynomial.eval_eq_sum]
  apply totalDegree_finsetSum_le
  intro i hi
  refine (totalDegree_mul _ _).trans ?_
  rw [← map_pow, totalDegree_C, Nat.add_zero]
  exact totalDegree_coeff_asFreshPolynomial_le P i

/-- The coefficient sum over positive fresh-coordinate exponents.  On Boolean
inputs it is exactly the value on the `true` slice minus the value on the
`false` slice. -/
noncomputable def freshDifferencePolynomial
    (P : MvPolynomial (Fin (m + 1)) ℝ) : MvPolynomial (Fin m) ℝ :=
  (asFreshPolynomial P).sum fun i A ↦ if i = 0 then 0 else A

theorem freshDifferencePolynomial_eq
    (P : MvPolynomial (Fin (m + 1)) ℝ) :
    freshDifferencePolynomial P =
      freshSlicePolynomial true P - freshSlicePolynomial false P := by
  classical
  unfold freshDifferencePolynomial freshSlicePolynomial
  rw [show boolToReal true = 1 by rfl, show boolToReal false = 0 by rfl]
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h0 : i = 0
  · subst i
    simp
  · simp [h0]

@[simp] theorem freshDifferencePolynomial_eval
    (P : MvPolynomial (Fin (m + 1)) ℝ) (y : Fin m → Bool) :
    eval (cubePoint y) (freshDifferencePolynomial P) =
      eval (cubePoint (consBit true y)) P -
        eval (cubePoint (consBit false y)) P := by
  rw [freshDifferencePolynomial_eq, map_sub,
    freshSlicePolynomial_eval, freshSlicePolynomial_eval]

/-- Taking the difference of the two Boolean slices removes at least one
fresh-coordinate degree. -/
theorem freshDifferencePolynomial_totalDegree_le
    (P : MvPolynomial (Fin (m + 1)) ℝ) :
    (freshDifferencePolynomial P).totalDegree ≤ P.totalDegree - 1 := by
  classical
  unfold freshDifferencePolynomial
  rw [Polynomial.sum_def]
  apply totalDegree_finsetSum_le
  intro i hi
  by_cases h0 : i = 0
  · simp [h0]
  · simp only [h0, if_false]
    by_cases hcoeff : (asFreshPolynomial P).coeff i = 0
    · simp [hcoeff]
    · have hadd : ((asFreshPolynomial P).coeff i).totalDegree + i ≤
          P.totalDegree := by
        simpa [asFreshPolynomial] using
          (totalDegree_coeff_finSuccEquiv_add_le P i (by simpa [asFreshPolynomial] using hcoeff))
      have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr h0
      omega

end HeadComplexity
