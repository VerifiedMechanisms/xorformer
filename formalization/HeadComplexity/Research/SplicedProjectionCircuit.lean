import HeadComplexity.Research.BooleanProjectionChainCircuit
import Mathlib.LinearAlgebra.Lagrange

set_option linter.style.header false

/-!
The exact kernel and moment identities behind the spliced-circuit obstruction.
The accompanying written proof establishes support minimality and affine rank;
those structural conclusions are not asserted by this module.
-/
noncomputable section
namespace HeadComplexity.SplicedProjectionCircuit
open Finset
open scoped BigOperators
open BooleanProjectionChainCircuit

/-- The chain with its zero point and first upper point removed. It has
`2 * (n + 1)` displayed atoms. -/
def chainRemainder (n : ℕ) (F : ℝ → ℝ) (x : ℕ → Bool) : ℝ :=
  F (partialSum x (n + 1)) + F (1 - boolToReal (x 0)) +
    ∑ i ∈ range n, (F (1 + partialSum x (i + 1) - boolToReal (x (i + 1))) -
      F (1 + partialSum x (i + 1)))

/-- A full-dimensional chain can have exactly the scalar observations of two
fixed intercept-axis atoms. This is an all-kernel identity. -/
theorem chain_remainder_identity (n : ℕ) (F : ℝ → ℝ) (x : ℕ → Bool) :
    chainRemainder n F x = F 0 + F 1 := by
  have h := scalar_function_identity F 0 x (n + 1)
  rw [sum_range_succ'] at h
  simp only [partialSum_zero, zero_add, add_zero] at h
  unfold chainRemainder
  linarith

variable {q : ℕ}

def lineResidue (nodes : Fin q → ℝ) (j : Fin q) : ℝ :=
  -((Lagrange.basis univ nodes j).eval 0 + (Lagrange.basis univ nodes j).eval 1)

/-- Lagrange interpolation replaces two point evaluations by `q` line atoms
for every polynomial of degree less than `q`. -/
theorem two_point_polynomial_identity (nodes : Fin q → ℝ)
    (hinj : Function.Injective nodes) (p : Polynomial ℝ)
    (hp : p.degree < q) :
    p.eval 0 + p.eval 1 + ∑ j, lineResidue nodes j * p.eval (nodes j) = 0 := by
  have hi : Set.InjOn nodes (univ : Finset (Fin q)) :=
    fun _ _ _ _ h => hinj h
  have he := Lagrange.eq_interpolate hi (by simpa using hp)
  have h0 := congrArg (fun f : Polynomial ℝ => f.eval 0) he
  have h1 := congrArg (fun f : Polynomial ℝ => f.eval 1) he
  simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C] at h0 h1
  rw [h0, h1]
  simp only [lineResidue, neg_add_rev, add_mul, neg_mul]
  rw [sum_add_distrib, sum_neg_distrib, sum_neg_distrib]
  have hc0 : (∑ j, p.eval (nodes j) * (Lagrange.basis univ nodes j).eval 0) =
      ∑ j, (Lagrange.basis univ nodes j).eval 0 * p.eval (nodes j) := by
    apply sum_congr rfl
    intro j _
    ring
  have hc1 : (∑ j, p.eval (nodes j) * (Lagrange.basis univ nodes j).eval 1) =
      ∑ j, (Lagrange.basis univ nodes j).eval 1 * p.eval (nodes j) := by
    apply sum_congr rfl
    intro j _
    ring
  rw [hc0, hc1]
  ring

/-- The displayed spliced cloud annihilates every degree-bounded Boolean
projection moment. No exact-score or margin conclusion is inferred. -/
theorem spliced_polynomial_identity (n : ℕ) (nodes : Fin q → ℝ)
    (hinj : Function.Injective nodes) (p : Polynomial ℝ) (hp : p.degree < q)
    (x : ℕ → Bool) :
    chainRemainder n p.eval x + ∑ j, lineResidue nodes j * p.eval (nodes j) = 0 := by
  rw [chain_remainder_identity]
  exact two_point_polynomial_identity nodes hinj p hp

end HeadComplexity.SplicedProjectionCircuit
