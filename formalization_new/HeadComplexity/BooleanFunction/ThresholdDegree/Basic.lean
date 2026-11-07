module

public import HeadComplexity.BooleanFunction.SignRepresentation
public import HeadComplexity.Data.Bool.Cube
public import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Fintype.EquivFin

/-!
# Threshold degree

The least total degree of a real polynomial whose signs represent a Boolean function.
Existence follows from interpolation on the Boolean cube.
-/

@[expose] public section

open scoped BigOperators

namespace MvPolynomial

variable {ι R : Type*} [CommRing R]

private noncomputable def cubeIndicator [Fintype ι] (x : ι → Bool) : MvPolynomial ι R :=
  ∏ i, if x i then X i else 1 - X i

/-- The vertex indicator polynomial evaluates to one at its designated vertex and zero at every
other vertex. -/
private theorem eval_cubeIndicator [Fintype ι] (x y : ι → Bool) [Decidable (x = y)] :
    eval (Bool.cubePoint R y) (cubeIndicator x) = if x = y then 1 else 0 := by
  classical
  rw [cubeIndicator, map_prod]
  split_ifs with h
  · subst y
    refine Finset.prod_eq_one fun i _ ↦ ?_
    cases hx : x i <;> simp [hx]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    cases hx : x i <;> cases hy : y i <;> simp [hx, hy] at hi ⊢

/-- Any values prescribed on the Boolean cube are the evaluations of a polynomial. -/
theorem exists_eval_cubePoint_eq [Finite ι] (a : (ι → Bool) → R) :
    ∃ p : MvPolynomial ι R, ∀ x, eval (Bool.cubePoint R x) p = a x := by
  classical
  let := Fintype.ofFinite ι
  refine ⟨∑ y, C (a y) * cubeIndicator y, fun x ↦ ?_⟩
  simp [eval_cubeIndicator, mul_ite]

end MvPolynomial

namespace HeadComplexity

variable {ι : Type*}

/-- A Boolean function has threshold degree at most `d` if a polynomial of total degree at
most `d` represents its signs on the Boolean cube. -/
def ThresholdDegreeLE (f : (ι → Bool) → Bool) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ d ∧
    Function.SignRepresents (fun x ↦ MvPolynomial.eval (Bool.cubePoint ℝ x) p) f

/-- A degree bound for a Boolean sign representation remains valid at any larger bound. -/
theorem ThresholdDegreeLE.mono {f : (ι → Bool) → Bool} {d e : ℕ}
    (h : ThresholdDegreeLE f d) (hde : d ≤ e) : ThresholdDegreeLE f e := by
  obtain ⟨p, hp, hf⟩ := h
  exact ⟨p, hp.trans hde, hf⟩

/-- Every Boolean function on a finite cube has a polynomial sign representation of some finite
degree. -/
theorem exists_thresholdDegreeLE [Finite ι] (f : (ι → Bool) → Bool) :
    ∃ d, ThresholdDegreeLE f d := by
  obtain ⟨p, hp⟩ := MvPolynomial.exists_eval_cubePoint_eq
    (fun x ↦ if f x then (1 : ℝ) else -1)
  refine ⟨p.totalDegree, p, le_rfl, fun x ↦ ?_⟩
  change 0 < MvPolynomial.eval (Bool.cubePoint ℝ x) p ↔ _
  rw [hp]
  cases f x <;> simp

/-- The least total degree of a polynomial that represents a Boolean function by its signs. -/
noncomputable def thresholdDegree [Finite ι] (f : (ι → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (exists_thresholdDegreeLE f)

/-- There is a polynomial sign representation that attains the threshold degree. -/
theorem thresholdDegreeLE_thresholdDegree [Finite ι] (f : (ι → Bool) → Bool) :
    ThresholdDegreeLE f (thresholdDegree f) := by
  classical
  exact Nat.find_spec (exists_thresholdDegreeLE f)

/-- The threshold degree is at most a given bound exactly when there is a sign representation of
degree at most that bound. -/
theorem thresholdDegree_le_iff [Finite ι] {f : (ι → Bool) → Bool} {d : ℕ} :
    thresholdDegree f ≤ d ↔ ThresholdDegreeLE f d := by
  classical
  exact ⟨(thresholdDegreeLE_thresholdDegree f).mono,
    Nat.find_min' (exists_thresholdDegreeLE f)⟩

/-- Any degree bound witnessed by a polynomial sign representation bounds the threshold degree. -/
theorem ThresholdDegreeLE.thresholdDegree_le [Finite ι] {f : (ι → Bool) → Bool} {d : ℕ}
    (h : ThresholdDegreeLE f d) : thresholdDegree f ≤ d :=
  thresholdDegree_le_iff.mpr h

end HeadComplexity
