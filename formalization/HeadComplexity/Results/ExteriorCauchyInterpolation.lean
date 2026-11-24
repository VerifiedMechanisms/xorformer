import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

set_option linter.style.header false

/-!
Positive interpolation by signed exterior Cauchy columns.

This verifies the root-only positive-spanning ingredient. It does not assert
simultaneous descendant feasibility or a superlinear query decoder.
-/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators
open Polynomial

/-- The partial-fraction form of polynomial interpolation at distinct poles. -/
theorem exterior_cauchy_barycentric {H : ℕ} (p : Fin H → ℝ)
    (hp : Function.Injective p) (N : ℝ[X]) (hN : N.degree < H)
    (t : ℝ) (ht : ∀ h, t ≠ p h) :
    (∑ h, N.eval (p h) * Lagrange.nodalWeight Finset.univ p h / (t - p h)) =
      N.eval t / (Lagrange.nodal Finset.univ p).eval t := by
  have hpi : Set.InjOn p (Finset.univ : Finset (Fin H)) := hp.injOn
  have hN' : N.degree < (Finset.univ : Finset (Fin H)).card := by simpa using hN
  have he := Lagrange.eval_interpolate_not_at_node
    (s := Finset.univ) (v := p) (fun h ↦ N.eval (p h)) (x := t)
    (fun h _ ↦ ht h)
  rw [← Lagrange.eq_interpolate hpi hN'] at he
  have hn : (Lagrange.nodal Finset.univ p).eval t ≠ 0 :=
    Lagrange.eval_nodal_not_at_node (fun h _ ↦ ht h)
  apply (eq_div_iff hn).mpr
  rw [he]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- Adding a polynomial that is positive at every pole makes all numerators
strictly positive, while preserving its zeros at every query. -/
theorem exists_positive_polynomial_shift {H : ℕ} (p : Fin H → ℝ)
    (P Q : ℝ[X]) (hQ : ∀ h, 0 < Q.eval (p h)) :
    ∃ shift : ℝ, ∀ h, 0 < (P + C shift * Q).eval (p h) := by
  let shift : ℝ := 1 + ∑ h, |P.eval (p h)| / Q.eval (p h)
  refine ⟨shift, ?_⟩
  intro h
  have hterm : |P.eval (p h)| / Q.eval (p h) ≤
      ∑ k, |P.eval (p k)| / Q.eval (p k) :=
    Finset.single_le_sum (fun k _ ↦ div_nonneg (abs_nonneg (P.eval (p k))) (le_of_lt (hQ k)))
      (Finset.mem_univ h)
  have hlt : |P.eval (p h)| / Q.eval (p h) < shift := by dsimp [shift]; linarith
  have hmul := (div_lt_iff₀ (hQ h)).mp hlt
  simp only [eval_add, eval_mul, eval_C]
  have habs := neg_abs_le (P.eval (p h))
  linarith

/-- Any q real query values are realized by q+1 exterior Cauchy columns
with strictly positive coefficients after their fixed barycentric signs.
The poles and query times may be arbitrarily close, but are distinct and
every pole is below every query. -/
theorem exists_positive_exterior_cauchy_interpolation {q : ℕ}
    (p : Fin (q + 1) → ℝ) (t y : Fin q → ℝ)
    (hp : Function.Injective p) (ht : Function.Injective t)
    (hpt : ∀ h j, p h < t j) :
    ∃ a : Fin (q + 1) → ℝ, (∀ h, 0 < a h) ∧
      ∀ j, (∑ h, a h * Lagrange.nodalWeight Finset.univ p h / (t j - p h)) = y j := by
  let P : ℝ[X] := Lagrange.interpolate Finset.univ t
    (fun j ↦ y j * (Lagrange.nodal Finset.univ p).eval (t j))
  let Q : ℝ[X] := ∏ j : Fin q, (C (t j) - X)
  have hQpos (h : Fin (q + 1)) : 0 < Q.eval (p h) := by
    simp only [Q, eval_prod, eval_sub, eval_C, eval_X]
    exact Finset.prod_pos (fun j _ ↦ sub_pos.mpr (hpt h j))
  obtain ⟨shift, hshift⟩ := exists_positive_polynomial_shift p P Q hQpos
  let N := P + C shift * Q
  refine ⟨fun h ↦ N.eval (p h), hshift, ?_⟩
  have hP : P.degree < (q : WithBot ℕ) := by
    simpa [P] using Lagrange.degree_interpolate_lt
      (s := Finset.univ) (v := t)
      (fun j ↦ y j * (Lagrange.nodal Finset.univ p).eval (t j)) ht.injOn
  have hQdeg : Q.natDegree ≤ q := by
    calc
      _ ≤ ∑ j : Fin q, (C (t j) - X : ℝ[X]).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _j : Fin q, 1 := Finset.sum_le_sum (fun j _ ↦ by
        exact (Polynomial.natDegree_sub_le _ _).trans (by simp))
      _ = q := by simp
  have hQ : Q.degree < (q + 1 : ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hQdeg)
      (by exact_mod_cast Nat.lt_succ_self q)
  have hN : N.degree < (q + 1 : ℕ) := by
    apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    apply max_lt
    · exact hP.trans (by exact_mod_cast Nat.lt_succ_self q)
    · have hm : (C shift * Q).degree ≤ Q.degree := by
        calc
          _ ≤ (C shift : ℝ[X]).degree + Q.degree := Polynomial.degree_mul_le _ _
          _ ≤ 0 + Q.degree := add_le_add (Polynomial.degree_C_le (a := shift)) le_rfl
          _ = Q.degree := zero_add _
      exact hm.trans_lt hQ
  intro j
  rw [exterior_cauchy_barycentric p hp N hN (t j)
    (fun h ↦ ne_of_gt (hpt h j))]
  have hQzero : Q.eval (t j) = 0 := by
    simp only [Q, eval_prod, eval_sub, eval_C, eval_X]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)
  have hPeval : P.eval (t j) = y j * (Lagrange.nodal Finset.univ p).eval (t j) :=
    Lagrange.eval_interpolate_at_node _ ht.injOn (Finset.mem_univ j)
  simp only [N, eval_add, eval_mul, eval_C, hQzero, mul_zero, add_zero, hPeval]
  exact mul_div_cancel_right₀ _ (Lagrange.eval_nodal_not_at_node
    (fun h _ ↦ ne_of_gt (hpt h j)))

end HeadComplexity.AxisZeroGluing
