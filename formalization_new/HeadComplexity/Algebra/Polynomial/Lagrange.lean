module

public import Mathlib.LinearAlgebra.Lagrange

/-!
# Reciprocal expansion at distinct poles

We use the barycentric form of the Lagrange interpolant to expand the quotient
of a bounded-degree polynomial by the nodal polynomial.
-/

public section

open scoped BigOperators

namespace Polynomial

variable {K ι : Type*} [Field K] {s : Finset ι} {a : ι → K}

/-- A polynomial of degree at most the number of distinct nodes is a multiple of their
nodal polynomial plus a linear combination of the nodal polynomials with one node erased. -/
theorem exists_eq_C_mul_nodal_add_sum [DecidableEq ι] (p : K[X]) (ha : Set.InjOn a s)
    (hp : p.natDegree ≤ s.card) :
    ∃ (c : K) (b : ι → K),
      p = C c * Lagrange.nodal s a + ∑ i ∈ s, C (b i) * Lagrange.nodal (s.erase i) a := by
  classical
  let Q := Lagrange.nodal s a
  let R := p %ₘ Q
  let c := (p /ₘ Q).coeff 0
  let b i := Lagrange.nodalWeight s a i * R.eval (a i)
  have hQ : Q.Monic := Lagrange.nodal_monic
  have hquo : p /ₘ Q = C c := by
    apply eq_C_of_natDegree_le_zero
    rw [natDegree_divByMonic _ hQ, Nat.sub_eq_zero_of_le (by simpa [Q] using hp)]
  have hR : R.degree < s.card := by
    simpa [R, Q] using degree_modByMonic_lt p hQ
  refine ⟨c, b, ?_⟩
  change p = C c * Q + _
  rw [← modByMonic_add_div p Q, hquo, mul_comm Q, add_comm R]
  congr 1
  rw [Lagrange.eq_interpolate ha hR, Lagrange.interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [← Lagrange.nodal_erase_eq_nodal_div hi, mul_right_comm, ← map_mul]

/-- Dividing a polynomial of degree at most `s.card` by the nodal polynomial
gives a constant plus one reciprocal term per node, away from those nodes. -/
theorem exists_eval_div_nodal_eq_const_add_sum_div (p : K[X]) (ha : Set.InjOn a s)
    (hp : p.natDegree ≤ s.card) :
    ∃ (c : K) (b : ι → K), ∀ x, (∀ i ∈ s, x ≠ a i) →
      p.eval x / (Lagrange.nodal s a).eval x = c + ∑ i ∈ s, b i / (x - a i) := by
  classical
  obtain ⟨c, b, hp⟩ := p.exists_eq_C_mul_nodal_add_sum ha hp
  refine ⟨c, b, fun x hx ↦ (div_eq_iff (Lagrange.eval_nodal_not_at_node hx)).2 ?_⟩
  rw [hp, add_mul, Finset.sum_mul]
  simp only [eval_add, eval_mul, eval_finsetSum, eval_C]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  conv_rhs => rw [Lagrange.nodal_eq_mul_nodal_erase hi]
  rw [eval_mul, eval_sub, eval_X, eval_C, ← mul_assoc,
    div_mul_cancel₀ _ (sub_ne_zero.mpr (hx i hi))]

end Polynomial
