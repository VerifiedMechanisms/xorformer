import HeadComplexity.Polynomial.AlgebraicRegularValues
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Algebra.MonoidAlgebra.Cardinal
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Generic polynomial levels

Algebraic independence over a countable coefficient field is dense in real
finite-dimensional space. It supplies generic levels without an assumption
of a polynomial regular-value theorem.
-/

namespace HeadComplexity.PolynomialRootCount

open MvPolynomial Set
open scoped Topology

/-- A nonzero real polynomial is nonzero on a dense set. -/
theorem dense_polynomial_ne_zero {ι : Type*} [Finite ι]
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) : Dense {x : ι → ℝ | eval x p ≠ 0} := by
  classical
  let := Fintype.ofFinite ι
  rw [dense_iff_inter_open]
  rintro U hU ⟨x, hx⟩
  by_contra hn
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  apply hp
  apply MvPolynomial.funext_set (fun i ↦ Ioo (x i - r) (x i + r))
    (fun i ↦ Ioo_infinite (by linarith))
  intro y hy
  simp only [map_zero]
  have hyball : y ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_pi_lt_iff hr]
    intro i
    rw [Real.dist_eq, abs_lt]
    have hi := hy i (mem_univ i)
    constructor <;> linarith [hi.1, hi.2]
  have hynot : ¬ eval y p ≠ 0 := by
    intro h
    exact hn ⟨y, hball hyball, h⟩
  exact not_not.mp hynot

/-- Algebraically independent real tuples over any countable subfield are dense. -/
theorem dense_algebraicIndependent (F : Type*) [Field F] [Countable F] [Algebra F ℝ]
    (ι : Type*) [Finite ι] : Dense {x : ι → ℝ | AlgebraicIndependent F x} := by
  classical
  let := Fintype.ofFinite ι
  let P := {p : MvPolynomial ι F // p ≠ 0}
  let U (p : P) : Set (ι → ℝ) := {x | aeval x p.1 ≠ 0}
  have heval (p : P) (x : ι → ℝ) :
      aeval x p.1 = eval x (map (algebraMap F ℝ) p.1) :=
    eval₂_eq_eval_map _ _ _
  have ho (p : P) : IsOpen (U p) := by
    simp_rw [U, heval]
    exact isOpen_ne.preimage (continuous_eval _)
  have hd (p : P) : Dense (U p) := by
    simp_rw [U, heval]
    apply dense_polynomial_ne_zero
    exact fun h ↦ p.2 ((map_injective _ (algebraMap F ℝ).injective) (h.trans (map_zero _).symm))
  apply (dense_iInter_of_isOpen ho hd).mono
  intro x hx
  rw [mem_ofPred_eq, algebraicIndependent_iff]
  intro p hp
  by_contra hn
  exact (mem_iInter.mp hx ⟨p, hn⟩) hp

/-- Adjoining a countable family to a countable field gives a countable field. -/
theorem countable_adjoin_range {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    [Countable F] [Countable ι] (a : ι → K) :
    Countable (IntermediateField.adjoin F (range a)) := by
  have hsub : (IntermediateField.adjoin F (range a) : Set K) ⊆
      range (fun p : MvPolynomial ι F × MvPolynomial ι F ↦ aeval a p.1 / aeval a p.2) := by
    intro x hx
    obtain ⟨p, q, h⟩ := (IntermediateField.mem_adjoin_range_iff F a x).mp hx
    exact ⟨(p, q), h.symm⟩
  exact (countable_range _).mono hsub |>.to_subtype

/-- Every countable polynomial family has a countable real coefficient field. -/
theorem exists_countable_coefficient_field {ι J : Type*} [Countable ι] [Countable J]
    (p : J → MvPolynomial ι ℝ) :
    ∃ F : IntermediateField ℚ ℝ, Countable F ∧
      ∀ j, ∃ q : MvPolynomial ι F, map F.subtype q = p j := by
  classical
  let a : J × (ι →₀ ℕ) → ℝ := fun ji ↦ (p ji.1).coeff ji.2
  let F := IntermediateField.adjoin ℚ (range a)
  refine ⟨F, countable_adjoin_range a, fun j ↦ ?_⟩
  apply mem_range_map_iff_coeffs_subset.mpr
  intro c hc
  obtain ⟨s, _, rfl⟩ := mem_coeffs_iff.mp hc
  exact ⟨⟨(p j).coeff s, IntermediateField.subset_adjoin ℚ _ ⟨(j, s), rfl⟩⟩, rfl⟩

end HeadComplexity.PolynomialRootCount
