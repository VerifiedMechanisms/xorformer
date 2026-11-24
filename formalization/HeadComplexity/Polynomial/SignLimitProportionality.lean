import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Proportionality after polynomial divisibility

This supplies the final degree and sign step in the grid-limit argument. The
hypothesis that the source divides the limit is explicit; it is not inferred
here merely from finite Boolean sign agreement.
-/

namespace HeadComplexity
namespace SignLimitProportionality

open MvPolynomial

/-- A nonzero polynomial divisible by a source of at least its total degree is
necessarily a nonzero scalar multiple of that source. -/
theorem scalar_multiple_of_dvd_of_totalDegree_le {σ : Type*}
    (P Q : MvPolynomial σ ℝ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hdegree : Q.totalDegree ≤ P.totalDegree) (hdiv : P ∣ Q) :
    ∃ a : ℝ, a ≠ 0 ∧ Q = C a * P := by
  obtain ⟨R, hR⟩ := hdiv
  have hRne : R ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hR
    exact hQ hR
  have hdeg := totalDegree_mul_of_isDomain hP hRne
  have hRzero : R.totalDegree = 0 := by
    rw [← hR] at hdeg
    omega
  have hconstant := totalDegree_eq_zero_iff_eq_C.mp hRzero
  refine ⟨R.coeff 0, ?_, ?_⟩
  · intro hz
    rw [hz, C_0] at hconstant
    exact hRne hconstant
  · calc
      Q = P * R := hR
      _ = P * C (R.coeff 0) := congrArg (P * ·) hconstant
      _ = C (R.coeff 0) * P := mul_comm _ _

/-- One strict positive source point and weak positive limit value determine the
positive orientation of a nonzero scalar multiple. -/
theorem positive_scalar_multiple_of_dvd_of_totalDegree_le {σ : Type*}
    (P Q : MvPolynomial σ ℝ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hdegree : Q.totalDegree ≤ P.totalDegree) (hdiv : P ∣ Q)
    (x : σ → ℝ) (hPx : 0 < eval x P) (hQx : 0 ≤ eval x Q) :
    ∃ a : ℝ, 0 < a ∧ Q = C a * P := by
  obtain ⟨a, ha, he⟩ := scalar_multiple_of_dvd_of_totalDegree_le P Q hP hQ hdegree hdiv
  refine ⟨a, ?_, he⟩
  have hmul : 0 ≤ a * eval x P := by simpa only [he, map_mul, eval_C] using hQx
  have hnonneg : 0 ≤ a := by nlinarith
  exact lt_of_le_of_ne hnonneg (Ne.symm ha)


/-- A real polynomial that vanishes on a nonempty open set is zero. The proof
extracts a product of nonempty open intervals and uses polynomial extensionality. -/
theorem eq_zero_of_eval_zero_on_open {σ : Type*} [Finite σ]
    (P : MvPolynomial σ ℝ) (U : Set (σ → ℝ)) (hU : IsOpen U)
    (hne : U.Nonempty) (hvanish : ∀ x ∈ U, eval x P = 0) : P = 0 := by
  letI := Fintype.ofFinite σ
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  apply MvPolynomial.funext_set (fun i ↦ Set.Ioo (x i - r) (x i + r))
    (fun i ↦ Set.Ioo_infinite (by linarith))
  intro y hy
  rw [map_zero]
  apply hvanish y
  apply hball
  apply (dist_pi_lt_iff hr).mpr
  intro i
  have hi := hy i (Set.mem_univ i)
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

end SignLimitProportionality
end HeadComplexity
