import HeadComplexity.Foundation.FiniteFeatureSignLimit
import Mathlib.Data.Finsupp.Weight
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Topology.Algebra.MvPolynomial

set_option linter.style.header false

/-!
# Compact normalized coefficients for bounded-degree polynomials

All normalizations in this file act on complete polynomial coefficient vectors,
not on parameters of a particular rational representation.
-/

namespace HeadComplexity.BoundedCoefficientLimit

open MvPolynomial
open scoped BigOperators Topology
open Filter

abbrev Exponent (n d : ℕ) := {e : Fin n →₀ ℕ // Finsupp.degree e ≤ d}

noncomputable instance (n d : ℕ) : Fintype (Exponent n d) :=
  (Finsupp.finite_of_degree_le (σ := Fin n) d).fintype

noncomputable def coefficients {n : ℕ} (d : ℕ) (P : MvPolynomial (Fin n) ℝ) :
    Exponent n d → ℝ := fun e ↦ P.coeff e.val

noncomputable def reconstruct {n d : ℕ} (a : Exponent n d → ℝ) :
    MvPolynomial (Fin n) ℝ := ∑ e, monomial e.val (a e)

@[simp] theorem coeff_reconstruct {n d : ℕ} (a : Exponent n d → ℝ)
    (e : Exponent n d) : (reconstruct a).coeff e.val = a e := by
  classical
  simp only [reconstruct, coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hbe
    exact if_neg (fun h ↦ hbe (Subtype.ext h))
  · simp

theorem coeff_reconstruct_of_large {n d : ℕ} (a : Exponent n d → ℝ)
    (e : Fin n →₀ ℕ) (he : d < Finsupp.degree e) :
    (reconstruct a).coeff e = 0 := by
  classical
  simp only [reconstruct, coeff_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [coeff_monomial]
  split_ifs with h
  · subst e
    omega
  · rfl

theorem coeff_zero_of_large {n d : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ d) (e : Fin n →₀ ℕ) (he : d < Finsupp.degree e) :
    P.coeff e = 0 := by
  by_contra hne
  have hmem : e ∈ P.support := mem_support_iff.mpr hne
  have hle := le_totalDegree hmem
  change Finsupp.degree e ≤ P.totalDegree at hle
  omega

theorem reconstruct_coefficients {n d : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ d) : reconstruct (coefficients d P) = P := by
  classical
  ext e
  by_cases he : Finsupp.degree e ≤ d
  · exact coeff_reconstruct (coefficients d P) ⟨e, he⟩
  · rw [coeff_reconstruct_of_large _ _ (by omega), coeff_zero_of_large P hP e (by omega)]

theorem totalDegree_reconstruct {n d : ℕ} (a : Exponent n d → ℝ) :
    (reconstruct a).totalDegree ≤ d := by
  apply totalDegree_finsetSum_le
  intro e he
  exact (totalDegree_monomial_le _ _).trans e.property

theorem reconstruct_injective {n d : ℕ} :
    Function.Injective (reconstruct (n := n) (d := d)) := by
  intro a b hab
  funext e
  have h := congrArg (fun P : MvPolynomial (Fin n) ℝ ↦ P.coeff e.val) hab
  simpa only [coeff_reconstruct] using h

theorem coefficients_ne_zero {n d : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ d) (hne : P ≠ 0) : coefficients d P ≠ 0 := by
  intro hz
  have he := reconstruct_coefficients P hP
  rw [hz] at he
  simp [reconstruct] at he
  exact hne he.symm

theorem normalized_polynomial_subsequence {n d : ℕ}
    (P : ℕ → MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ m, (P m).totalDegree ≤ d) (hne : ∀ m, P m ≠ 0) :
    ∃ (t : ℕ → ℝ) (Q : MvPolynomial (Fin n) ℝ) (φ : ℕ → ℕ),
      (∀ m, 0 < t m) ∧ Q ≠ 0 ∧ Q.totalDegree ≤ d ∧ StrictMono φ ∧
      ∀ e, Tendsto (fun k ↦ (C (t (φ k)) * P (φ k)).coeff e) atTop
        (𝓝 (Q.coeff e)) := by
  classical
  let a : ℕ → Exponent n d → ℝ := fun m ↦ coefficients d (P m)
  have ha : ∀ m, a m ≠ 0 := fun m ↦ coefficients_ne_zero (P m) (hdeg m) (hne m)
  let t : ℕ → ℝ := fun m ↦ ‖a m‖⁻¹
  have ht : ∀ m, 0 < t m := fun m ↦ inv_pos.mpr (norm_pos_iff.mpr (ha m))
  have hnorm : ∀ m, ‖t m • a m‖ = 1 := by
    intro m
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (ht m)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (ha m))
  obtain ⟨c, φ, _, hc, hφ, hlim⟩ :=
    normalized_coefficients_subsequence (fun m ↦ t m • a m) hnorm
  refine ⟨t, reconstruct c, φ, ht, ?_, totalDegree_reconstruct c, hφ, ?_⟩
  · intro hz
    apply hc
    funext e
    have he := congrArg (fun R : MvPolynomial (Fin n) ℝ ↦ R.coeff e.val) hz
    simpa only [coeff_reconstruct, coeff_zero, Pi.zero_apply] using he
  · intro e
    by_cases he : Finsupp.degree e ≤ d
    · have hh := (continuous_apply (⟨e, he⟩ : Exponent n d)).continuousAt.tendsto.comp hlim
      change Tendsto (fun k ↦ t (φ k) * (P (φ k)).coeff e) atTop
        (𝓝 (c ⟨e, he⟩)) at hh
      rw [show (reconstruct c).coeff e = c ⟨e, he⟩ from coeff_reconstruct c ⟨e, he⟩]
      simpa only [coeff_C_mul] using hh
    · have hlarge : d < Finsupp.degree e := by omega
      have hz (k : ℕ) : (C (t (φ k)) * P (φ k)).coeff e = 0 := by
        rw [coeff_C_mul, coeff_zero_of_large _ (hdeg (φ k)) _ hlarge, mul_zero]
      simp only [hz, coeff_reconstruct_of_large c e hlarge]
      exact tendsto_const_nhds

theorem tendsto_eval_of_bounded_coefficients {n d : ℕ}
    (P : ℕ → MvPolynomial (Fin n) ℝ) (Q : MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ m, (P m).totalDegree ≤ d) (hQdeg : Q.totalDegree ≤ d)
    (hcoeff : ∀ e, Tendsto (fun m ↦ (P m).coeff e) atTop (𝓝 (Q.coeff e)))
    (x : ℕ → Fin n → ℝ) (y : Fin n → ℝ)
    (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun m ↦ eval (x m) (P m)) atTop (𝓝 (eval y Q)) := by
  classical
  let F : Exponent n d → (Fin n → ℝ) → ℝ :=
    fun e z ↦ eval z (monomial e.val (1 : ℝ))
  have heval (R : MvPolynomial (Fin n) ℝ) (hR : R.totalDegree ≤ d)
      (z : Fin n → ℝ) :
      eval z R = ∑ e : Exponent n d, coefficients d R e * F e z := by
    conv_lhs => rw [← reconstruct_coefficients R hR]
    simp only [reconstruct, map_sum, eval_monomial, coefficients, F, one_mul]
  have hh := tendsto_finite_feature_eval F (fun m ↦ coefficients d (P m))
    (coefficients d Q) x y
    (fun e ↦ (MvPolynomial.continuous_eval (p := monomial e.val (1 : ℝ))).continuousAt)
    (tendsto_pi_nhds.mpr fun e ↦ hcoeff e.val) hx
  have heq : (fun m ↦ eval (x m) (P m)) =
      (fun m ↦ ∑ e : Exponent n d, coefficients d (P m) e * F e (x m)) :=
    funext fun m ↦ heval (P m) (hdeg m) (x m)
  rw [heq, heval Q hQdeg y]
  exact hh

end HeadComplexity.BoundedCoefficientLimit
