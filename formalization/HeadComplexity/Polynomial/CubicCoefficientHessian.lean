import HeadComplexity.Polynomial.GenericCubicHessianPullback
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

set_option linter.style.header false

/-! # Ordinary cubic coefficient errors bound actual Hessian entries -/

namespace HeadComplexity.CubicCoefficientHessian
noncomputable section
open scoped BigOperators
open MvPolynomial

/-- The coefficient formula for one partial derivative, in ordinary monomial
coordinates. No homogeneous assumption is needed. -/
theorem coeff_pderiv {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (s : Fin n →₀ ℕ) :
    coeff s (pderiv i p) = (s i + 1 : ℕ) * coeff (s + Finsupp.single i 1) p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases hm : m i = 0
    · have hne : m ≠ s + Finsupp.single i 1 := by
        intro he
        have hi := congrArg (fun a : Fin n →₀ ℕ ↦ a i) he
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hi
        omega
      simp [hm, hne]
    · have hc : m - Finsupp.single i 1 + Finsupp.single i 1 = m :=
        Finsupp.sub_add_single_one_cancel hm
      have he : m - Finsupp.single i 1 = s ↔ m = s + Finsupp.single i 1 := by
        constructor
        · intro h
          rw [← hc, h]
        · intro h
          rw [h]
          simp
      by_cases hs : m = s + Finsupp.single i 1
      · simp [hs]
        ring
      · simp [he, hs]
  | add p q hp hq => simp [hp, hq, mul_add]

/-- The third derivative at the origin is the ordinary cubic coefficient
multiplied by a multiplicity between one and six. -/
theorem third_coeff_formula {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (i j k : Fin n) :
    coeff 0 (pderiv k (pderiv i (pderiv j p))) =
      ((Finsupp.single k 1 : Fin n →₀ ℕ) i + 1 : ℕ) *
      ((Finsupp.single k 1 + Finsupp.single i 1 : Fin n →₀ ℕ) j + 1 : ℕ) *
      coeff (Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1) p := by
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv]
  simp [mul_assoc]

/-- A coefficient error bound in ordinary monomial coordinates gives a uniform
sixfold error bound on the constant third-derivative tensor. -/
theorem third_coeff_abs_le {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (e : ℝ)
    (_he : 0 ≤ e) (hp : ∀ d, |coeff d p| ≤ e) (i j k : Fin n) :
    |coeff 0 (pderiv k (pderiv i (pderiv j p)))| ≤ 6 * e := by
  rw [third_coeff_formula, abs_mul, abs_mul]
  have hfirst : ((Finsupp.single k 1 : Fin n →₀ ℕ) i + 1 : ℕ) ≤ 2 := by
    simp only [Finsupp.single_apply]
    split_ifs <;> omega
  have hsecond : ((Finsupp.single k 1 + Finsupp.single i 1 : Fin n →₀ ℕ) j + 1 : ℕ) ≤ 3 := by
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hf : |(((Finsupp.single k 1 : Fin n →₀ ℕ) i + 1 : ℕ) : ℝ)| ≤ 2 := by
    simpa only [Nat.abs_cast] using
      (show (((Finsupp.single k 1 : Fin n →₀ ℕ) i + 1 : ℕ) : ℝ) ≤ 2 by
        exact_mod_cast hfirst)
  have hs : |(((Finsupp.single k 1 + Finsupp.single i 1 : Fin n →₀ ℕ) j + 1 : ℕ) : ℝ)| ≤ 3 := by
    simpa only [Nat.abs_cast] using
      (show (((Finsupp.single k 1 + Finsupp.single i 1 : Fin n →₀ ℕ) j + 1 : ℕ) : ℝ)
        ≤ 3 by exact_mod_cast hsecond)
  calc
    _ ≤ 2 * 3 * e := by gcongr; exact hp _
    _ = 6 * e := by ring

/-- Euler's identity writes every cubic Hessian as a linear slice of its
constant third-derivative tensor. -/
theorem eval_hessian_eq_sum {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous 3) (z : Fin n → ℝ) (i j : Fin n) :
    eval z (pderiv i (pderiv j p)) =
      ∑ k, z k * coeff 0 (pderiv k (pderiv i (pderiv j p))) := by
  have htwo : (pderiv i (pderiv j p)).IsHomogeneous 1 := by
    simpa using hp.pderiv.pderiv
  have hconst (k : Fin n) : pderiv k (pderiv i (pderiv j p)) =
      C (coeff 0 (pderiv k (pderiv i (pderiv j p)))) := by
    have hzero : (pderiv k (pderiv i (pderiv j p))).IsHomogeneous 0 := by
      simpa using htwo.pderiv
    exact totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous (Fin n)).mpr hzero)
  have heval (k : Fin n) : eval z (pderiv k (pderiv i (pderiv j p))) =
      coeff 0 (pderiv k (pderiv i (pderiv j p))) := by
    conv_lhs => rw [hconst]
    simp only [eval_C]
  have heuler := congrArg (eval z) htwo.sum_X_mul_pderiv
  simpa only [map_sum, map_mul, eval_X, heval, one_nsmul] using heuler.symm

/-- Ordinary coefficient bounds control every actual Hessian entry on the
coordinate cube of radius two. -/
theorem hessian_entry_abs_le {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous 3) (e : ℝ) (he : 0 ≤ e)
    (hc : ∀ d, |coeff d p| ≤ e) (z : Fin n → ℝ) (hz : ∀ k, |z k| ≤ 2)
    (i j : Fin n) : |eval z (pderiv i (pderiv j p))| ≤ 12 * n * e := by
  rw [eval_hessian_eq_sum p hp]
  calc
    _ ≤ ∑ k, |z k * coeff 0 (pderiv k (pderiv i (pderiv j p)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, 2 * (6 * e) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (hz k) (third_coeff_abs_le p e he hc i j k)
        (abs_nonneg _) (by norm_num)
    _ = 12 * n * e := by simp; ring

/-- The exact 168 factor used in the fourteen-variable raw coefficient gap. -/
theorem hessian_difference_le (p q : MvPolynomial (Fin 14) ℝ)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (e : ℝ) (he : 0 ≤ e) (hc : ∀ d, |coeff d p - coeff d q| ≤ e)
    (z : Fin 14 → ℝ) (hz : ∀ k, |z k| ≤ 2) (i j : Fin 14) :
    |GenericCubicHessianPullback.polynomialHessian p z i j -
      GenericCubicHessianPullback.polynomialHessian q z i j| ≤ 168 * e := by
  have h := hessian_entry_abs_le (p - q) (hp.sub hq) e he
    (by simpa using hc) z hz i j
  norm_num only [Nat.cast_ofNat] at h
  simpa only [GenericCubicHessianPullback.polynomialHessian, map_sub] using h

end
end HeadComplexity.CubicCoefficientHessian
