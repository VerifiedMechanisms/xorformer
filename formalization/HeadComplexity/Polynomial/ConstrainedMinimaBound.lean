import HeadComplexity.Polynomial.GenericFiberBound
import HeadComplexity.Polynomial.PenaltyMinimization
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Counting strict constrained minima

A sum-of-squares penalty converts finitely many strict constrained minima into
distinct critical points of one polynomial of controlled degree. A generic
linear perturbation then permits the quantitative fiber bound.
-/

namespace HeadComplexity.PolynomialRootCount

open MvPolynomial Set Filter Metric
open scoped Topology

variable {n : ℕ}

/-- The linear polynomial with the given slope vector. -/
noncomputable def slopePolynomial (v : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, C (v i) * X i

@[simp]
theorem eval_slopePolynomial (v x : Fin n → ℝ) :
    eval x (slopePolynomial v) = ∑ i, v i * x i := by
  simp [slopePolynomial]

@[simp]
theorem pderiv_slopePolynomial (v : Fin n → ℝ) (i : Fin n) :
    pderiv i (slopePolynomial v) = C (v i) := by
  classical
  simp [slopePolynomial, Pi.single_apply, mul_ite]

/-- At a local minimum every formal partial derivative vanishes. -/
theorem eval_pderiv_eq_zero_of_isLocalMin (p : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : IsLocalMin (fun z ↦ eval z p) x) (i : Fin n) :
    eval x (pderiv i p) = 0 := by
  have h := hx.hasFDerivAt_eq_zero (hasStrictFDerivAt_eval p x).hasFDerivAt
  have hi := congrArg (fun D : (Fin n → ℝ) →L[ℝ] ℝ ↦ D (Pi.single i 1)) h
  simpa [evalDerivative, Pi.single_apply, mul_ite] using hi

/-- Disjoint strict boundary gaps force distinct critical points after a
generic linear perturbation, so their number is bounded by the polynomial degree. -/
theorem polynomial_boundary_minima_card_le {I : Type*} [Fintype I] {d : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ d + 1)
    (x : I → Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ i j, i ≠ j → 2 * r < dist (x i) (x j))
    (hbd : ∀ i y, y ∈ sphere (x i) r → eval (x i) p < eval y p) :
    Fintype.card I ≤ (d + 1) ^ n := by
  classical
  let f : (Fin n → ℝ) × (Fin n → ℝ) → ℝ :=
    fun z ↦ eval z.2 p - ∑ i, z.1 i * z.2 i
  have hf : Continuous f := (continuous_eval p |>.comp continuous_snd).sub (by fun_prop)
  have hgap (i : I) : ∀ᶠ v in 𝓝 (0 : Fin n → ℝ), ∀ y ∈ sphere (x i) r,
      f (v, x i) < f (v, y) := by
    apply compact_gap_eventually (isCompact_sphere (x i) r) f hf 0 (x i)
    simpa [f] using hbd i
  have hgaps : ∀ᶠ v in 𝓝 (0 : Fin n → ℝ), ∀ i y, y ∈ sphere (x i) r →
      f (v, x i) < f (v, y) := Filter.eventually_all.mpr hgap
  obtain ⟨v, hv, hvgap⟩ := (dense_polynomial_boundedFibers
    (fun i ↦ pderiv i p) (totalDegree_pderiv_le p hp)).inter_nhds_nonempty hgaps
  have hlocal (i : I) : ∃ y ∈ ball (x i) r,
      IsLocalMin (fun z ↦ eval z (p - slopePolynomial v)) y := by
    apply exists_localMin_of_boundary_lt (x i) hr (continuous_eval _)
    simpa [f] using hvgap i
  choose y hyball hymin using hlocal
  have hyinj : Function.Injective y := by
    intro i j hij
    by_contra hne
    have hs := hsep i j hne
    have hi : dist (x i) (y i) < r := by simpa [dist_comm] using hyball i
    have hj : dist (y i) (x j) < r := by rw [hij]; exact hyball j
    have ht := dist_triangle (x i) (y i) (x j)
    linarith
  have hyroot (a : I) (i : Fin n) : eval (y a) (pderiv i p) = v i := by
    have h := eval_pderiv_eq_zero_of_isLocalMin (p - slopePolynomial v) (y a) (hymin a) i
    simpa only [map_sub, pderiv_slopePolynomial, eval_C, sub_eq_zero] using h
  have hb := hv (Finset.univ.image y) (by
    intro z hz
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
    exact hyroot a)
  simpa [Finset.card_image_of_injective _ hyinj] using hb

/-- Finitely many distinct strict local minima of a degree-at-most-`2d`
objective on a degree-`d` algebraic set have cardinality at most `(2d)^n`. -/
theorem constrained_minima_card_le {J I : Type*} [Finite J] [Fintype I]
    {d : ℕ} (hd : 0 < d) (p : J → MvPolynomial (Fin n) ℝ)
    (hp : ∀ j, (p j).totalDegree ≤ d)
    (q : MvPolynomial (Fin n) ℝ) (hq : q.totalDegree ≤ 2 * d)
    (x : I → Fin n → ℝ) (hx : Function.Injective x)
    (hz : ∀ a j, eval (x a) (p j) = 0)
    (hmin : ∀ a, ∀ᶠ y in 𝓝 (x a), (∀ j, eval y (p j) = 0) →
      y ≠ x a → eval (x a) q < eval y q) :
    Fintype.card I ≤ (2 * d) ^ n := by
  classical
  let := Fintype.ofFinite J
  let S : MvPolynomial (Fin n) ℝ := ∑ j, (p j) ^ 2
  have hSeval (y : Fin n → ℝ) : eval y S = ∑ j, eval y (p j) ^ 2 := by simp [S]
  have hSnonneg (y : Fin n → ℝ) : 0 ≤ eval y S := by
    rw [hSeval]
    exact Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  have hSzero (y : Fin n → ℝ) : eval y S = 0 ↔ ∀ j, eval y (p j) = 0 := by
    rw [hSeval, Finset.sum_sq_eq_zero_iff]
    simp
  have hSx (a : I) : eval (x a) S = 0 := (hSzero _).mpr (hz a)
  let U (a : I) : Set (Fin n → ℝ) :=
    {y | (∀ j, eval y (p j) = 0) → y ≠ x a → eval (x a) q < eval y q}
  obtain ⟨r, hr, hU, hsep⟩ := exists_separated_radius x hx U hmin
  have hε (a : I) : ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t, 0 < t → t ≤ t₀ →
      ∀ y ∈ sphere (x a) r, 0 < eval y S + t * (eval y q - eval (x a) q) := by
    apply compact_penalty_positive (isCompact_sphere (x a) r)
      (continuous_eval S) ((continuous_eval q).sub continuous_const)
      (fun y _ ↦ hSnonneg y)
    intro y hy hzero
    have hneq : y ≠ x a := by
      intro heq
      have hh := mem_sphere.mp hy
      rw [heq, dist_self] at hh
      linarith
    exact sub_pos.mpr (hU a (sphere_subset_closedBall hy) ((hSzero y).mp hzero) hneq)
  choose ε hεpos hεbound using hε
  obtain ⟨t, ht, htε⟩ := exists_pos_lt_finite ε hεpos
  let P := S + C t * q
  have hSdeg : S.totalDegree ≤ 2 * d := by
    apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_pow (p j) 2).trans (Nat.mul_le_mul_left 2 (hp j))
  have hPdeg : P.totalDegree ≤ 2 * d - 1 + 1 := by
    have hh : P.totalDegree ≤ 2 * d :=
      (totalDegree_add _ _).trans (max_le hSdeg
        ((totalDegree_mul _ _).trans (by simpa using hq)))
    omega
  have hbd (a : I) (y : Fin n → ℝ) (hy : y ∈ sphere (x a) r) :
      eval (x a) P < eval y P := by
    have hh := hεbound a t ht (htε a).le y hy
    simp only [P, map_add, map_mul, eval_C, hSx, zero_add]
    nlinarith
  have hb := polynomial_boundary_minima_card_le P hPdeg x hr hsep hbd
  have hnat : 2 * d - 1 + 1 = 2 * d := by omega
  rwa [hnat] at hb

end HeadComplexity.PolynomialRootCount
