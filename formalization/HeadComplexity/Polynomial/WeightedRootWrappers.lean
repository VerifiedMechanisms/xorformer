import HeadComplexity.Polynomial.WeightedDiagonalRootBound
import HeadComplexity.Polynomial.ConstrainedMinimaBound

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
Weighted analogues of the regular-root, generic-fiber, and strict-minimum
wrappers.  The analytic perturbation arguments are unchanged; each variable
has its own positive diagonal perturbation exponent.
-/

namespace HeadComplexity.PolynomialRootCount

open Filter MvPolynomial Set Metric
open scoped Topology

/-- Regular roots are counted by the product of the unequal diagonal degrees. -/
theorem weighted_regular_roots_card_le {n : ℕ} {ι : Type*} [Fintype ι]
    (w e : Fin n → ℕ) (hw : ∀ i, 0 < w i) (he : ∀ i, 0 < e i)
    (p : Fin n → MvPolynomial (Fin n) ℝ)
    (hp : ∀ i, ∀ m ∈ (p i).support, monomialWeight w m < e i * w i)
    (x : ι → Fin n → ℝ) (hx : Function.Injective x)
    (hroot : ∀ a i, eval (x a) (p i) = 0)
    (A : ι → (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hA : ∀ a, HasStrictFDerivAt (fun z i ↦ eval z (p i))
      (A a).toContinuousLinearMap (x a)) :
    Fintype.card ι ≤ ∏ i, e i := by
  let g : (Fin n → ℝ) → (Fin n → ℝ) := fun z i ↦ z i ^ (e i)
  let B (a : ι) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi (fun i ↦
      ((e i) • (x a i) ^ (e i - 1)) • ContinuousLinearMap.proj i)
  have hg (a : ι) : HasStrictFDerivAt g (B a) (x a) := by
    apply hasStrictFDerivAt_pi.mpr
    intro i
    simpa [B] using (hasStrictFDerivAt_apply (𝕜 := ℝ) i (x a)).pow (e i)
  have hzero (a : ι) : (fun i ↦ eval (x a) (p i)) = 0 := funext (hroot a)
  choose u hu hsol using fun a ↦ exists_zero_branch (A a) (B a) (hA a) (hg a) (hzero a)
  have hinj := eventually_injective_branches x hx u hu
  have hsols : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ a,
      (fun i ↦ eval (u a t) (p i)) + t • g (u a t) = 0 :=
    Filter.eventually_all.mpr hsol
  have hgood : ∀ᶠ t in 𝓝[≠] (0 : ℝ), Function.Injective (fun a ↦ u a t) ∧
      ∀ a, (fun i ↦ eval (u a t) (p i)) + t • g (u a t) = 0 :=
    (hinj.and hsols).filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 := self_mem_nhdsWithin
  obtain ⟨ε, hε, hεinj, hεsol⟩ := (Filter.Eventually.and hne hgood).exists
  apply weighted_perturbed_roots_card_le w e hw he p hp ε hε
    (fun a ↦ u a ε) hεinj
  intro a i
  have hi := congrFun (hεsol a) i
  simpa [g] using hi


/-- Generic fibers satisfy the same unequal-degree count. -/
theorem weighted_dense_polynomial_boundedFibers {n : ℕ}
    (w e : Fin n → ℕ) (hw : ∀ i, 0 < w i) (he : ∀ i, 0 < e i)
    (p : Fin n → MvPolynomial (Fin n) ℝ)
    (hp : ∀ i, ∀ m ∈ (p i).support, monomialWeight w m < e i * w i) :
    Dense {b : Fin n → ℝ | ∀ s : Finset (Fin n → ℝ),
      (∀ x ∈ s, ∀ i, eval x (p i) = b i) → s.card ≤ ∏ i, e i} := by
  classical
  apply (dense_polynomial_regularValues p).mono
  intro b hb s hs
  let q (i : Fin n) := p i - C (b i)
  have hq (i : Fin n) (m : Fin n →₀ ℕ) (hm : m ∈ (q i).support) :
      monomialWeight w m < e i * w i := by
    by_cases hm0 : m = 0
    · subst m
      simpa [monomialWeight] using Nat.mul_pos (he i) (hw i)
    · apply hp i m
      simpa only [q, mem_support_iff, coeff_sub, coeff_C_of_ne_zero hm0,
        sub_zero] using hm
  have hz (x : s) (i : Fin n) : eval (x : Fin n → ℝ) (q i) = 0 := by
    simp [q, hs x x.2 i]
  choose e' he' using fun x : s ↦ hb (x : Fin n → ℝ) (hs x x.2)
  have heq (x : s) : HasStrictFDerivAt (fun z i ↦ eval z (q i))
      (e' x).toContinuousLinearMap (x : Fin n → ℝ) := by
    convert (he' x).sub_const b using 1
    funext z i
    simp [q]
  simpa using weighted_regular_roots_card_le w e hw he q hq
    (fun x : s ↦ (x : Fin n → ℝ)) Subtype.val_injective hz e' heq

/-- Strict boundary minima are counted when their derivative polynomials have
strictly smaller weighted degrees than the chosen diagonal terms. -/
theorem weighted_polynomial_boundary_minima_card_le {n : ℕ}
    {I : Type*} [Fintype I]
    (w e : Fin n → ℕ) (hw : ∀ i, 0 < w i) (he : ∀ i, 0 < e i)
    (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ i, ∀ m ∈ (pderiv i p).support,
      monomialWeight w m < e i * w i)
    (x : I → Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ i j, i ≠ j → 2 * r < dist (x i) (x j))
    (hbd : ∀ i y, y ∈ sphere (x i) r → eval (x i) p < eval y p) :
    Fintype.card I ≤ ∏ i, e i := by
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
  obtain ⟨v, hv, hvgap⟩ := (weighted_dense_polynomial_boundedFibers w e hw he
    (fun i ↦ pderiv i p) hp).inter_nhds_nonempty hgaps
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

/-- Weighted-degree constraints and objective give a product bound for strict
constrained minima. The exponents need only dominate the derivative weights. -/
theorem weighted_constrained_minima_card_le {n : ℕ}
    {J I : Type*} [Finite J] [Fintype I] {D : ℕ}
    (w e : Fin n → ℕ) (hw : ∀ i, 0 < w i) (he : ∀ i, 0 < e i)
    (hcut : ∀ i, 2 * D - w i < e i * w i)
    (p : J → MvPolynomial (Fin n) ℝ)
    (hp : ∀ j, WeightedDegreeLE w (p j) D)
    (q : MvPolynomial (Fin n) ℝ) (hq : WeightedDegreeLE w q (2 * D))
    (x : I → Fin n → ℝ) (hx : Function.Injective x)
    (hz : ∀ a j, eval (x a) (p j) = 0)
    (hmin : ∀ a, ∀ᶠ y in 𝓝 (x a), (∀ j, eval y (p j) = 0) →
      y ≠ x a → eval (x a) q < eval y q) :
    Fintype.card I ≤ ∏ i, e i := by
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
  have hSdeg : WeightedDegreeLE w S (2 * D) := by
    apply weightedDegreeLE_sum
    intro j _
    simpa [Nat.mul_comm] using weightedDegreeLE_pow (hp j) 2
  have hPdeg : WeightedDegreeLE w P (2 * D) := by
    apply weightedDegreeLE_add hSdeg
    simpa using weightedDegreeLE_mul (weightedDegreeLE_C w t) hq
  have hgrad (i : Fin n) (m : Fin n →₀ ℕ)
      (hm : m ∈ (pderiv i P).support) :
      monomialWeight w m < e i * w i :=
    (weightedDegreeLE_pderiv hPdeg i m hm).trans_lt (hcut i)
  have hbd (a : I) (y : Fin n → ℝ) (hy : y ∈ sphere (x a) r) :
      eval (x a) P < eval y P := by
    have hh := hεbound a t ht (htε a).le y hy
    simp only [P, map_add, map_mul, eval_C, hSx, zero_add]
    nlinarith
  exact weighted_polynomial_boundary_minima_card_le w e hw he P hgrad x hr hsep hbd

end HeadComplexity.PolynomialRootCount
