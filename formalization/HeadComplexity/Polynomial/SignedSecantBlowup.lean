import HeadComplexity.Polynomial.PositiveSecantBlowup

set_option linter.style.header false

/-!
# Signed-secant diagonal blow-ups

This file proves the signed analogue of the positive pair-gap blow-up.  The
direction consists of a denominator direction together with the centered
mixture direction.  At the new `t = 0` boundary, an outward-pointing direction
is first moved to an interior simplex base and then opened into a short secant.
-/

namespace HeadComplexity

open Finset Filter Polynomial Set
open scoped BigOperators Topology

namespace SignedSecant

open PositiveSecant

variable {I J X : Type*} [Fintype I] [Fintype J]

/-- The signed score of two simplex-product endpoints at mixture `s`. -/
noncomputable def secantScore (L : I → J → X → ℝ)
    (theta₀ theta₁ : I → J → ℝ) (s : ℝ) (x : X) : ℝ :=
  s * productScore L theta₁ x - (1 - s) * productScore L theta₀ x

/-- The centered mixture scalar along a signed direction. -/
noncomputable def mixtureRay (a t : ℝ) : ℝ := (1 + t * a) / 2

/-- Sup normalization on the product of the denominator direction and the
one-dimensional mixture direction. -/
def IsNormalizedSignedDirection (v : I → J → ℝ) (a : ℝ) : Prop :=
  ‖(v, a)‖ = 1

/-- The signed secant score along the diagonal ray. -/
noncomputable def signedRayScore (L : I → J → X → ℝ)
    (theta v : I → J → ℝ) (a t : ℝ) (x : X) : ℝ :=
  secantScore L theta (rayPoint theta v t) (mixtureRay a t) x

/-- The exact quotient of the perturbed product by its universal `t` factor. -/
noncomputable def dividedProductRayPolynomial (L : I → J → X → ℝ)
    (theta v : I → J → ℝ) (x : X) : ℝ[X] :=
  (productRayPolynomial L theta v x - C (productScore L theta x)).divX

/-- Exact signed-score quotient polynomial.  This formula is the polynomial
version of
`(Q(theta+t*v)-Q(theta) + a*t*(Q(theta+t*v)+Q(theta))) / 2`. -/
noncomputable def dividedSignedRayPolynomial (L : I → J → X → ℝ)
    (theta v : I → J → ℝ) (a : ℝ) (x : X) : ℝ[X] :=
  C (2 : ℝ)⁻¹ *
    (dividedProductRayPolynomial L theta v x +
      C a * (productRayPolynomial L theta v x + C (productScore L theta x)))

theorem productRayPolynomial_sub_coeff_zero
    (L : I → J → X → ℝ) (theta v : I → J → ℝ) (x : X) :
    (productRayPolynomial L theta v x - C (productScore L theta x)).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  rw [eval_sub, eval_productRayPolynomial, eval_C, rayPoint_zero]
  exact sub_self _

theorem productRayPolynomial_sub_eq_X_mul_divided
    (L : I → J → X → ℝ) (theta v : I → J → ℝ) (x : X) :
    productRayPolynomial L theta v x - C (productScore L theta x) =
      Polynomial.X * dividedProductRayPolynomial L theta v x := by
  have hzero := productRayPolynomial_sub_coeff_zero L theta v x
  simpa [dividedProductRayPolynomial, hzero] using
    (Polynomial.X_mul_divX_add
      (productRayPolynomial L theta v x - C (productScore L theta x))).symm

theorem productScore_ray_sub_eq_mul_eval_divided
    (L : I → J → X → ℝ) (theta v : I → J → ℝ)
    (x : X) (t : ℝ) :
    productScore L (rayPoint theta v t) x - productScore L theta x =
      t * (dividedProductRayPolynomial L theta v x).eval t := by
  rw [← eval_productRayPolynomial]
  have heq := productRayPolynomial_sub_eq_X_mul_divided L theta v x
  have := congrArg (fun p : ℝ[X] ↦ p.eval t) heq
  simpa using this

/-- Exact signed quotient identity at every scalar, including `t = 0`. -/
theorem signedRayScore_eq_mul_eval_divided
    (L : I → J → X → ℝ) (theta v : I → J → ℝ)
    (a t : ℝ) (x : X) :
    signedRayScore L theta v a t x =
      t * (dividedSignedRayPolynomial L theta v a x).eval t := by
  rw [signedRayScore, secantScore, mixtureRay,
    dividedSignedRayPolynomial, eval_mul, eval_C, eval_add, eval_mul, eval_C,
    eval_add, eval_productRayPolynomial, eval_C]
  have hprod := productScore_ray_sub_eq_mul_eval_divided L theta v x t
  calc
    (1 + t * a) / 2 * productScore L (rayPoint theta v t) x -
        (1 - (1 + t * a) / 2) * productScore L theta x =
      (productScore L (rayPoint theta v t) x - productScore L theta x +
        t * a * (productScore L (rayPoint theta v t) x +
          productScore L theta x)) / 2 := by ring
    _ = t * (2⁻¹ * ((dividedProductRayPolynomial L theta v x).eval t +
        a * (productScore L (rayPoint theta v t) x +
          productScore L theta x))) := by rw [hprod]; ring

theorem dividedProductRayPolynomial_natDegree_le
    (L : I → J → X → ℝ) (theta v : I → J → ℝ) (x : X) :
    (dividedProductRayPolynomial L theta v x).natDegree ≤
      Fintype.card I - 1 := by
  rw [dividedProductRayPolynomial,
    Polynomial.natDegree_divX_eq_natDegree_tsub_one]
  apply Nat.sub_le_sub_right _ 1
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le (productRayPolynomial_natDegree_le L theta v x) (by simp))

/-- The signed quotient has scalar degree at most the number of heads. -/
theorem dividedSignedRayPolynomial_natDegree_le
    (L : I → J → X → ℝ) (theta v : I → J → ℝ)
    (a : ℝ) (x : X) :
    (dividedSignedRayPolynomial L theta v a x).natDegree ≤ Fintype.card I := by
  unfold dividedSignedRayPolynomial
  refine (Polynomial.natDegree_mul_le).trans ?_
  simp only [natDegree_C, zero_add]
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (dividedProductRayPolynomial_natDegree_le L theta v x).trans
      (Nat.sub_le _ _)
  · refine Polynomial.natDegree_mul_le.trans ?_
    simp only [natDegree_C, zero_add]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le (productRayPolynomial_natDegree_le L theta v x) (by simp))

/-! ## Normalization charts -/

/-- Product normalization is exactly the finite union of denominator-coordinate
and mixture-coordinate charts. -/
theorem normalizedSignedDirection_iff_charts [Nonempty I] [Nonempty J]
    (v : I → J → ℝ) (a : ℝ) :
    IsNormalizedSignedDirection v a ↔
      ( (∀ h j, |v h j| ≤ 1) ∧ |a| ≤ 1 ) ∧
        ((∃ h j, v h j = 1 ∨ v h j = -1) ∨ a = 1 ∨ a = -1) := by
  rw [IsNormalizedSignedDirection, Prod.norm_def]
  constructor
  · intro hmax
    have hvle : ‖v‖ ≤ 1 := by rw [← hmax]; exact le_max_left _ _
    have hale : |a| ≤ 1 := by
      rw [← Real.norm_eq_abs, ← hmax]
      exact le_max_right _ _
    have hvcoords : ∀ h j, |v h j| ≤ 1 := by
      intro h j
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (v h) j).trans (norm_le_pi_norm v h) |>.trans hvle
    refine ⟨⟨hvcoords, hale⟩, ?_⟩
    rcases max_choice ‖v‖ ‖a‖ with hvmax | hamax
    · left
      exact ((normalizedDirection_iff_charts v).1 (by
        rw [IsNormalizedDirection, ← hvmax, hmax])).2
    · right
      have haeq : |a| = 1 := by
        rw [← Real.norm_eq_abs, ← hamax, hmax]
      exact (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp haeq
  · rintro ⟨⟨hvcoords, hale⟩, hchart⟩
    have hvle : ‖v‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun h ↦
        (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j ↦ by
          simpa [Real.norm_eq_abs] using hvcoords h j
    apply le_antisymm (max_le hvle (by simpa [Real.norm_eq_abs] using hale))
    rcases hchart with hcoord | ha | ha
    · calc
        1 = ‖v‖ := (normalizedDirection_iff_charts v).2 ⟨hvcoords, hcoord⟩ |>.symm
        _ ≤ max ‖v‖ ‖a‖ := le_max_left _ _
    · simp [ha]
    · simp [ha]

/-! ## Signed secant and blow-up feasibility -/

/-- Strict signed feasibility for a pair of product-simplex endpoints. -/
def SignedSecantFeasible (L : I → J → X → ℝ) (y : X → ℝ)
    (U : Finset X) : Prop :=
  ∃ (theta₀ theta₁ : I → J → ℝ) (s : ℝ),
    IsSimplexPoint theta₀ ∧ IsSimplexPoint theta₁ ∧ s ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ x ∈ U, 0 < y x * secantScore L theta₀ theta₁ s x

/-- Normalized signed diagonal-blow-up feasibility.  Unlike the positive
pair-gap formulation, no tangent-cone face condition is imposed on `v`. -/
def SignedBlowupFeasible (L : I → J → X → ℝ) (y : X → ℝ)
    (U : Finset X) : Prop :=
  ∃ (theta v : I → J → ℝ) (a t : ℝ),
    IsSimplexPoint theta ∧ (∀ h, ∑ j, v h j = 0) ∧
      IsNormalizedSignedDirection v a ∧ t ∈ Set.Icc (0 : ℝ) 1 ∧
      IsSimplexPoint (rayPoint theta v t) ∧
      ∀ x ∈ U, 0 < y x * (dividedSignedRayPolynomial L theta v a x).eval t

/-- Interior-endpoint variant of signed secant feasibility. -/
def InteriorSignedSecantFeasible (L : I → J → X → ℝ)
    (y : X → ℝ) (U : Finset X) : Prop :=
  ∃ (theta₀ theta₁ : I → J → ℝ) (s : ℝ),
    IsInteriorSimplexPoint theta₀ ∧ IsInteriorSimplexPoint theta₁ ∧
      s ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ x ∈ U, 0 < y x * secantScore L theta₀ theta₁ s x

/-- Interior-endpoint variant of the normalized signed blow-up. -/
def InteriorSignedBlowupFeasible (L : I → J → X → ℝ)
    (y : X → ℝ) (U : Finset X) : Prop :=
  ∃ (theta v : I → J → ℝ) (a t : ℝ),
    IsInteriorSimplexPoint theta ∧ (∀ h, ∑ j, v h j = 0) ∧
      IsNormalizedSignedDirection v a ∧ t ∈ Set.Icc (0 : ℝ) 1 ∧
      IsInteriorSimplexPoint (rayPoint theta v t) ∧
      ∀ x ∈ U, 0 < y x * (dividedSignedRayPolynomial L theta v a x).eval t

omit [Fintype I] in
private theorem simplex_coordinate_le_one {theta : I → J → ℝ}
    (htheta : IsSimplexPoint theta) (h : I) (j : J) : theta h j ≤ 1 := by
  classical
  calc
    theta h j ≤ ∑ k, theta h k :=
      Finset.single_le_sum (fun k _ ↦ htheta.1 h k) (Finset.mem_univ j)
    _ = 1 := htheta.2 h

private theorem simplex_sub_norm_le_one [Nonempty I] [Nonempty J]
    {theta₀ theta₁ : I → J → ℝ}
    (htheta₀ : IsSimplexPoint theta₀) (htheta₁ : IsSimplexPoint theta₁) :
    ‖theta₁ - theta₀‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro h
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro j
  rw [Pi.sub_apply, Pi.sub_apply, Real.norm_eq_abs, abs_le]
  constructor
  · linarith [htheta₁.1 h j, simplex_coordinate_le_one htheta₀ h j]
  · linarith [htheta₀.1 h j, simplex_coordinate_le_one htheta₁ h j]

private theorem centered_mixture_abs_le_one {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : |2 * s - 1| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [hs.1, hs.2]

theorem mixtureRay_mem_Icc_of_normalized
    {v : I → J → ℝ} {a t : ℝ}
    (hnorm : IsNormalizedSignedDirection v a)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    mixtureRay a t ∈ Set.Icc (0 : ℝ) 1 := by
  have hale : |a| ≤ 1 := by
    rw [← Real.norm_eq_abs]
    calc
      ‖a‖ ≤ max ‖v‖ ‖a‖ := le_max_right _ _
      _ = 1 := hnorm
  have haBounds : -1 ≤ a ∧ a ≤ 1 := (abs_le.mp hale)
  constructor <;> unfold mixtureRay <;> nlinarith [ht.1, ht.2]

private theorem signedSecant_endpoints_not_centered
    (L : I → J → X → ℝ) (y : X → ℝ) {U : Finset X}
    (hU : U.Nonempty) {theta₀ theta₁ : I → J → ℝ} {s : ℝ}
    (hgap : ∀ x ∈ U, 0 < y x * secantScore L theta₀ theta₁ s x) :
    (theta₁ - theta₀, 2 * s - 1) ≠ 0 := by
  intro hzero
  have hd : theta₁ - theta₀ = 0 := congrArg Prod.fst hzero
  have hb : 2 * s - 1 = 0 := congrArg Prod.snd hzero
  have htheta : theta₁ = theta₀ := sub_eq_zero.mp hd
  have hs : s = 2⁻¹ := by linarith
  obtain ⟨x, hx⟩ := hU
  have hpos := hgap x hx
  rw [htheta, hs] at hpos
  unfold secantScore at hpos
  norm_num at hpos

/-- Every strict signed secant determines a normalized signed direction with
parameter in the compact interval `[0,1]`. -/
theorem signedBlowupFeasible_of_signedSecantFeasible
    [Nonempty I] [Nonempty J]
    (L : I → J → X → ℝ) (y : X → ℝ) {U : Finset X}
    (hU : U.Nonempty) (hsec : SignedSecantFeasible L y U) :
    SignedBlowupFeasible L y U := by
  classical
  rcases hsec with ⟨theta₀, theta₁, s, htheta₀, htheta₁, hs, hgap⟩
  let d : I → J → ℝ := theta₁ - theta₀
  let b : ℝ := 2 * s - 1
  let t : ℝ := ‖(d, b)‖
  let v : I → J → ℝ := t⁻¹ • d
  let a : ℝ := t⁻¹ * b
  have hpairne : (d, b) ≠ 0 := by
    exact signedSecant_endpoints_not_centered L y hU hgap
  have ht : 0 < t := norm_pos_iff.mpr hpairne
  have htupper : t ≤ 1 := by
    dsimp only [t]
    rw [Prod.norm_def]
    exact max_le
      (simplex_sub_norm_le_one htheta₀ htheta₁)
      (by simpa [b, Real.norm_eq_abs] using centered_mixture_abs_le_one hs)
  have hray : rayPoint theta₀ v t = theta₁ := by
    ext h j
    dsimp [rayPoint, v, d]
    field_simp [ht.ne']
    ring
  have hmix : mixtureRay a t = s := by
    dsimp [mixtureRay, a, b]
    field_simp [ht.ne']
    ring
  have hvsum : ∀ h, ∑ j, v h j = 0 := by
    intro h
    change ∑ j, t⁻¹ * (theta₁ h j - theta₀ h j) = 0
    rw [← Finset.mul_sum, Finset.sum_sub_distrib,
      htheta₁.2 h, htheta₀.2 h]
    ring
  have hnorm : IsNormalizedSignedDirection v a := by
    change ‖(v, a)‖ = 1
    have hscaled : (v, a) = t⁻¹ • (d, b) := by
      ext <;> rfl
    rw [hscaled, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    change t⁻¹ * t = 1
    exact inv_mul_cancel₀ ht.ne'
  refine ⟨theta₀, v, a, t, htheta₀, hvsum, hnorm, ⟨ht.le, htupper⟩,
    by rwa [hray], ?_⟩
  intro x hx
  have hmul :
      0 < t * (y x * (dividedSignedRayPolynomial L theta₀ v a x).eval t) := by
    have hactual : 0 < y x * signedRayScore L theta₀ v a t x := by
      simpa [signedRayScore, hray, hmix] using hgap x hx
    rw [signedRayScore_eq_mul_eval_divided] at hactual
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hactual
  rcases mul_pos_iff.mp hmul with hpos | hneg
  · exact hpos.2
  · exact (not_lt_of_ge ht.le hneg.1).elim

/-- First directional derivative of the product score. -/
noncomputable def productDirectionalDerivative
    (L : I → J → X → ℝ) (theta v : I → J → ℝ) (x : X) : ℝ :=
  by
    classical
    exact ∑ h, directionFactor L v h x *
      ∏ g ∈ (Finset.univ.erase h), factor L theta g x

theorem dividedProductRayPolynomial_eval_zero
    (L : I → J → X → ℝ) (theta v : I → J → ℝ) (x : X) :
    (dividedProductRayPolynomial L theta v x).eval 0 =
      productDirectionalDerivative L theta v x := by
  classical
  rw [← Polynomial.coeff_zero_eq_eval_zero, dividedProductRayPolynomial,
    Polynomial.coeff_divX]
  simp only [zero_add, Polynomial.coeff_sub, Polynomial.coeff_C,
    if_neg (by norm_num : (1 : ℕ) ≠ 0), sub_zero]
  have hderiv := congrArg (fun p : ℝ[X] ↦ p.eval 0)
    (Polynomial.derivative_prod_finset
      (s := (Finset.univ : Finset I))
      (f := fun h ↦ C (factor L theta h x) +
        Polynomial.X * C (directionFactor L v h x)))
  have hcoeff (p : ℝ[X]) : p.coeff 1 = p.derivative.eval 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    rw [Polynomial.coeff_derivative]
    norm_num
  rw [productRayPolynomial, hcoeff, hderiv, Polynomial.eval_finsetSum,
    productDirectionalDerivative]
  apply Finset.sum_congr rfl
  intro h _
  rw [Polynomial.eval_mul, Polynomial.eval_prod]
  simp only [Polynomial.derivative_add, Polynomial.derivative_C,
    Polynomial.derivative_mul, Polynomial.derivative_X,
    Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, zero_mul, add_zero, zero_add, one_mul, mul_zero]
  rw [mul_comm]

/-- Explicit value of the signed quotient on the exceptional divisor. -/
theorem dividedSignedRayPolynomial_eval_zero
    (L : I → J → X → ℝ) (theta v : I → J → ℝ)
    (a : ℝ) (x : X) :
    (dividedSignedRayPolynomial L theta v a x).eval 0 =
      2⁻¹ * (productDirectionalDerivative L theta v x +
        a * (productScore L theta x + productScore L theta x)) := by
  rw [dividedSignedRayPolynomial, eval_mul, eval_C, eval_add,
    eval_mul, eval_C, eval_add, eval_productRayPolynomial, eval_C,
    dividedProductRayPolynomial_eval_zero, rayPoint_zero]

/-- The boundary quotient varies continuously when its simplex base is moved
toward the barycenter. -/
theorem continuous_dividedSignedRay_eval_zero_interiorize [Nonempty J]
    (L : I → J → X → ℝ) (theta v : I → J → ℝ)
    (a : ℝ) (x : X) :
    Continuous fun delta ↦
      (dividedSignedRayPolynomial L (interiorize theta delta) v a x).eval 0 := by
  simp_rw [dividedSignedRayPolynomial_eval_zero]
  classical
  unfold productDirectionalDerivative productScore factor directionFactor
    interiorize rayPoint simplexBarycenter
  fun_prop

theorem continuous_secantScore_interiorize [Nonempty J]
    (L : I → J → X → ℝ) (theta₀ theta₁ : I → J → ℝ)
    (s : ℝ) (x : X) :
    Continuous fun delta ↦ secantScore L (interiorize theta₀ delta)
      (interiorize theta₁ delta) s x := by
  classical
  unfold secantScore productScore factor interiorize rayPoint simplexBarycenter
  fun_prop

/-- Even when the signed direction points out of a boundary face, a strict
point on the exceptional divisor opens into a genuine secant.  The base is
first moved into the simplex interior, then a sufficiently short positive ray
is chosen. -/
theorem interiorSignedSecantFeasible_of_signedBlowupFeasible [Nonempty J]
    (L : I → J → X → ℝ) (y : X → ℝ) (U : Finset X)
    (hblow : SignedBlowupFeasible L y U) :
    InteriorSignedSecantFeasible L y U := by
  classical
  rcases hblow with
    ⟨theta, v, a, t, htheta, hvsum, hnorm, ht, hthetaRay, hgap⟩
  by_cases htzero : t = 0
  · subst t
    have hbasePositive :
        ∀ᶠ delta in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ∀ x ∈ U, 0 < y x *
            (dividedSignedRayPolynomial L (interiorize theta delta) v a x).eval 0 := by
      rw [Filter.eventually_all_finset]
      intro x hx
      have hcont : Continuous fun delta ↦ y x *
          (dividedSignedRayPolynomial L (interiorize theta delta) v a x).eval 0 :=
        continuous_const.mul
          (continuous_dividedSignedRay_eval_zero_interiorize L theta v a x)
      have hevent := hcont.tendsto 0 |>.eventually
        (lt_mem_nhds (by simpa using hgap x hx))
      exact hevent.filter_mono inf_le_left
    have hdeltaInterval :
        ∀ᶠ delta in nhdsWithin (0 : ℝ) (Set.Ioi 0), delta ∈ Set.Ioo 0 1 :=
      Ioo_mem_nhdsGT zero_lt_one
    obtain ⟨delta, hbasePositive, hdelta⟩ :=
      (hbasePositive.and hdeltaInterval).exists
    let theta' := interiorize theta delta
    have htheta' : IsInteriorSimplexPoint theta' :=
      interiorize_isInteriorSimplexPoint htheta hdelta
    have hrayInterior := eventually_isInteriorSimplexPoint_ray htheta' hvsum
    have hrayPositive :
        ∀ᶠ e in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ∀ x ∈ U, 0 < y x *
            (dividedSignedRayPolynomial L theta' v a x).eval e := by
      rw [Filter.eventually_all_finset]
      intro x hx
      have hcont : Continuous fun e ↦ y x *
          (dividedSignedRayPolynomial L theta' v a x).eval e :=
        continuous_const.mul (dividedSignedRayPolynomial L theta' v a x).continuous
      have hevent := hcont.tendsto 0 |>.eventually
        (lt_mem_nhds (hbasePositive x hx))
      exact hevent.filter_mono inf_le_left
    have heInterval :
        ∀ᶠ e in nhdsWithin (0 : ℝ) (Set.Ioi 0), e ∈ Set.Ioo 0 1 :=
      Ioo_mem_nhdsGT zero_lt_one
    obtain ⟨e, heInterior, hePositive, he⟩ :=
      (hrayInterior.and (hrayPositive.and heInterval)).exists
    refine ⟨theta', rayPoint theta' v e, mixtureRay a e,
      htheta', heInterior, mixtureRay_mem_Icc_of_normalized hnorm ⟨he.1.le, he.2.le⟩, ?_⟩
    intro x hx
    have hmul : 0 < e * (y x *
        (dividedSignedRayPolynomial L theta' v a x).eval e) :=
      mul_pos he.1 (hePositive x hx)
    have hactual : signedRayScore L theta' v a e x =
        e * (dividedSignedRayPolynomial L theta' v a x).eval e :=
      signedRayScore_eq_mul_eval_divided L theta' v a e x
    change 0 < y x * signedRayScore L theta' v a e x
    rw [hactual]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
    have hclosed : ∀ x ∈ U, 0 < y x * secantScore L theta
        (rayPoint theta v t) (mixtureRay a t) x := by
      intro x hx
      have hmul : 0 < t * (y x *
          (dividedSignedRayPolynomial L theta v a x).eval t) :=
        mul_pos htpos (hgap x hx)
      change 0 < y x * signedRayScore L theta v a t x
      rw [signedRayScore_eq_mul_eval_divided]
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
    have hstrict :
        ∀ᶠ delta in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ∀ x ∈ U, 0 < y x *
            secantScore L (interiorize theta delta)
              (interiorize (rayPoint theta v t) delta) (mixtureRay a t) x := by
      rw [Filter.eventually_all_finset]
      intro x hx
      have hcont : Continuous fun delta ↦ y x *
          secantScore L (interiorize theta delta)
            (interiorize (rayPoint theta v t) delta) (mixtureRay a t) x :=
        continuous_const.mul
          (continuous_secantScore_interiorize L theta
            (rayPoint theta v t) (mixtureRay a t) x)
      have hevent := hcont.tendsto 0 |>.eventually
        (lt_mem_nhds (by simpa using hclosed x hx))
      exact hevent.filter_mono inf_le_left
    have hdeltaInterval :
        ∀ᶠ delta in nhdsWithin (0 : ℝ) (Set.Ioi 0), delta ∈ Set.Ioo 0 1 :=
      Ioo_mem_nhdsGT zero_lt_one
    obtain ⟨delta, hstrict, hdelta⟩ := (hstrict.and hdeltaInterval).exists
    exact ⟨interiorize theta delta,
      interiorize (rayPoint theta v t) delta, mixtureRay a t,
      interiorize_isInteriorSimplexPoint htheta hdelta,
      interiorize_isInteriorSimplexPoint hthetaRay hdelta,
      mixtureRay_mem_Icc_of_normalized hnorm ht, hstrict⟩

/-- Dropping endpoint interiority gives ordinary signed secant feasibility. -/
theorem signedSecantFeasible_of_signedBlowupFeasible [Nonempty J]
    (L : I → J → X → ℝ) (y : X → ℝ) (U : Finset X)
    (hblow : SignedBlowupFeasible L y U) : SignedSecantFeasible L y U := by
  rcases interiorSignedSecantFeasible_of_signedBlowupFeasible L y U hblow with
    ⟨theta₀, theta₁, s, htheta₀, htheta₁, hs, hgap⟩
  exact ⟨theta₀, theta₁, s,
    interior_simplexPoint_isSimplexPoint htheta₀,
    interior_simplexPoint_isSimplexPoint htheta₁, hs, hgap⟩

/-- **Theorem 194, generic analytic form.** Strict signed secants are exactly
the feasible points of their compact normalized diagonal blow-up. -/
theorem signedSecantFeasible_iff_signedBlowupFeasible
    [Nonempty I] [Nonempty J]
    (L : I → J → X → ℝ) (y : X → ℝ) {U : Finset X}
    (hU : U.Nonempty) :
    SignedSecantFeasible L y U ↔ SignedBlowupFeasible L y U := by
  constructor
  · exact signedBlowupFeasible_of_signedSecantFeasible L y hU
  · exact signedSecantFeasible_of_signedBlowupFeasible L y U

/-- Normalization preserves endpoint interiority when the original signed
secant has interior endpoints. -/
theorem interiorSignedBlowupFeasible_of_interiorSignedSecantFeasible
    [Nonempty I] [Nonempty J]
    (L : I → J → X → ℝ) (y : X → ℝ) {U : Finset X}
    (hU : U.Nonempty) (hsec : InteriorSignedSecantFeasible L y U) :
    InteriorSignedBlowupFeasible L y U := by
  classical
  rcases hsec with ⟨theta₀, theta₁, s, htheta₀, htheta₁, hs, hgap⟩
  let d : I → J → ℝ := theta₁ - theta₀
  let b : ℝ := 2 * s - 1
  let t : ℝ := ‖(d, b)‖
  let v : I → J → ℝ := t⁻¹ • d
  let a : ℝ := t⁻¹ * b
  have hpairne : (d, b) ≠ 0 :=
    signedSecant_endpoints_not_centered L y hU hgap
  have ht : 0 < t := norm_pos_iff.mpr hpairne
  have htheta₀' := interior_simplexPoint_isSimplexPoint htheta₀
  have htheta₁' := interior_simplexPoint_isSimplexPoint htheta₁
  have htupper : t ≤ 1 := by
    dsimp only [t]
    rw [Prod.norm_def]
    exact max_le
      (simplex_sub_norm_le_one htheta₀' htheta₁')
      (by simpa [b, Real.norm_eq_abs] using centered_mixture_abs_le_one hs)
  have hray : rayPoint theta₀ v t = theta₁ := by
    ext h j
    dsimp [rayPoint, v, d]
    field_simp [ht.ne']
    ring
  have hmix : mixtureRay a t = s := by
    dsimp [mixtureRay, a, b]
    field_simp [ht.ne']
    ring
  have hvsum : ∀ h, ∑ j, v h j = 0 := by
    intro h
    change ∑ j, t⁻¹ * (theta₁ h j - theta₀ h j) = 0
    rw [← Finset.mul_sum, Finset.sum_sub_distrib,
      htheta₁.2 h, htheta₀.2 h]
    ring
  have hnorm : IsNormalizedSignedDirection v a := by
    change ‖(v, a)‖ = 1
    have hscaled : (v, a) = t⁻¹ • (d, b) := by
      ext <;> rfl
    rw [hscaled, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    change t⁻¹ * t = 1
    exact inv_mul_cancel₀ ht.ne'
  refine ⟨theta₀, v, a, t, htheta₀, hvsum, hnorm, ⟨ht.le, htupper⟩,
    by rwa [hray], ?_⟩
  intro x hx
  have hactual : 0 < y x * signedRayScore L theta₀ v a t x := by
    simpa [signedRayScore, hray, hmix] using hgap x hx
  rw [signedRayScore_eq_mul_eval_divided] at hactual
  have hmul : 0 < t *
      (y x * (dividedSignedRayPolynomial L theta₀ v a x).eval t) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hactual
  rcases mul_pos_iff.mp hmul with hpos | hneg
  · exact hpos.2
  · exact (not_lt_of_ge ht.le hneg.1).elim

theorem interiorSignedSecantFeasible_of_interiorSignedBlowupFeasible
    [Nonempty J]
    (L : I → J → X → ℝ) (y : X → ℝ) (U : Finset X)
    (hblow : InteriorSignedBlowupFeasible L y U) :
    InteriorSignedSecantFeasible L y U := by
  rcases hblow with ⟨theta, v, a, t, htheta, hvsum, hnorm, ht, hthetaRay, hgap⟩
  apply interiorSignedSecantFeasible_of_signedBlowupFeasible L y U
  exact ⟨theta, v, a, t,
    interior_simplexPoint_isSimplexPoint htheta, hvsum, hnorm, ht,
    interior_simplexPoint_isSimplexPoint hthetaRay, hgap⟩

/-- Interior-endpoint form of the exact signed blow-up equivalence. -/
theorem interiorSignedSecantFeasible_iff_interiorSignedBlowupFeasible
    [Nonempty I] [Nonempty J]
    (L : I → J → X → ℝ) (y : X → ℝ) {U : Finset X}
    (hU : U.Nonempty) :
    InteriorSignedSecantFeasible L y U ↔
      InteriorSignedBlowupFeasible L y U := by
  constructor
  · exact interiorSignedBlowupFeasible_of_interiorSignedSecantFeasible L y hU
  · exact interiorSignedSecantFeasible_of_interiorSignedBlowupFeasible L y U

/-! ## Oriented Boolean-cube specialization -/

/-- Boolean labels as real signs. -/
def truthSign {n : ℕ} (f : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) : ℝ := if f x then 1 else -1

/-- **Theorem 194, oriented Boolean-cube form.** For every fixed head
orientation, strict signed secants are exactly normalized signed blow-ups. -/
theorem orientedSignedSecantFeasible_iff_signedBlowupFeasible
    {n H : ℕ} (hH : 0 < H) (f : (Fin n → Bool) → Bool)
    (sigma : Fin H → Bool) :
    SignedSecantFeasible (orientedLiteralFamily sigma) (truthSign f) Finset.univ ↔
      SignedBlowupFeasible (orientedLiteralFamily sigma) (truthSign f) Finset.univ := by
  letI : Nonempty (Fin H) := Fin.pos_iff_nonempty.mp hH
  exact signedSecantFeasible_iff_signedBlowupFeasible
    (orientedLiteralFamily sigma) (truthSign f) Finset.univ_nonempty

/-- Interior-endpoint form of Theorem 194 for oriented Boolean literals. -/
theorem orientedInteriorSignedSecantFeasible_iff_interiorSignedBlowupFeasible
    {n H : ℕ} (hH : 0 < H) (f : (Fin n → Bool) → Bool)
    (sigma : Fin H → Bool) :
    InteriorSignedSecantFeasible (orientedLiteralFamily sigma)
        (truthSign f) Finset.univ ↔
      InteriorSignedBlowupFeasible (orientedLiteralFamily sigma)
        (truthSign f) Finset.univ := by
  letI : Nonempty (Fin H) := Fin.pos_iff_nonempty.mp hH
  exact interiorSignedSecantFeasible_iff_interiorSignedBlowupFeasible
    (orientedLiteralFamily sigma) (truthSign f) Finset.univ_nonempty

/-- The exact signed quotient in Theorem 194 has scalar degree at most `H`. -/
theorem orientedDividedSignedRayPolynomial_natDegree_le {n H : ℕ}
    (sigma : Fin H → Bool)
    (theta v : Fin H → Option (Fin n) → ℝ) (a : ℝ)
    (x : Fin n → Bool) :
    (dividedSignedRayPolynomial (orientedLiteralFamily sigma)
      theta v a x).natDegree ≤ H := by
  simpa using dividedSignedRayPolynomial_natDegree_le
    (orientedLiteralFamily sigma) theta v a x

end SignedSecant

end HeadComplexity
