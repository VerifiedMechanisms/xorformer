import HeadComplexity.Polynomial.ThresholdDegree
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRightNhds

set_option linter.style.header false

/-!
# Positive-secant diagonal blow-ups

This file isolates the algebraic and analytic content of the positive-secant
blow-up.  The head and literal index types are arbitrary finite types.  An
oriented Boolean-cube family is supplied at the end as a specialization.
-/

namespace HeadComplexity

open Finset Filter Polynomial Set
open scoped BigOperators Topology

namespace PositiveSecant

variable {I J X : Type*} [Fintype I] [Fintype J]

/-- A tuple of points in standard simplices, one simplex for each head. -/
def IsSimplexPoint (theta : I → J → ℝ) : Prop :=
  (∀ h j, 0 ≤ theta h j) ∧ ∀ h, ∑ j, theta h j = 1

/-- Interior of the product of standard simplices. -/
def IsInteriorSimplexPoint (theta : I → J → ℝ) : Prop :=
  (∀ h j, 0 < theta h j) ∧ ∀ h, ∑ j, theta h j = 1

/-- The affine ray based at `theta` in direction `v`. -/
def rayPoint (theta v : I → J → ℝ) (t : ℝ) : I → J → ℝ :=
  fun h j ↦ theta h j + t * v h j

omit [Fintype I] [Fintype J] in
@[simp] theorem rayPoint_zero (theta v : I → J → ℝ) :
    rayPoint theta v 0 = theta := by
  ext h j
  simp [rayPoint]

/-- Tangent-cone feasibility at a product-simplex point. -/
def IsFeasibleDirection (theta v : I → J → ℝ) : Prop :=
  (∀ h, ∑ j, v h j = 0) ∧
    ∀ h j, theta h j = 0 → 0 ≤ v h j

/-- Sup-norm normalization used by the blow-up charts. -/
def IsNormalizedDirection (v : I → J → ℝ) : Prop :=
  ‖v‖ = 1

/-- Linear simplex factor associated with one head. -/
noncomputable def factor (L : I → J → X → ℝ)
    (theta : I → J → ℝ) (h : I) (x : X) : ℝ :=
  ∑ j, theta h j * L h j x

/-- Directional linear factor. -/
noncomputable def directionFactor (L : I → J → X → ℝ)
    (v : I → J → ℝ) (h : I) (x : X) : ℝ :=
  ∑ j, v h j * L h j x

/-- Product of the headwise simplex factors. -/
noncomputable def productScore (L : I → J → X → ℝ)
    (theta : I → J → ℝ) (x : X) : ℝ :=
  ∏ h, factor L theta h x

/-- Positive-secant pair gap, with the positive vertex first and the negative
vertex second. -/
noncomputable def pairGap (L : I → J → X → ℝ)
    (theta₀ theta₁ : I → J → ℝ) (p q : X) : ℝ :=
  productScore L theta₀ q * productScore L theta₁ p -
    productScore L theta₀ p * productScore L theta₁ q

omit [Fintype I] in
theorem factor_ray (L : I → J → X → ℝ)
    (theta v : I → J → ℝ) (t : ℝ) (h : I) (x : X) :
    factor L (rayPoint theta v t) h x =
      factor L theta h x + t * directionFactor L v h x := by
  classical
  simp only [factor, directionFactor, rayPoint, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum]
  simp only [mul_assoc]

/-- The polynomial in the secant parameter obtained from the perturbed
product. -/
noncomputable def productRayPolynomial (L : I → J → X → ℝ)
    (theta v : I → J → ℝ) (x : X) : ℝ[X] :=
  ∏ h, (C (factor L theta h x) +
    Polynomial.X * C (directionFactor L v h x))

/-- Polynomial pair gap along a ray. -/
noncomputable def pairGapPolynomial (L : I → J → X → ℝ)
    (theta v : I → J → ℝ) (p q : X) : ℝ[X] :=
  C (productScore L theta q) * productRayPolynomial L theta v p -
    C (productScore L theta p) * productRayPolynomial L theta v q

/-- Exact quotient after removing the universal factor `X`. -/
noncomputable def dividedPairGapPolynomial
    (L : I → J → X → ℝ)
    (theta v : I → J → ℝ) (p q : X) : ℝ[X] :=
  (pairGapPolynomial L theta v p q).divX

theorem eval_productRayPolynomial (L : I → J → X → ℝ)
    (theta v : I → J → ℝ) (x : X) (t : ℝ) :
    (productRayPolynomial L theta v x).eval t =
      productScore L (rayPoint theta v t) x := by
  classical
  simp only [productRayPolynomial, productScore, eval_prod, eval_add, eval_C,
    eval_mul, eval_X, factor_ray]

theorem eval_pairGapPolynomial (L : I → J → X → ℝ)
    (theta v : I → J → ℝ) (p q : X) (t : ℝ) :
    (pairGapPolynomial L theta v p q).eval t =
      pairGap L theta (rayPoint theta v t) p q := by
  simp [pairGapPolynomial, pairGap, eval_productRayPolynomial]

theorem pairGapPolynomial_coeff_zero
    (L : I → J → X → ℝ)
    (theta v : I → J → ℝ) (p q : X) :
    (pairGapPolynomial L theta v p q).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_pairGapPolynomial]
  simp [pairGap]
  ring

/-- Exact polynomial divisibility, not merely pointwise division away from
zero. -/
theorem pairGapPolynomial_eq_X_mul_divided
    (L : I → J → X → ℝ)
    (theta v : I → J → ℝ) (p q : X) :
    pairGapPolynomial L theta v p q =
      Polynomial.X * dividedPairGapPolynomial L theta v p q := by
  have hzero := pairGapPolynomial_coeff_zero L theta v p q
  simpa [dividedPairGapPolynomial, hzero] using
    (Polynomial.X_mul_divX_add (pairGapPolynomial L theta v p q)).symm

/-- The exact quotient identity at every scalar, including `t = 0`. -/
theorem pairGap_ray_eq_mul_eval_divided
    (L : I → J → X → ℝ)
    (theta v : I → J → ℝ) (p q : X) (t : ℝ) :
    pairGap L theta (rayPoint theta v t) p q =
      t * (dividedPairGapPolynomial L theta v p q).eval t := by
  rw [← eval_pairGapPolynomial]
  rw [pairGapPolynomial_eq_X_mul_divided]
  simp

theorem productRayPolynomial_natDegree_le
    (L : I → J → X → ℝ)
    (theta v : I → J → ℝ) (x : X) :
    (productRayPolynomial L theta v x).natDegree ≤ Fintype.card I := by
  classical
  unfold productRayPolynomial
  refine (Polynomial.natDegree_prod_le
    (fun h : I ↦ C (factor L theta h x) +
      Polynomial.X * C (directionFactor L v h x))
    (s := Finset.univ)).trans ?_
  calc
    (∑ h ∈ (Finset.univ : Finset I),
        (C (factor L theta h x) +
          Polynomial.X * C (directionFactor L v h x)).natDegree) ≤
        ∑ _h ∈ (Finset.univ : Finset I), 1 := by
      apply Finset.sum_le_sum
      intro h _
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · simp
      · exact Polynomial.natDegree_mul_le.trans (by simp)
    _ = Fintype.card I := by simp

theorem pairGapPolynomial_natDegree_le
    (L : I → J → X → ℝ)
    (theta v : I → J → ℝ) (p q : X) :
    (pairGapPolynomial L theta v p q).natDegree ≤ Fintype.card I := by
  unfold pairGapPolynomial
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (Polynomial.natDegree_C_mul_le _ _).trans
      (productRayPolynomial_natDegree_le L theta v p)
  · exact (Polynomial.natDegree_C_mul_le _ _).trans
      (productRayPolynomial_natDegree_le L theta v q)

/-- The divided pair gap has scalar degree at most one less than the number of
heads. -/
theorem dividedPairGapPolynomial_natDegree_le
    (L : I → J → X → ℝ)
    (theta v : I → J → ℝ) (p q : X) :
    (dividedPairGapPolynomial L theta v p q).natDegree ≤
      Fintype.card I - 1 := by
  rw [dividedPairGapPolynomial,
    Polynomial.natDegree_divX_eq_natDegree_tsub_one]
  exact Nat.sub_le_sub_right
    (pairGapPolynomial_natDegree_le L theta v p q) 1

/-! ## Simplex rays and normalization charts -/

omit [Fintype I] in
theorem interior_simplexPoint_isSimplexPoint {theta : I → J → ℝ}
    (htheta : IsInteriorSimplexPoint theta) : IsSimplexPoint theta :=
  ⟨fun h j ↦ (htheta.1 h j).le, htheta.2⟩

/-- Sup-norm one is exactly the finite union of signed coordinate charts. -/
theorem normalizedDirection_iff_charts [Nonempty I] [Nonempty J]
    (v : I → J → ℝ) :
    IsNormalizedDirection v ↔
      (∀ h j, |v h j| ≤ 1) ∧
        ∃ h j, v h j = 1 ∨ v h j = -1 := by
  constructor
  · intro hv
    change ‖v‖ = 1 at hv
    have hle : ∀ h j, |v h j| ≤ 1 := by
      intro h j
      rw [← Real.norm_eq_abs, ← hv]
      exact (norm_le_pi_norm (v h) j).trans (norm_le_pi_norm v h)
    refine ⟨hle, ?_⟩
    have hex : ∃ h j, |v h j| = 1 := by
      by_contra hnot
      push Not at hnot
      have hall : ∀ h j, ‖v h j‖ < 1 := by
        intro h j
        rw [Real.norm_eq_abs]
        exact lt_of_le_of_ne (hle h j) (hnot h j)
      have hvlt : ‖v‖ < 1 :=
        (pi_norm_lt_iff one_pos).2 fun h ↦
          (pi_norm_lt_iff one_pos).2 fun j ↦ hall h j
      rw [hv] at hvlt
      exact (lt_irrefl 1 hvlt)
    obtain ⟨h, j, hj⟩ := hex
    refine ⟨h, j, ?_⟩
    exact (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hj
  · rintro ⟨hle, hchart⟩
    have hvle : ‖v‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun h ↦
        (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j ↦ by
          simpa [Real.norm_eq_abs] using hle h j
    obtain ⟨h, j, hj | hj⟩ := hchart
    · apply le_antisymm hvle
      calc
        1 = ‖v h j‖ := by simp [hj]
        _ ≤ ‖v h‖ := norm_le_pi_norm (v h) j
        _ ≤ ‖v‖ := norm_le_pi_norm v h
    · apply le_antisymm hvle
      calc
        1 = ‖v h j‖ := by simp [hj]
        _ ≤ ‖v h‖ := norm_le_pi_norm (v h) j
        _ ≤ ‖v‖ := norm_le_pi_norm v h

omit [Fintype I] in
theorem rayPoint_block_sum {theta v : I → J → ℝ}
    (htheta : ∀ h, ∑ j, theta h j = 1)
    (hv : ∀ h, ∑ j, v h j = 0) (t : ℝ) (h : I) :
    ∑ j, rayPoint theta v t h j = 1 := by
  classical
  simp only [rayPoint, Finset.sum_add_distrib, ← Finset.mul_sum, htheta h, hv h]
  ring

omit [Fintype I] in
/-- A feasible tangent-cone direction remains in the product simplex for all
sufficiently small positive parameters. -/
theorem eventually_isSimplexPoint_ray [Finite I]
    {theta v : I → J → ℝ} (htheta : IsSimplexPoint theta)
    (hv : IsFeasibleDirection theta v) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      IsSimplexPoint (rayPoint theta v t) := by
  classical
  letI := Fintype.ofFinite I
  have hnonneg :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ h j, 0 ≤ rayPoint theta v t h j := by
    rw [Filter.eventually_all]
    intro h
    rw [Filter.eventually_all]
    intro j
    by_cases hz : theta h j = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [rayPoint, hz, zero_add]
      exact mul_nonneg ht.le (hv.2 h j hz)
    · have hpos : 0 < theta h j := lt_of_le_of_ne (htheta.1 h j) (Ne.symm hz)
      have hevent :
          ∀ᶠ t in nhds (0 : ℝ), 0 < theta h j + t * v h j :=
        ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0).eventually
          (lt_mem_nhds (by simpa using hpos))
      exact (hevent.filter_mono inf_le_left).mono fun t ht ↦ ht.le
  filter_upwards [hnonneg] with t ht
  exact ⟨ht, rayPoint_block_sum htheta.2 hv.1 t⟩

omit [Fintype I] in
/-- An interior base point remains interior for all sufficiently short
positive rays whose block sums vanish. -/
theorem eventually_isInteriorSimplexPoint_ray [Finite I]
    {theta v : I → J → ℝ}
    (htheta : IsInteriorSimplexPoint theta)
    (hv : ∀ h, ∑ j, v h j = 0) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      IsInteriorSimplexPoint (rayPoint theta v t) := by
  classical
  letI := Fintype.ofFinite I
  have hpos :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ h j, 0 < rayPoint theta v t h j := by
    rw [Filter.eventually_all]
    intro h
    rw [Filter.eventually_all]
    intro j
    have hevent :
        ∀ᶠ t in nhds (0 : ℝ), 0 < theta h j + t * v h j :=
      ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0).eventually
        (lt_mem_nhds (by simpa using htheta.1 h j))
    exact hevent.filter_mono inf_le_left
  filter_upwards [hpos] with t ht
  exact ⟨ht, rayPoint_block_sum htheta.2 hv t⟩

/-! ## Exact secant versus blow-up feasibility -/

/-- Strict positive-secant feasibility for two product-simplex endpoints. -/
def SecantFeasible (L : I → J → X → ℝ) (P N : Finset X) : Prop :=
  ∃ theta₀ theta₁ : I → J → ℝ,
    IsSimplexPoint theta₀ ∧ IsSimplexPoint theta₁ ∧
      ∀ p ∈ P, ∀ q ∈ N, 0 < pairGap L theta₀ theta₁ p q

/-- Normalized positive blow-up feasibility. -/
def BlowupFeasible (L : I → J → X → ℝ) (P N : Finset X) : Prop :=
  ∃ (theta v : I → J → ℝ) (t : ℝ),
    IsSimplexPoint theta ∧ IsFeasibleDirection theta v ∧
      IsNormalizedDirection v ∧ 0 ≤ t ∧
      IsSimplexPoint (rayPoint theta v t) ∧
      ∀ p ∈ P, ∀ q ∈ N,
        0 < (dividedPairGapPolynomial L theta v p q).eval t

/-- Interior-endpoint variant of positive-secant feasibility. -/
def InteriorSecantFeasible (L : I → J → X → ℝ)
    (P N : Finset X) : Prop :=
  ∃ theta₀ theta₁ : I → J → ℝ,
    IsInteriorSimplexPoint theta₀ ∧ IsInteriorSimplexPoint theta₁ ∧
      ∀ p ∈ P, ∀ q ∈ N, 0 < pairGap L theta₀ theta₁ p q

/-- Interior-endpoint variant of normalized blow-up feasibility. -/
def InteriorBlowupFeasible (L : I → J → X → ℝ)
    (P N : Finset X) : Prop :=
  ∃ (theta v : I → J → ℝ) (t : ℝ),
    IsInteriorSimplexPoint theta ∧ IsFeasibleDirection theta v ∧
      IsNormalizedDirection v ∧ 0 ≤ t ∧
      IsInteriorSimplexPoint (rayPoint theta v t) ∧
      ∀ p ∈ P, ∀ q ∈ N,
        0 < (dividedPairGapPolynomial L theta v p q).eval t

private theorem secantEndpoints_ne
    (L : I → J → X → ℝ) {P N : Finset X}
    (hP : P.Nonempty) (hN : N.Nonempty)
    {theta₀ theta₁ : I → J → ℝ}
    (hgap : ∀ p ∈ P, ∀ q ∈ N, 0 < pairGap L theta₀ theta₁ p q) :
    theta₁ ≠ theta₀ := by
  intro heq
  obtain ⟨p, hp⟩ := hP
  obtain ⟨q, hq⟩ := hN
  have hpos := hgap p hp q hq
  rw [heq] at hpos
  unfold pairGap at hpos
  nlinarith

/-- Every strict secant determines a nonzero normalized feasible direction. -/
theorem blowupFeasible_of_secantFeasible [Nonempty I] [Nonempty J]
    (L : I → J → X → ℝ) {P N : Finset X}
    (hP : P.Nonempty) (hN : N.Nonempty)
    (hsec : SecantFeasible L P N) : BlowupFeasible L P N := by
  classical
  rcases hsec with ⟨theta₀, theta₁, htheta₀, htheta₁, hgap⟩
  let d : I → J → ℝ := theta₁ - theta₀
  let t : ℝ := ‖d‖
  let v : I → J → ℝ := t⁻¹ • d
  have hne : theta₁ ≠ theta₀ :=
    secantEndpoints_ne L hP hN hgap
  have hdne : d ≠ 0 := by
    exact sub_ne_zero.mpr hne
  have ht : 0 < t := by
    exact norm_pos_iff.mpr hdne
  have hray : rayPoint theta₀ v t = theta₁ := by
    ext h j
    dsimp [rayPoint, v, d]
    field_simp [ht.ne']
    ring
  have hvfeasible : IsFeasibleDirection theta₀ v := by
    constructor
    · intro h
      change ∑ j, t⁻¹ * (theta₁ h j - theta₀ h j) = 0
      rw [← Finset.mul_sum, Finset.sum_sub_distrib,
        htheta₁.2 h, htheta₀.2 h]
      ring
    · intro h j hz
      simp only [v, d, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, hz, sub_zero]
      exact mul_nonneg (inv_nonneg.mpr ht.le) (htheta₁.1 h j)
  have hvnorm : IsNormalizedDirection v := by
    change ‖v‖ = 1
    dsimp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    change t⁻¹ * t = 1
    exact inv_mul_cancel₀ ht.ne'
  refine ⟨theta₀, v, t, htheta₀, hvfeasible, hvnorm, ht.le, ?_, ?_⟩
  · rwa [hray]
  · intro p hp q hq
    have hmul :
        0 < t * (dividedPairGapPolynomial L theta₀ v p q).eval t := by
      rw [← pairGap_ray_eq_mul_eval_divided, hray]
      exact hgap p hp q hq
    rcases (mul_pos_iff.mp hmul) with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge ht.le hneg.1).elim

/-- A strict point on the blown-up `t = 0` boundary opens into a genuine
positive secant. -/
theorem secantFeasible_of_blowupFeasible
    (L : I → J → X → ℝ) (P N : Finset X)
    (hblow : BlowupFeasible L P N) : SecantFeasible L P N := by
  classical
  rcases hblow with
    ⟨theta, v, t, htheta, hv, _hvnorm, ht, hthetaRay, hgap⟩
  by_cases htzero : t = 0
  · subst t
    have hsimplex := eventually_isSimplexPoint_ray htheta hv
    have hpositive :
        ∀ᶠ e in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ∀ p ∈ P, ∀ q ∈ N,
            0 < (dividedPairGapPolynomial L theta v p q).eval e := by
      rw [Filter.eventually_all_finset]
      intro p hp
      rw [Filter.eventually_all_finset]
      intro q hq
      have hevent :
          ∀ᶠ e in nhds (0 : ℝ),
            0 < (dividedPairGapPolynomial L theta v p q).eval e :=
        ((dividedPairGapPolynomial L theta v p q).continuous.tendsto 0).eventually
          (lt_mem_nhds (hgap p hp q hq))
      exact hevent.filter_mono inf_le_left
    have hinterval :
        ∀ᶠ e in nhdsWithin (0 : ℝ) (Set.Ioi 0), e ∈ Set.Ioo 0 1 :=
      Ioo_mem_nhdsGT zero_lt_one
    obtain ⟨e, hesimplex, hepositive, hepos, _heone⟩ :=
      (hsimplex.and (hpositive.and hinterval)).exists
    refine ⟨theta, rayPoint theta v e, htheta, hesimplex, ?_⟩
    intro p hp q hq
    rw [pairGap_ray_eq_mul_eval_divided]
    exact mul_pos hepos (hepositive p hp q hq)
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
    refine ⟨theta, rayPoint theta v t, htheta, hthetaRay, ?_⟩
    intro p hp q hq
    rw [pairGap_ray_eq_mul_eval_divided]
    exact mul_pos htpos (hgap p hp q hq)

/-- **Positive-secant blow-up equivalence.** The normalized blow-up is exact,
including at its new zero-parameter boundary. -/
theorem secantFeasible_iff_blowupFeasible [Nonempty I] [Nonempty J]
    (L : I → J → X → ℝ) {P N : Finset X}
    (hP : P.Nonempty) (hN : N.Nonempty) :
    SecantFeasible L P N ↔ BlowupFeasible L P N := by
  constructor
  · exact blowupFeasible_of_secantFeasible L hP hN
  · exact secantFeasible_of_blowupFeasible L P N

/-! ## Interior strictification -/

/-- Product of the simplex barycenters. -/
noncomputable def simplexBarycenter [Nonempty J] : I → J → ℝ :=
  fun _ _ ↦ (Fintype.card J : ℝ)⁻¹

omit [Fintype I] in
theorem simplexBarycenter_interior [Nonempty J] :
    IsInteriorSimplexPoint (simplexBarycenter : I → J → ℝ) := by
  classical
  have hcard : 0 < (Fintype.card J : ℝ) := by
    exact_mod_cast Fintype.card_pos
  constructor
  · intro h j
    exact inv_pos.mpr hcard
  · intro h
    simp only [simplexBarycenter, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard.ne'

/-- Move a simplex tuple toward the product barycenter. -/
noncomputable def interiorize [Nonempty J]
    (theta : I → J → ℝ) (delta : ℝ) : I → J → ℝ :=
  rayPoint theta (simplexBarycenter - theta) delta

omit [Fintype I] in
@[simp] theorem interiorize_zero [Nonempty J] (theta : I → J → ℝ) :
    interiorize theta 0 = theta := by
  simp [interiorize]

omit [Fintype I] in
theorem interiorize_isInteriorSimplexPoint [Nonempty J]
    {theta : I → J → ℝ} (htheta : IsSimplexPoint theta)
    {delta : ℝ} (hdelta : delta ∈ Set.Ioo 0 1) :
    IsInteriorSimplexPoint (interiorize theta delta) := by
  classical
  have hb := (simplexBarycenter_interior :
    IsInteriorSimplexPoint (simplexBarycenter : I → J → ℝ))
  constructor
  · intro h j
    have hfirst : 0 ≤ (1 - delta) * theta h j :=
      mul_nonneg (sub_nonneg.mpr hdelta.2.le) (htheta.1 h j)
    have hsecond : 0 < delta * simplexBarycenter h j :=
      mul_pos hdelta.1 (hb.1 h j)
    change 0 < theta h j + delta * (simplexBarycenter h j - theta h j)
    nlinarith
  · intro h
    unfold interiorize
    apply rayPoint_block_sum htheta.2
    intro g
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hb.2 g, htheta.2 g, sub_self]

theorem continuous_pairGap_interiorize [Nonempty J]
    (L : I → J → X → ℝ)
    (theta₀ theta₁ : I → J → ℝ) (p q : X) :
    Continuous fun delta ↦
      pairGap L (interiorize theta₀ delta) (interiorize theta₁ delta) p q := by
  classical
  unfold pairGap productScore factor interiorize rayPoint simplexBarycenter
  fun_prop

/-- Strict endpoint inequalities can always be preserved while moving both
endpoints into their simplex interiors. -/
theorem interiorSecantFeasible_iff_secantFeasible [Nonempty J]
    (L : I → J → X → ℝ) (P N : Finset X) :
    InteriorSecantFeasible L P N ↔ SecantFeasible L P N := by
  constructor
  · rintro ⟨theta₀, theta₁, htheta₀, htheta₁, hgap⟩
    exact ⟨theta₀, theta₁,
      interior_simplexPoint_isSimplexPoint htheta₀,
      interior_simplexPoint_isSimplexPoint htheta₁, hgap⟩
  · rintro ⟨theta₀, theta₁, htheta₀, htheta₁, hgap⟩
    have hpositive :
        ∀ᶠ delta in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ∀ p ∈ P, ∀ q ∈ N,
            0 < pairGap L (interiorize theta₀ delta)
              (interiorize theta₁ delta) p q := by
      rw [Filter.eventually_all_finset]
      intro p hp
      rw [Filter.eventually_all_finset]
      intro q hq
      have hevent :
          ∀ᶠ delta in nhds (0 : ℝ),
            0 < pairGap L (interiorize theta₀ delta)
              (interiorize theta₁ delta) p q :=
        ((continuous_pairGap_interiorize L theta₀ theta₁ p q).tendsto 0).eventually
          (lt_mem_nhds (by simpa using hgap p hp q hq))
      exact hevent.filter_mono inf_le_left
    have hinterval :
        ∀ᶠ delta in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          delta ∈ Set.Ioo 0 1 := Ioo_mem_nhdsGT zero_lt_one
    obtain ⟨delta, hpositive, hdelta⟩ := (hpositive.and hinterval).exists
    exact ⟨interiorize theta₀ delta, interiorize theta₁ delta,
      interiorize_isInteriorSimplexPoint htheta₀ hdelta,
      interiorize_isInteriorSimplexPoint htheta₁ hdelta,
      hpositive⟩

/-- Normalizing a secant between interior endpoints preserves both endpoint
interiority conditions. -/
theorem interiorBlowupFeasible_of_interiorSecantFeasible
    [Nonempty I] [Nonempty J]
    (L : I → J → X → ℝ) {P N : Finset X}
    (hP : P.Nonempty) (hN : N.Nonempty)
    (hsec : InteriorSecantFeasible L P N) :
    InteriorBlowupFeasible L P N := by
  classical
  rcases hsec with ⟨theta₀, theta₁, htheta₀, htheta₁, hgap⟩
  let d : I → J → ℝ := theta₁ - theta₀
  let t : ℝ := ‖d‖
  let v : I → J → ℝ := t⁻¹ • d
  have hne : theta₁ ≠ theta₀ := secantEndpoints_ne L hP hN hgap
  have hdne : d ≠ 0 := sub_ne_zero.mpr hne
  have ht : 0 < t := norm_pos_iff.mpr hdne
  have hray : rayPoint theta₀ v t = theta₁ := by
    ext h j
    dsimp [rayPoint, v, d]
    field_simp [ht.ne']
    ring
  have hvfeasible : IsFeasibleDirection theta₀ v := by
    constructor
    · intro h
      change ∑ j, t⁻¹ * (theta₁ h j - theta₀ h j) = 0
      rw [← Finset.mul_sum, Finset.sum_sub_distrib,
        htheta₁.2 h, htheta₀.2 h]
      ring
    · intro h j hz
      simp only [v, d, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, hz, sub_zero]
      exact mul_nonneg (inv_nonneg.mpr ht.le) (htheta₁.1 h j).le
  have hvnorm : IsNormalizedDirection v := by
    change ‖v‖ = 1
    dsimp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    change t⁻¹ * t = 1
    exact inv_mul_cancel₀ ht.ne'
  refine ⟨theta₀, v, t, htheta₀, hvfeasible, hvnorm, ht.le, ?_, ?_⟩
  · rwa [hray]
  · intro p hp q hq
    have hmul :
        0 < t * (dividedPairGapPolynomial L theta₀ v p q).eval t := by
      rw [← pairGap_ray_eq_mul_eval_divided, hray]
      exact hgap p hp q hq
    rcases (mul_pos_iff.mp hmul) with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge ht.le hneg.1).elim

/-- An interior strict point at the blow-up boundary opens along a sufficiently
short ray while staying in the interior. -/
theorem interiorSecantFeasible_of_interiorBlowupFeasible
    (L : I → J → X → ℝ) (P N : Finset X)
    (hblow : InteriorBlowupFeasible L P N) :
    InteriorSecantFeasible L P N := by
  classical
  rcases hblow with
    ⟨theta, v, t, htheta, hv, _hvnorm, ht, hthetaRay, hgap⟩
  by_cases htzero : t = 0
  · subst t
    have hinterior := eventually_isInteriorSimplexPoint_ray htheta hv.1
    have hpositive :
        ∀ᶠ e in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ∀ p ∈ P, ∀ q ∈ N,
            0 < (dividedPairGapPolynomial L theta v p q).eval e := by
      rw [Filter.eventually_all_finset]
      intro p hp
      rw [Filter.eventually_all_finset]
      intro q hq
      have hevent :
          ∀ᶠ e in nhds (0 : ℝ),
            0 < (dividedPairGapPolynomial L theta v p q).eval e :=
        ((dividedPairGapPolynomial L theta v p q).continuous.tendsto 0).eventually
          (lt_mem_nhds (hgap p hp q hq))
      exact hevent.filter_mono inf_le_left
    have hinterval :
        ∀ᶠ e in nhdsWithin (0 : ℝ) (Set.Ioi 0), e ∈ Set.Ioo 0 1 :=
      Ioo_mem_nhdsGT zero_lt_one
    obtain ⟨e, heinterior, hepositive, hepos, _heone⟩ :=
      (hinterior.and (hpositive.and hinterval)).exists
    refine ⟨theta, rayPoint theta v e, htheta, heinterior, ?_⟩
    intro p hp q hq
    rw [pairGap_ray_eq_mul_eval_divided]
    exact mul_pos hepos (hepositive p hp q hq)
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
    refine ⟨theta, rayPoint theta v t, htheta, hthetaRay, ?_⟩
    intro p hp q hq
    rw [pairGap_ray_eq_mul_eval_divided]
    exact mul_pos htpos (hgap p hp q hq)

/-- Interior version of the exact positive-secant blow-up equivalence. -/
theorem interiorSecantFeasible_iff_interiorBlowupFeasible
    [Nonempty I] [Nonempty J]
    (L : I → J → X → ℝ) {P N : Finset X}
    (hP : P.Nonempty) (hN : N.Nonempty) :
    InteriorSecantFeasible L P N ↔ InteriorBlowupFeasible L P N := by
  constructor
  · exact interiorBlowupFeasible_of_interiorSecantFeasible L hP hN
  · exact interiorSecantFeasible_of_interiorBlowupFeasible L P N

/-! ## Oriented Boolean-cube specialization -/

/-- The constant literal and the two orientations of a Boolean coordinate.
`none` is the constant literal, while `some i` is oriented by `sigma`. -/
def orientedLiteral {n : ℕ} (sigma : Bool) (j : Option (Fin n))
    (x : Fin n → Bool) : ℝ :=
  match j with
  | none => 1
  | some i => if sigma then boolToReal (x i) else 1 - boolToReal (x i)

/-- The oriented literal family for a fixed orientation of every head. -/
def orientedLiteralFamily {n H : ℕ} (sigma : Fin H → Bool) :
    Fin H → Option (Fin n) → (Fin n → Bool) → ℝ :=
  fun h ↦ orientedLiteral (sigma h)

/-- Positive truth-table vertices. -/
noncomputable def positiveInputs {n : ℕ}
    (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun x ↦ f x = true

/-- Negative truth-table vertices. -/
noncomputable def negativeInputs {n : ℕ}
    (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun x ↦ f x = false

@[simp] theorem mem_positiveInputs {n : ℕ}
    (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    x ∈ positiveInputs f ↔ f x = true := by
  classical
  simp [positiveInputs]

@[simp] theorem mem_negativeInputs {n : ℕ}
    (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    x ∈ negativeInputs f ↔ f x = false := by
  classical
  simp [negativeInputs]

theorem positiveInputs_nonempty_of_nonconstant {n : ℕ}
    {f : (Fin n → Bool) → Bool}
    (hf : ¬ ∀ x y, f x = f y) : (positiveInputs f).Nonempty := by
  classical
  by_contra hempty
  have hall : ∀ x, f x = false := by
    intro x
    cases hx : f x
    · rfl
    · exact (hempty ⟨x, (mem_positiveInputs f x).2 hx⟩).elim
  exact hf fun x y ↦ by rw [hall x, hall y]

theorem negativeInputs_nonempty_of_nonconstant {n : ℕ}
    {f : (Fin n → Bool) → Bool}
    (hf : ¬ ∀ x y, f x = f y) : (negativeInputs f).Nonempty := by
  classical
  by_contra hempty
  have hall : ∀ x, f x = true := by
    intro x
    cases hx : f x
    · exact (hempty ⟨x, (mem_negativeInputs f x).2 hx⟩).elim
    · rfl
  exact hf fun x y ↦ by rw [hall x, hall y]

/-- **Theorem 193, oriented Boolean-cube form.** For any nonconstant Boolean
function, a strict positive secant of oriented simplex products exists exactly
when its normalized diagonal blow-up is feasible. -/
theorem orientedSecantFeasible_iff_blowupFeasible {n H : ℕ}
    (hH : 0 < H) (f : (Fin n → Bool) → Bool)
    (hf : ¬ ∀ x y, f x = f y) (sigma : Fin H → Bool) :
    SecantFeasible (orientedLiteralFamily sigma)
        (positiveInputs f) (negativeInputs f) ↔
      BlowupFeasible (orientedLiteralFamily sigma)
        (positiveInputs f) (negativeInputs f) := by
  letI : Nonempty (Fin H) := Fin.pos_iff_nonempty.mp hH
  exact secantFeasible_iff_blowupFeasible
    (orientedLiteralFamily sigma)
    (positiveInputs_nonempty_of_nonconstant hf)
    (negativeInputs_nonempty_of_nonconstant hf)

/-- Interior-endpoint form of Theorem 193 for oriented Boolean literals. -/
theorem orientedInteriorSecantFeasible_iff_interiorBlowupFeasible
    {n H : ℕ} (hH : 0 < H) (f : (Fin n → Bool) → Bool)
    (hf : ¬ ∀ x y, f x = f y) (sigma : Fin H → Bool) :
    InteriorSecantFeasible (orientedLiteralFamily sigma)
        (positiveInputs f) (negativeInputs f) ↔
      InteriorBlowupFeasible (orientedLiteralFamily sigma)
        (positiveInputs f) (negativeInputs f) := by
  letI : Nonempty (Fin H) := Fin.pos_iff_nonempty.mp hH
  exact interiorSecantFeasible_iff_interiorBlowupFeasible
    (orientedLiteralFamily sigma)
    (positiveInputs_nonempty_of_nonconstant hf)
    (negativeInputs_nonempty_of_nonconstant hf)

/-- The exact divided pair-gap polynomial in Theorem 193 has scalar degree at
most `H - 1`. -/
theorem orientedDividedPairGapPolynomial_natDegree_le {n H : ℕ}
    (sigma : Fin H → Bool)
    (theta v : Fin H → Option (Fin n) → ℝ)
    (p q : Fin n → Bool) :
    (dividedPairGapPolynomial (orientedLiteralFamily sigma)
      theta v p q).natDegree ≤ H - 1 := by
  simpa using dividedPairGapPolynomial_natDegree_le
    (orientedLiteralFamily sigma) theta v p q

end PositiveSecant

end HeadComplexity
