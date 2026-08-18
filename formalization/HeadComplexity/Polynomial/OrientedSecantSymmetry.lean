import HeadComplexity.Polynomial.SignedSecantBlowup
import HeadComplexity.Polynomial.UnivariateReduction

set_option linter.style.header false

/-!
# Head-permutation symmetry of oriented signed secants

The head indices in a simplex product are unordered.  This file makes that
symmetry explicit and uses it to replace the `2^H` Boolean orientation
branches by the `H + 1` possible numbers of positively oriented heads.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

namespace SignedSecant

open PositiveSecant

variable {I J X : Type*} [Fintype I] [Fintype J]

/-- Reindex a literal family by a permutation of its head indices. -/
def permuteHeadFamily (e : Equiv.Perm I) (L : I → J → X → ℝ) :
    I → J → X → ℝ :=
  fun h ↦ L (e h)

/-- Reindex a product-simplex point or tangent direction by a head
permutation. -/
def permuteHeadPoint (e : Equiv.Perm I) (theta : I → J → ℝ) :
    I → J → ℝ :=
  fun h ↦ theta (e h)

omit [Fintype I] [Fintype J] in
@[simp] theorem permuteHeadFamily_symm_apply (e : Equiv.Perm I)
    (L : I → J → X → ℝ) :
    permuteHeadFamily e.symm (permuteHeadFamily e L) = L := by
  ext h j x
  simp [permuteHeadFamily]

omit [Fintype I] [Fintype J] in
@[simp] theorem permuteHeadFamily_apply_symm (e : Equiv.Perm I)
    (L : I → J → X → ℝ) :
    permuteHeadFamily e (permuteHeadFamily e.symm L) = L := by
  ext h j x
  simp [permuteHeadFamily]

omit [Fintype I] [Fintype J] in
@[simp] theorem permuteHeadPoint_symm_apply (e : Equiv.Perm I)
    (theta : I → J → ℝ) :
    permuteHeadPoint e.symm (permuteHeadPoint e theta) = theta := by
  ext h j
  simp [permuteHeadPoint]

omit [Fintype I] [Fintype J] in
@[simp] theorem permuteHeadPoint_apply_symm (e : Equiv.Perm I)
    (theta : I → J → ℝ) :
    permuteHeadPoint e (permuteHeadPoint e.symm theta) = theta := by
  ext h j
  simp [permuteHeadPoint]

omit [Fintype I] in
theorem isSimplexPoint_permuteHeadPoint_iff (e : Equiv.Perm I)
    (theta : I → J → ℝ) :
    IsSimplexPoint (permuteHeadPoint e theta) ↔ IsSimplexPoint theta := by
  constructor
  · rintro ⟨hnonneg, hsum⟩
    refine ⟨fun h j ↦ ?_, fun h ↦ ?_⟩
    · simpa [permuteHeadPoint] using hnonneg (e.symm h) j
    · simpa [permuteHeadPoint] using hsum (e.symm h)
  · rintro ⟨hnonneg, hsum⟩
    exact ⟨fun h j ↦ hnonneg (e h) j,
      fun h ↦ by simpa [permuteHeadPoint] using hsum (e h)⟩

omit [Fintype I] in
theorem isInteriorSimplexPoint_permuteHeadPoint_iff (e : Equiv.Perm I)
    (theta : I → J → ℝ) :
    IsInteriorSimplexPoint (permuteHeadPoint e theta) ↔
      IsInteriorSimplexPoint theta := by
  constructor
  · rintro ⟨hpos, hsum⟩
    refine ⟨fun h j ↦ ?_, fun h ↦ ?_⟩
    · simpa [permuteHeadPoint] using hpos (e.symm h) j
    · simpa [permuteHeadPoint] using hsum (e.symm h)
  · rintro ⟨hpos, hsum⟩
    exact ⟨fun h j ↦ hpos (e h) j,
      fun h ↦ by simpa [permuteHeadPoint] using hsum (e h)⟩

omit [Fintype I] [Fintype J] in
@[simp] theorem rayPoint_permuteHeadPoint (e : Equiv.Perm I)
    (theta v : I → J → ℝ) (t : ℝ) :
    rayPoint (permuteHeadPoint e theta) (permuteHeadPoint e v) t =
      permuteHeadPoint e (rayPoint theta v t) := by
  rfl

omit [Fintype I] in
@[simp] theorem factor_permuteHeads (e : Equiv.Perm I)
    (L : I → J → X → ℝ) (theta : I → J → ℝ)
    (h : I) (x : X) :
    factor (permuteHeadFamily e L) (permuteHeadPoint e theta) h x =
      factor L theta (e h) x := by
  rfl

omit [Fintype I] in
@[simp] theorem directionFactor_permuteHeads (e : Equiv.Perm I)
    (L : I → J → X → ℝ) (v : I → J → ℝ) (h : I) (x : X) :
    directionFactor (permuteHeadFamily e L) (permuteHeadPoint e v) h x =
      directionFactor L v (e h) x := by
  rfl

@[simp] theorem productScore_permuteHeads (e : Equiv.Perm I)
    (L : I → J → X → ℝ) (theta : I → J → ℝ) (x : X) :
    productScore (permuteHeadFamily e L) (permuteHeadPoint e theta) x =
      productScore L theta x := by
  classical
  unfold productScore
  simpa only [factor_permuteHeads] using
    Equiv.prod_comp e (fun h ↦ factor L theta h x)

@[simp] theorem productRayPolynomial_permuteHeads (e : Equiv.Perm I)
    (L : I → J → X → ℝ) (theta v : I → J → ℝ) (x : X) :
    productRayPolynomial (permuteHeadFamily e L)
        (permuteHeadPoint e theta) (permuteHeadPoint e v) x =
      productRayPolynomial L theta v x := by
  classical
  unfold productRayPolynomial
  simpa only [factor_permuteHeads, directionFactor_permuteHeads] using
    Equiv.prod_comp e (fun h ↦
      Polynomial.C (factor L theta h x) +
        Polynomial.X * Polynomial.C (directionFactor L v h x))

@[simp] theorem dividedProductRayPolynomial_permuteHeads (e : Equiv.Perm I)
    (L : I → J → X → ℝ) (theta v : I → J → ℝ) (x : X) :
    dividedProductRayPolynomial (permuteHeadFamily e L)
        (permuteHeadPoint e theta) (permuteHeadPoint e v) x =
      dividedProductRayPolynomial L theta v x := by
  simp [dividedProductRayPolynomial]

@[simp] theorem dividedSignedRayPolynomial_permuteHeads (e : Equiv.Perm I)
    (L : I → J → X → ℝ) (theta v : I → J → ℝ) (a : ℝ) (x : X) :
    dividedSignedRayPolynomial (permuteHeadFamily e L)
        (permuteHeadPoint e theta) (permuteHeadPoint e v) a x =
      dividedSignedRayPolynomial L theta v a x := by
  simp [dividedSignedRayPolynomial]

@[simp] theorem secantScore_permuteHeads (e : Equiv.Perm I)
    (L : I → J → X → ℝ) (theta₀ theta₁ : I → J → ℝ)
    (s : ℝ) (x : X) :
    secantScore (permuteHeadFamily e L)
        (permuteHeadPoint e theta₀) (permuteHeadPoint e theta₁) s x =
      secantScore L theta₀ theta₁ s x := by
  simp [secantScore]

/-- Signed secant feasibility is invariant under a permutation of the head
indices. -/
theorem signedSecantFeasible_permuteHeads_iff (e : Equiv.Perm I)
    (L : I → J → X → ℝ) (y : X → ℝ) (U : Finset X) :
    SignedSecantFeasible (permuteHeadFamily e L) y U ↔
      SignedSecantFeasible L y U := by
  constructor
  · rintro ⟨theta₀, theta₁, s, htheta₀, htheta₁, hs, hgap⟩
    refine ⟨permuteHeadPoint e.symm theta₀,
      permuteHeadPoint e.symm theta₁, s, ?_, ?_, hs, ?_⟩
    · exact (isSimplexPoint_permuteHeadPoint_iff e.symm theta₀).2 htheta₀
    · exact (isSimplexPoint_permuteHeadPoint_iff e.symm theta₁).2 htheta₁
    · intro x hx
      rw [← secantScore_permuteHeads e L
        (permuteHeadPoint e.symm theta₀) (permuteHeadPoint e.symm theta₁)]
      simpa only [permuteHeadPoint_apply_symm] using hgap x hx
  · rintro ⟨theta₀, theta₁, s, htheta₀, htheta₁, hs, hgap⟩
    refine ⟨permuteHeadPoint e theta₀, permuteHeadPoint e theta₁,
      s, ?_, ?_, hs, ?_⟩
    · exact (isSimplexPoint_permuteHeadPoint_iff e theta₀).2 htheta₀
    · exact (isSimplexPoint_permuteHeadPoint_iff e theta₁).2 htheta₁
    · intro x hx
      simpa using hgap x hx

/-- Signed blow-up feasibility inherits head-permutation invariance from the
exact signed-secant/blow-up equivalence. -/
theorem signedBlowupFeasible_permuteHeads_iff [Nonempty I] [Nonempty J]
    (e : Equiv.Perm I) (L : I → J → X → ℝ) (y : X → ℝ)
    {U : Finset X} (hU : U.Nonempty) :
    SignedBlowupFeasible (permuteHeadFamily e L) y U ↔
      SignedBlowupFeasible L y U := by
  rw [← signedSecantFeasible_iff_signedBlowupFeasible
      (permuteHeadFamily e L) y hU,
    signedSecantFeasible_permuteHeads_iff,
    signedSecantFeasible_iff_signedBlowupFeasible L y hU]

/-! ## Finite normalization charts -/

/-- The finite coordinate charts of the signed sup normalization.  A Boolean
tag chooses the `+1` face when true and the `-1` face when false. -/
inductive SignedNormalizationChart (I J : Type*) where
  | denominator (h : I) (j : J) (positive : Bool)
  | mixture (positive : Bool)
  deriving DecidableEq, Fintype

/-- Reindex the head coordinate named by a normalization chart. -/
def permuteSignedNormalizationChart (e : Equiv.Perm I) :
    SignedNormalizationChart I J → SignedNormalizationChart I J
  | .denominator h j positive => .denominator (e h) j positive
  | .mixture positive => .mixture positive

omit [Fintype I] [Fintype J] in
@[simp] theorem permuteSignedNormalizationChart_symm_apply
    (e : Equiv.Perm I) (c : SignedNormalizationChart I J) :
    permuteSignedNormalizationChart e.symm
      (permuteSignedNormalizationChart e c) = c := by
  cases c <;> simp [permuteSignedNormalizationChart]

omit [Fintype I] [Fintype J] in
@[simp] theorem permuteSignedNormalizationChart_apply_symm
    (e : Equiv.Perm I) (c : SignedNormalizationChart I J) :
    permuteSignedNormalizationChart e
      (permuteSignedNormalizationChart e.symm c) = c := by
  cases c <;> simp [permuteSignedNormalizationChart]

/-- Coordinate bounds shared by every signed normalization chart. -/
def SignedDirectionBounds (v : I → J → ℝ) (a : ℝ) : Prop :=
  (∀ h j, |v h j| ≤ 1) ∧ |a| ≤ 1

omit [Fintype I] [Fintype J] in
theorem signedDirectionBounds_permuteHeadPoint_iff (e : Equiv.Perm I)
    (v : I → J → ℝ) (a : ℝ) :
    SignedDirectionBounds (permuteHeadPoint e v) a ↔
      SignedDirectionBounds v a := by
  constructor
  · rintro ⟨hv, ha⟩
    exact ⟨fun h j ↦ by simpa [permuteHeadPoint] using hv (e.symm h) j, ha⟩
  · rintro ⟨hv, ha⟩
    exact ⟨fun h j ↦ hv (e h) j, ha⟩

/-- The coordinate equality selected by one normalization chart. -/
def SatisfiesSignedNormalizationChart (v : I → J → ℝ) (a : ℝ) :
    SignedNormalizationChart I J → Prop
  | .denominator h j true => v h j = 1
  | .denominator h j false => v h j = -1
  | .mixture true => a = 1
  | .mixture false => a = -1

omit [Fintype I] [Fintype J] in
theorem satisfiesSignedNormalizationChart_permuteHeadPoint_iff
    (e : Equiv.Perm I) (v : I → J → ℝ) (a : ℝ)
    (c : SignedNormalizationChart I J) :
    SatisfiesSignedNormalizationChart (permuteHeadPoint e v) a c ↔
      SatisfiesSignedNormalizationChart v a
        (permuteSignedNormalizationChart e c) := by
  cases c with
  | denominator h j positive => cases positive <;> rfl
  | mixture positive => cases positive <;> rfl

/-- Sup normalization is a finite union of explicitly indexed coordinate
charts. -/
theorem normalizedSignedDirection_iff_exists_chart [Nonempty I] [Nonempty J]
    (v : I → J → ℝ) (a : ℝ) :
    IsNormalizedSignedDirection v a ↔
      SignedDirectionBounds v a ∧
        ∃ c : SignedNormalizationChart I J,
          SatisfiesSignedNormalizationChart v a c := by
  rw [normalizedSignedDirection_iff_charts]
  constructor
  · rintro ⟨hbounds, hsaturated⟩
    refine ⟨hbounds, ?_⟩
    rcases hsaturated with ⟨h, j, hpos | hneg⟩ | hpos | hneg
    · exact ⟨.denominator h j true, hpos⟩
    · exact ⟨.denominator h j false, hneg⟩
    · exact ⟨.mixture true, hpos⟩
    · exact ⟨.mixture false, hneg⟩
  · rintro ⟨hbounds, c, hc⟩
    refine ⟨hbounds, ?_⟩
    cases c with
    | denominator h j positive =>
        left
        refine ⟨h, j, ?_⟩
        cases positive
        · exact Or.inr hc
        · exact Or.inl hc
    | mixture positive =>
        right
        cases positive
        · exact Or.inr hc
        · exact Or.inl hc

/-- Signed blow-up feasibility restricted to one explicit normalization
chart. -/
def SignedBlowupChartFeasible (L : I → J → X → ℝ) (y : X → ℝ)
    (U : Finset X) (c : SignedNormalizationChart I J) : Prop :=
  ∃ (theta v : I → J → ℝ) (a t : ℝ),
    IsSimplexPoint theta ∧ (∀ h, ∑ j, v h j = 0) ∧
      SignedDirectionBounds v a ∧ SatisfiesSignedNormalizationChart v a c ∧
      t ∈ Set.Icc (0 : ℝ) 1 ∧ IsSimplexPoint (rayPoint theta v t) ∧
      ∀ x ∈ U, 0 < y x * (dividedSignedRayPolynomial L theta v a x).eval t

private theorem signedBlowupChartFeasible_permuteHeads_of
    (e : Equiv.Perm I) (L : I → J → X → ℝ) (y : X → ℝ)
    (U : Finset X) (c : SignedNormalizationChart I J)
    (hfeasible : SignedBlowupChartFeasible L y U
      (permuteSignedNormalizationChart e c)) :
    SignedBlowupChartFeasible (permuteHeadFamily e L) y U c := by
  rcases hfeasible with
    ⟨theta, v, a, t, htheta, hvsum, hbounds, hchart, ht, hray, hgap⟩
  refine ⟨permuteHeadPoint e theta, permuteHeadPoint e v, a, t,
    (isSimplexPoint_permuteHeadPoint_iff e theta).2 htheta, ?_,
    (signedDirectionBounds_permuteHeadPoint_iff e v a).2 hbounds,
    (satisfiesSignedNormalizationChart_permuteHeadPoint_iff e v a c).2 hchart,
    ht, ?_, ?_⟩
  · intro h
    exact hvsum (e h)
  · rw [rayPoint_permuteHeadPoint]
    exact (isSimplexPoint_permuteHeadPoint_iff e
      (rayPoint theta v t)).2 hray
  · intro x hx
    simpa only [dividedSignedRayPolynomial_permuteHeads] using hgap x hx

/-- Feasibility in an individual normalization chart is equivariant under
head permutations. -/
theorem signedBlowupChartFeasible_permuteHeads_iff
    (e : Equiv.Perm I) (L : I → J → X → ℝ) (y : X → ℝ)
    (U : Finset X) (c : SignedNormalizationChart I J) :
    SignedBlowupChartFeasible (permuteHeadFamily e L) y U c ↔
      SignedBlowupChartFeasible L y U
        (permuteSignedNormalizationChart e c) := by
  constructor
  · intro hfeasible
    have h := signedBlowupChartFeasible_permuteHeads_of e.symm
      (permuteHeadFamily e L) y U (permuteSignedNormalizationChart e c)
      (by simpa only [permuteSignedNormalizationChart_symm_apply] using hfeasible)
    simpa only [permuteHeadFamily_symm_apply] using h
  · exact signedBlowupChartFeasible_permuteHeads_of e L y U c

/-- A signed blow-up is feasible exactly when one member of its finite chart
family is feasible. -/
theorem signedBlowupFeasible_iff_exists_chart [Nonempty I] [Nonempty J]
    (L : I → J → X → ℝ) (y : X → ℝ) (U : Finset X) :
    SignedBlowupFeasible L y U ↔
      ∃ c : SignedNormalizationChart I J,
        SignedBlowupChartFeasible L y U c := by
  constructor
  · rintro ⟨theta, v, a, t, htheta, hvsum, hnorm, ht, hray, hgap⟩
    obtain ⟨hbounds, c, hc⟩ :=
      (normalizedSignedDirection_iff_exists_chart v a).1 hnorm
    exact ⟨c, theta, v, a, t, htheta, hvsum, hbounds, hc, ht, hray, hgap⟩
  · rintro ⟨c, theta, v, a, t, htheta, hvsum, hbounds, hc, ht, hray, hgap⟩
    exact ⟨theta, v, a, t, htheta, hvsum,
      (normalizedSignedDirection_iff_exists_chart v a).2 ⟨hbounds, c, hc⟩,
      ht, hray, hgap⟩

/-- Infeasibility of a signed blow-up is exactly infeasibility in every one
of its finitely many normalization charts. -/
theorem not_signedBlowupFeasible_iff_all_charts_infeasible
    [Nonempty I] [Nonempty J]
    (L : I → J → X → ℝ) (y : X → ℝ) (U : Finset X) :
    (¬ SignedBlowupFeasible L y U) ↔
      ∀ c : SignedNormalizationChart I J,
        ¬ SignedBlowupChartFeasible L y U c := by
  rw [signedBlowupFeasible_iff_exists_chart]
  simp only [not_exists]

/-! ## Boolean orientations modulo head permutations -/

/-- Heads carrying the positive Boolean-literal orientation. -/
def trueHeads {H : ℕ} (sigma : Fin H → Bool) : Finset (Fin H) :=
  Finset.univ.filter fun h ↦ sigma h = true

@[simp] theorem mem_trueHeads {H : ℕ} (sigma : Fin H → Bool) (h : Fin H) :
    h ∈ trueHeads sigma ↔ sigma h = true := by
  simp [trueHeads]

/-- Number of positively oriented heads. -/
def orientationTrueCount {H : ℕ} (sigma : Fin H → Bool) : ℕ :=
  (trueHeads sigma).card

/-- Canonical orientation with its first `k` heads positive.  The bound
`k < H + 1` carried by `Fin (H + 1)` says exactly that `k ≤ H`. -/
def canonicalOrientation (H : ℕ) (k : Fin (H + 1)) : Fin H → Bool :=
  fun h ↦ decide (h.val < k.val)

theorem orientationTrueCount_le {H : ℕ} (sigma : Fin H → Bool) :
    orientationTrueCount sigma ≤ H := by
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin H)

/-- The count itself, packaged as one of the `H + 1` canonical branches. -/
def orientationCountIndex {H : ℕ} (sigma : Fin H → Bool) : Fin (H + 1) :=
  ⟨orientationTrueCount sigma, Nat.lt_succ_iff.mpr (orientationTrueCount_le sigma)⟩

@[simp] theorem orientationTrueCount_canonicalOrientation (H : ℕ)
    (k : Fin (H + 1)) :
    orientationTrueCount (canonicalOrientation H k) = k.val := by
  simp [orientationTrueCount, trueHeads, canonicalOrientation,
    Fin.card_filter_val_lt, Nat.min_eq_right (Nat.lt_succ_iff.mp k.isLt)]

/-- Two orientations with the same number of positive heads differ only by a
head permutation. -/
theorem exists_headPerm_orientation_eq_of_trueCount_eq {H : ℕ}
    {sigma tau : Fin H → Bool}
    (hcount : orientationTrueCount sigma = orientationTrueCount tau) :
    ∃ e : Equiv.Perm (Fin H), ∀ h, tau (e h) = sigma h := by
  classical
  have hcard : (trueHeads sigma).card = (trueHeads tau).card := hcount
  obtain ⟨e, he⟩ := exists_perm_image hcard
  refine ⟨e, fun h ↦ ?_⟩
  have hmem : h ∈ trueHeads sigma ↔ e h ∈ trueHeads tau := by
    rw [← he]
    simp
  apply Bool.eq_iff_iff.mpr
  simpa only [mem_trueHeads] using hmem.symm

/-- Every orientation is a head permutation of its canonical count branch. -/
theorem exists_headPerm_to_canonicalOrientation {H : ℕ}
    (sigma : Fin H → Bool) :
    ∃ e : Equiv.Perm (Fin H),
      ∀ h, sigma (e h) = canonicalOrientation H (orientationCountIndex sigma) h := by
  apply exists_headPerm_orientation_eq_of_trueCount_eq
  simp [orientationCountIndex]

omit [Fintype I] [Fintype J] in
theorem permuteHeadFamily_orientedLiteralFamily {n H : ℕ}
    (e : Equiv.Perm (Fin H)) (sigma : Fin H → Bool) {tau : Fin H → Bool}
    (hsigma : ∀ h, sigma (e h) = tau h) :
    permuteHeadFamily e (orientedLiteralFamily (n := n) sigma) =
      orientedLiteralFamily (n := n) tau := by
  funext h j x
  simp [permuteHeadFamily, orientedLiteralFamily, hsigma h]

omit [Fintype I] [Fintype J] in
theorem orientation_preserved_by_swap_of_eq {H : ℕ}
    (sigma : Fin H → Bool) {h g : Fin H} (horientation : sigma h = sigma g) :
    ∀ k, sigma (Equiv.swap h g k) = sigma k := by
  intro k
  rw [Equiv.swap_apply_def]
  split_ifs with hkh hkg
  · subst k
    exact horientation.symm
  · subst k
    exact horientation
  · rfl

/-- Inside one orientation branch, denominator charts naming heads of the
same orientation are equivalent.  The literal coordinate and the selected
`+1` or `-1` face remain fixed. -/
theorem orientedSignedBlowupChartFeasible_denominator_iff_of_same_orientation
    {n H : ℕ} (f : (Fin n → Bool) → Bool) (sigma : Fin H → Bool)
    {h g : Fin H} (horientation : sigma h = sigma g)
    (j : Option (Fin n)) (positive : Bool) :
    SignedBlowupChartFeasible (orientedLiteralFamily sigma)
        (truthSign f) Finset.univ (.denominator h j positive) ↔
      SignedBlowupChartFeasible (orientedLiteralFamily sigma)
        (truthSign f) Finset.univ (.denominator g j positive) := by
  let e : Equiv.Perm (Fin H) := Equiv.swap h g
  have he : ∀ k, sigma (e k) = sigma k :=
    orientation_preserved_by_swap_of_eq sigma horientation
  have hfamily := permuteHeadFamily_orientedLiteralFamily (n := n) e sigma he
  have hpermute := signedBlowupChartFeasible_permuteHeads_iff e
    (orientedLiteralFamily sigma) (truthSign f) Finset.univ
    (.denominator h j positive)
  rw [hfamily] at hpermute
  simpa [e, permuteSignedNormalizationChart] using hpermute

/-! ## The chart quotient within one orientation branch -/

/-- Abstract chart types after forgetting the particular head name.  A
denominator type records its head orientation, literal coordinate, and
normalization sign.  A mixture type records only its normalization sign. -/
abbrev OrientedSignedNormalizationChartType (n : ℕ) :=
  (((Bool × Option (Fin n)) × Bool) ⊕ Bool)

/-- There are exactly `4 * (n + 1) + 2` abstract chart types, independently
of the number of heads. -/
theorem card_orientedSignedNormalizationChartType (n : ℕ) :
    Fintype.card (OrientedSignedNormalizationChartType n) =
      4 * (n + 1) + 2 := by
  simp [OrientedSignedNormalizationChartType]
  ring

/-- A denominator chart type is available precisely when the branch has a
head with its requested orientation.  Both mixture charts are always
available. -/
def OrientedSignedNormalizationChartType.IsAvailable {n H : ℕ}
    (sigma : Fin H → Bool) :
    OrientedSignedNormalizationChartType n → Prop
  | .inl ((orientation, _), _) => ∃ h, sigma h = orientation
  | .inr _ => True

/-- Choose one representative head for each available denominator chart
type. -/
noncomputable def orientedSignedNormalizationChartRepresentative
    {n H : ℕ} (sigma : Fin H → Bool)
    (q : OrientedSignedNormalizationChartType n)
    (hq : q.IsAvailable sigma) :
    SignedNormalizationChart (Fin H) (Option (Fin n)) := by
  rcases q with ⟨⟨orientation, j⟩, positive⟩ | positive
  · have hexists : ∃ h, sigma h = orientation := by
      simpa [OrientedSignedNormalizationChartType.IsAvailable] using hq
    exact .denominator (Classical.choose hexists) j positive
  · exact .mixture positive

/-- Checking one representative of every available abstract chart type is
equivalent to checking every concrete chart in the branch. -/
theorem all_orientedSignedBlowupCharts_infeasible_iff_all_chartTypes
    {n H : ℕ} (f : (Fin n → Bool) → Bool) (sigma : Fin H → Bool) :
    (∀ c : SignedNormalizationChart (Fin H) (Option (Fin n)),
      ¬ SignedBlowupChartFeasible (orientedLiteralFamily sigma)
        (truthSign f) Finset.univ c) ↔
      ∀ (q : OrientedSignedNormalizationChartType n)
        (hq : q.IsAvailable sigma),
        ¬ SignedBlowupChartFeasible (orientedLiteralFamily sigma)
          (truthSign f) Finset.univ
          (orientedSignedNormalizationChartRepresentative sigma q hq) := by
  constructor
  · intro hall q hq
    exact hall (orientedSignedNormalizationChartRepresentative sigma q hq)
  · intro hrepresentatives c
    cases c with
    | mixture positive =>
        exact hrepresentatives (.inr positive) trivial
    | denominator h j positive =>
        let q : OrientedSignedNormalizationChartType n :=
          .inl ((sigma h, j), positive)
        have hq : q.IsAvailable sigma := by
          exact ⟨h, rfl⟩
        let representative :=
          orientedSignedNormalizationChartRepresentative sigma q hq
        have hrepresentative := hrepresentatives q hq
        have hexists : ∃ g, sigma g = sigma h := ⟨h, rfl⟩
        let g : Fin H := Classical.choose hexists
        have hg : sigma g = sigma h := Classical.choose_spec hexists
        have hrepresentative_eq :
            representative = SignedNormalizationChart.denominator g j positive := by
          rfl
        change ¬ SignedBlowupChartFeasible (orientedLiteralFamily sigma)
          (truthSign f) Finset.univ representative at hrepresentative
        rw [hrepresentative_eq] at hrepresentative
        exact fun hfeasible ↦ hrepresentative
          ((orientedSignedBlowupChartFeasible_denominator_iff_of_same_orientation
            f sigma hg j positive).2 hfeasible)

/-- An oriented signed-secant branch depends only on the number of positive
head orientations. -/
theorem orientedSignedSecantFeasible_iff_countBranch {n H : ℕ}
    (f : (Fin n → Bool) → Bool) (sigma : Fin H → Bool) :
    SignedSecantFeasible (orientedLiteralFamily sigma) (truthSign f) Finset.univ ↔
      SignedSecantFeasible
        (orientedLiteralFamily
          (canonicalOrientation H (orientationCountIndex sigma)))
        (truthSign f) Finset.univ := by
  obtain ⟨e, he⟩ := exists_headPerm_to_canonicalOrientation sigma
  have hfamily := permuteHeadFamily_orientedLiteralFamily (n := n) e sigma he
  rw [← hfamily]
  exact (signedSecantFeasible_permuteHeads_iff e
    (orientedLiteralFamily sigma) (truthSign f) Finset.univ).symm

/-- An oriented signed-blow-up branch depends only on the number of positive
head orientations. -/
theorem orientedSignedBlowupFeasible_iff_countBranch {n H : ℕ}
    (hH : 0 < H) (f : (Fin n → Bool) → Bool) (sigma : Fin H → Bool) :
    SignedBlowupFeasible (orientedLiteralFamily sigma) (truthSign f) Finset.univ ↔
      SignedBlowupFeasible
        (orientedLiteralFamily
          (canonicalOrientation H (orientationCountIndex sigma)))
        (truthSign f) Finset.univ := by
  letI : Nonempty (Fin H) := Fin.pos_iff_nonempty.mp hH
  obtain ⟨e, he⟩ := exists_headPerm_to_canonicalOrientation sigma
  have hfamily := permuteHeadFamily_orientedLiteralFamily (n := n) e sigma he
  rw [← hfamily]
  exact (signedBlowupFeasible_permuteHeads_iff e
    (orientedLiteralFamily sigma) (truthSign f) Finset.univ_nonempty).symm

/-- The `2^H` signed-secant orientation search is exactly the `H + 1`
canonical true-count branches. -/
theorem exists_orientedSignedSecantFeasible_iff_exists_countBranch
    {n H : ℕ} (f : (Fin n → Bool) → Bool) :
    (∃ sigma : Fin H → Bool,
      SignedSecantFeasible (orientedLiteralFamily sigma)
        (truthSign f) Finset.univ) ↔
      ∃ k : Fin (H + 1),
        SignedSecantFeasible (orientedLiteralFamily (canonicalOrientation H k))
          (truthSign f) Finset.univ := by
  constructor
  · rintro ⟨sigma, hsigma⟩
    exact ⟨orientationCountIndex sigma,
      (orientedSignedSecantFeasible_iff_countBranch f sigma).1 hsigma⟩
  · rintro ⟨k, hk⟩
    exact ⟨canonicalOrientation H k, hk⟩

/-- The `2^H` signed-blow-up orientation search is exactly the `H + 1`
canonical true-count branches. -/
theorem exists_orientedSignedBlowupFeasible_iff_exists_countBranch
    {n H : ℕ} (hH : 0 < H) (f : (Fin n → Bool) → Bool) :
    (∃ sigma : Fin H → Bool,
      SignedBlowupFeasible (orientedLiteralFamily sigma)
        (truthSign f) Finset.univ) ↔
      ∃ k : Fin (H + 1),
        SignedBlowupFeasible (orientedLiteralFamily (canonicalOrientation H k))
          (truthSign f) Finset.univ := by
  constructor
  · rintro ⟨sigma, hsigma⟩
    exact ⟨orientationCountIndex sigma,
      (orientedSignedBlowupFeasible_iff_countBranch hH f sigma).1 hsigma⟩
  · rintro ⟨k, hk⟩
    exact ⟨canonicalOrientation H k, hk⟩

/-- Consequently, an all-orientations blow-up obstruction needs only `H + 1`
canonical infeasibility checks. -/
theorem all_orientedSignedBlowup_infeasible_iff_all_countBranches
    {n H : ℕ} (hH : 0 < H) (f : (Fin n → Bool) → Bool) :
    (∀ sigma : Fin H → Bool,
      ¬ SignedBlowupFeasible (orientedLiteralFamily sigma)
        (truthSign f) Finset.univ) ↔
      ∀ k : Fin (H + 1),
        ¬ SignedBlowupFeasible (orientedLiteralFamily (canonicalOrientation H k))
          (truthSign f) Finset.univ := by
  rw [← not_exists, ← not_exists,
    exists_orientedSignedBlowupFeasible_iff_exists_countBranch hH f]

/-- Fully finite obstruction form: it is enough to refute each coordinate or
mixture chart in each of the `H + 1` canonical orientation branches. -/
theorem all_orientedSignedBlowup_infeasible_iff_all_countBranchCharts
    {n H : ℕ} (hH : 0 < H) (f : (Fin n → Bool) → Bool) :
    (∀ sigma : Fin H → Bool,
      ¬ SignedBlowupFeasible (orientedLiteralFamily sigma)
        (truthSign f) Finset.univ) ↔
      ∀ (k : Fin (H + 1))
        (c : SignedNormalizationChart (Fin H) (Option (Fin n))),
        ¬ SignedBlowupChartFeasible
          (orientedLiteralFamily (canonicalOrientation H k))
          (truthSign f) Finset.univ c := by
  letI : Nonempty (Fin H) := Fin.pos_iff_nonempty.mp hH
  rw [all_orientedSignedBlowup_infeasible_iff_all_countBranches hH f]
  apply forall_congr'
  intro k
  exact not_signedBlowupFeasible_iff_all_charts_infeasible
    (orientedLiteralFamily (canonicalOrientation H k))
    (truthSign f) Finset.univ

/-- Final chart quotient for the obstruction search.  For each of the
`H + 1` canonical orientation-count branches, only the available members of
the fixed `4 * (n + 1) + 2` chart-type family need to be checked. -/
theorem all_orientedSignedBlowup_infeasible_iff_all_countBranchChartTypes
    {n H : ℕ} (hH : 0 < H) (f : (Fin n → Bool) → Bool) :
    (∀ sigma : Fin H → Bool,
      ¬ SignedBlowupFeasible (orientedLiteralFamily sigma)
        (truthSign f) Finset.univ) ↔
      ∀ (k : Fin (H + 1))
        (q : OrientedSignedNormalizationChartType n)
        (hq : q.IsAvailable (canonicalOrientation H k)),
        ¬ SignedBlowupChartFeasible
          (orientedLiteralFamily (canonicalOrientation H k))
          (truthSign f) Finset.univ
          (orientedSignedNormalizationChartRepresentative
            (canonicalOrientation H k) q hq) := by
  letI : Nonempty (Fin H) := Fin.pos_iff_nonempty.mp hH
  rw [all_orientedSignedBlowup_infeasible_iff_all_countBranches hH f]
  apply forall_congr'
  intro k
  calc
    (¬ SignedBlowupFeasible
        (orientedLiteralFamily (canonicalOrientation H k))
        (truthSign f) Finset.univ) ↔
        ∀ c : SignedNormalizationChart (Fin H) (Option (Fin n)),
          ¬ SignedBlowupChartFeasible
            (orientedLiteralFamily (canonicalOrientation H k))
            (truthSign f) Finset.univ c :=
      not_signedBlowupFeasible_iff_all_charts_infeasible
        (orientedLiteralFamily (canonicalOrientation H k))
        (truthSign f) Finset.univ
    _ ↔ _ := all_orientedSignedBlowupCharts_infeasible_iff_all_chartTypes
      f (canonicalOrientation H k)

end SignedSecant

end HeadComplexity
