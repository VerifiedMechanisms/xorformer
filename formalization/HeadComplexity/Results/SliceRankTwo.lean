import HeadComplexity.Atoms.ClearedNormalForm
import HeadComplexity.Atoms.FracComputableMonotone
import HeadComplexity.Results.LowComplexity
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option linter.style.header false

/-!
# Slice-rank-two obstruction for cleared head scores

Affine numerator and denominator forms are homogenized with one new variable.
After clearing denominators, isolating one head writes the resulting degree
`H` form as a sum of two products of degrees `1` and `H - 1`.  The second
linear factor is an actual positive attention denominator.
-/

namespace HeadComplexity

open Finset MvPolynomial
open scoped BigOperators

variable {n H : ℕ}

/-- Homogeneous point `(1,x)` associated with a Boolean input. -/
def homogenizedCubePoint (x : Fin n → Bool) : Option (Fin n) → ℝ
  | none => 1
  | some i => boolToReal (x i)

/-- Degree-one homogenization of the affine part of a polynomial. -/
noncomputable def affineHomogenize (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Option (Fin n)) ℝ :=
  C (P.coeff 0) * X none +
    ∑ i, C (P.coeff (Finsupp.single i 1)) * X (some i)

/-- Affine homogenization is homogeneous of degree one. -/
theorem affineHomogenize_isHomogeneous (P : MvPolynomial (Fin n) ℝ) :
    (affineHomogenize P).IsHomogeneous 1 := by
  unfold affineHomogenize
  apply IsHomogeneous.add
  · exact isHomogeneous_C_mul_X _ _
  · exact IsHomogeneous.sum Finset.univ _ 1 fun i _ ↦
      isHomogeneous_C_mul_X _ _

/-- On the affine chart `z₀ = 1`, homogenization preserves every affine
polynomial's value. -/
theorem eval_affineHomogenize (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ 1) (x : Fin n → Bool) :
    eval (homogenizedCubePoint x) (affineHomogenize P) =
      eval (cubePoint x) P := by
  rw [eval_cubePoint_affine P hP]
  simp [affineHomogenize, homogenizedCubePoint]

/-- Homogenized denominator-cleared polynomial of an affine fraction family. -/
noncomputable def homogenizedClearedAffinePoly
    (A : AffineFractionFamily n H) (c : ℝ) :
    MvPolynomial (Option (Fin n)) ℝ :=
  C c * ∏ h, affineHomogenize (A.den h) +
    ∑ h, affineHomogenize (A.num h) *
      ∏ g ∈ Finset.univ.erase h, affineHomogenize (A.den g)

private theorem homogenizedDenProduct_isHomogeneous
    (A : AffineFractionFamily n H) (s : Finset (Fin H)) :
    (∏ h ∈ s, affineHomogenize (A.den h)).IsHomogeneous s.card := by
  have hprod := IsHomogeneous.prod s
    (fun h ↦ affineHomogenize (A.den h)) (fun _ ↦ 1)
    (fun h _ ↦ affineHomogenize_isHomogeneous (A.den h))
  simpa using hprod

/-- The homogenized cleared polynomial has homogeneous degree `H`. -/
theorem homogenizedClearedAffinePoly_isHomogeneous
    (A : AffineFractionFamily n H) (c : ℝ) :
    (homogenizedClearedAffinePoly A c).IsHomogeneous H := by
  classical
  unfold homogenizedClearedAffinePoly
  apply IsHomogeneous.add
  · have hprod := homogenizedDenProduct_isHomogeneous A
        (Finset.univ : Finset (Fin H))
    simpa using hprod.C_mul c
  · apply IsHomogeneous.sum Finset.univ _ H
    intro h hh
    have hprod := homogenizedDenProduct_isHomogeneous A
      ((Finset.univ : Finset (Fin H)).erase h)
    have hcard : ((Finset.univ : Finset (Fin H)).erase h).card = H - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ h), Finset.card_fin]
    have hmul := (affineHomogenize_isHomogeneous (A.num h)).mul hprod
    have hH : 0 < H := Nat.pos_of_ne_zero (by rintro rfl; exact h.elim0)
    have hdegree : 1 + (H - 1) = H := by omega
    simpa [hcard, hdegree] using hmul

/-- Homogenization commutes with evaluation of the cleared affine score on
the chart `(1,x)`. -/
theorem eval_homogenizedClearedAffinePoly
    (A : AffineFractionFamily n H) (c : ℝ) (x : Fin n → Bool) :
    eval (homogenizedCubePoint x) (homogenizedClearedAffinePoly A c) =
      eval (cubePoint x) (clearedAffinePoly A c) := by
  classical
  simp only [homogenizedClearedAffinePoly, clearedAffinePoly, map_add,
    map_mul, map_prod, map_sum, eval_C]
  simp_rw [eval_affineHomogenize (A.den _) (A.den_degree _)]
  simp_rw [eval_affineHomogenize (A.num _) (A.num_degree _)]

/-- A homogeneous degree-`H` polynomial written as two degree-one slices. -/
structure HomogeneousSliceRankTwoCertificate
    (P : MvPolynomial (Option (Fin n)) ℝ) (H : ℕ) where
  linear₁ : MvPolynomial (Option (Fin n)) ℝ
  linear₂ : MvPolynomial (Option (Fin n)) ℝ
  cofactor₁ : MvPolynomial (Option (Fin n)) ℝ
  cofactor₂ : MvPolynomial (Option (Fin n)) ℝ
  polynomial_homogeneous : P.IsHomogeneous H
  linear₁_homogeneous : linear₁.IsHomogeneous 1
  linear₂_homogeneous : linear₂.IsHomogeneous 1
  cofactor₁_homogeneous : cofactor₁.IsHomogeneous (H - 1)
  cofactor₂_homogeneous : cofactor₂.IsHomogeneous (H - 1)
  decomposition : P = linear₁ * cofactor₁ + linear₂ * cofactor₂

namespace HomogeneousSliceRankTwoCertificate

/-- Both slice generators vanishing forces the represented polynomial to
vanish. -/
theorem eval_eq_zero_of_generators_eq_zero
    {P : MvPolynomial (Option (Fin n)) ℝ}
    (C : HomogeneousSliceRankTwoCertificate P H)
    (point : Option (Fin n) → ℝ)
    (h₁ : eval point C.linear₁ = 0) (h₂ : eval point C.linear₂ = 0) :
    eval point P = 0 := by
  rw [C.decomposition, map_add, map_mul, map_mul, h₁, h₂]
  ring

/-- The same linear-space containment persists after arbitrary coefficient
base change, including `ℝ → ℂ`. -/
theorem map_eval_eq_zero_of_generators_eq_zero
    {P : MvPolynomial (Option (Fin n)) ℝ}
    (C : HomogeneousSliceRankTwoCertificate P H)
    {S : Type*} [CommSemiring S] (F : ℝ →+* S)
    (point : Option (Fin n) → S)
    (h₁ : eval point (map F C.linear₁) = 0)
    (h₂ : eval point (map F C.linear₂) = 0) :
    eval point (map F P) = 0 := by
  rw [C.decomposition, map_add, map_mul, map_mul,
    map_add, map_mul, map_mul, h₁, h₂]
  ring

end HomogeneousSliceRankTwoCertificate

/-- First slice generator after absorbing the global bias at `h₀`. -/
noncomputable def sliceLinear₁ (A : AffineFractionFamily n H) (c : ℝ)
    (h₀ : Fin H) : MvPolynomial (Option (Fin n)) ℝ :=
  affineHomogenize (A.num h₀) + C c * affineHomogenize (A.den h₀)

/-- The second slice generator is an actual homogenized denominator. -/
noncomputable def sliceLinear₂ (A : AffineFractionFamily n H)
    (h₀ : Fin H) : MvPolynomial (Option (Fin n)) ℝ :=
  affineHomogenize (A.den h₀)

/-- Cofactor of the absorbed first slice. -/
noncomputable def sliceCofactor₁ (A : AffineFractionFamily n H)
    (h₀ : Fin H) : MvPolynomial (Option (Fin n)) ℝ :=
  ∏ g ∈ Finset.univ.erase h₀, affineHomogenize (A.den g)

/-- Cofactor of the actual-denominator slice. -/
noncomputable def sliceCofactor₂ (A : AffineFractionFamily n H)
    (h₀ : Fin H) : MvPolynomial (Option (Fin n)) ℝ :=
  ∑ h ∈ Finset.univ.erase h₀,
    affineHomogenize (A.num h) *
      ∏ g ∈ (Finset.univ.erase h₀).erase h,
        affineHomogenize (A.den g)

/-- Isolating `h₀` gives the advertised two-slice identity. -/
theorem homogenizedClearedAffinePoly_eq_two_slices
    (A : AffineFractionFamily n H) (c : ℝ) (h₀ : Fin H) :
    homogenizedClearedAffinePoly A c =
      sliceLinear₁ A c h₀ * sliceCofactor₁ A h₀ +
        sliceLinear₂ A h₀ * sliceCofactor₂ A h₀ := by
  classical
  let B : Fin H → MvPolynomial (Option (Fin n)) ℝ :=
    fun h ↦ affineHomogenize (A.den h)
  let N : Fin H → MvPolynomial (Option (Fin n)) ℝ :=
    fun h ↦ affineHomogenize (A.num h)
  let term : Fin H → MvPolynomial (Option (Fin n)) ℝ :=
    fun h ↦ N h * ∏ g ∈ Finset.univ.erase h, B g
  have hsplit : (∑ h, term h) =
      term h₀ + ∑ h ∈ Finset.univ.erase h₀, term h := by
    exact (Finset.add_sum_erase Finset.univ term (Finset.mem_univ h₀)).symm
  have hprod : (∏ h, B h) =
      B h₀ * ∏ g ∈ Finset.univ.erase h₀, B g :=
    (Finset.mul_prod_erase Finset.univ B (Finset.mem_univ h₀)).symm
  have hterm : ∀ h ∈ Finset.univ.erase h₀,
      term h = B h₀ *
        (N h * ∏ g ∈ (Finset.univ.erase h₀).erase h, B g) := by
    intro h hh
    have hne : h ≠ h₀ := Finset.ne_of_mem_erase hh
    have hh₀ : h₀ ∈ (Finset.univ : Finset (Fin H)).erase h := by
      simp [Ne.symm hne]
    have hfactor : (∏ g ∈ Finset.univ.erase h, B g) =
        B h₀ * ∏ g ∈ (Finset.univ.erase h₀).erase h, B g := by
      rw [← Finset.mul_prod_erase (Finset.univ.erase h) B hh₀]
      congr 1
      rw [Finset.erase_right_comm]
    dsimp [term]
    rw [hfactor]
    ring
  unfold homogenizedClearedAffinePoly sliceLinear₁ sliceLinear₂
    sliceCofactor₁ sliceCofactor₂
  change C c * ∏ h, B h + ∑ h, term h =
    (N h₀ + C c * B h₀) * ∏ g ∈ Finset.univ.erase h₀, B g +
      B h₀ * ∑ h ∈ Finset.univ.erase h₀,
        N h * ∏ g ∈ (Finset.univ.erase h₀).erase h, B g
  rw [hsplit, hprod]
  have hsum : (∑ h ∈ Finset.univ.erase h₀, term h) =
      B h₀ * ∑ h ∈ Finset.univ.erase h₀,
        N h * ∏ g ∈ (Finset.univ.erase h₀).erase h, B g := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    exact hterm
  rw [hsum]
  dsimp [term]
  ring

/-- The two explicit cofactors are homogeneous of degree `H - 1`. -/
theorem sliceCofactors_homogeneous (hH : 2 ≤ H)
    (A : AffineFractionFamily n H) (h₀ : Fin H) :
    (sliceCofactor₁ A h₀).IsHomogeneous (H - 1) ∧
      (sliceCofactor₂ A h₀).IsHomogeneous (H - 1) := by
  classical
  constructor
  · unfold sliceCofactor₁
    have hprod := homogenizedDenProduct_isHomogeneous A
      ((Finset.univ : Finset (Fin H)).erase h₀)
    have hcard : ((Finset.univ : Finset (Fin H)).erase h₀).card = H - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ h₀), Finset.card_fin]
    simpa [hcard] using hprod
  · unfold sliceCofactor₂
    apply IsHomogeneous.sum (Finset.univ.erase h₀) _ (H - 1)
    intro h hh
    have hprod := homogenizedDenProduct_isHomogeneous A
      ((Finset.univ.erase h₀).erase h)
    have hcard₀ : ((Finset.univ : Finset (Fin H)).erase h₀).card = H - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ h₀), Finset.card_fin]
    have hcard : ((Finset.univ.erase h₀).erase h).card = H - 2 := by
      rw [Finset.card_erase_of_mem hh, hcard₀]
      omega
    have hmul := (affineHomogenize_isHomogeneous (A.num h)).mul hprod
    have hdegree : 1 + (H - 2) = H - 1 := by omega
    simpa [hcard, hdegree] using hmul

/-- Explicit slice-rank-two certificate whose second generator is an actual
attention denominator. -/
noncomputable def sliceRankTwoCertificate (hH : 2 ≤ H)
    (A : AffineFractionFamily n H) (c : ℝ) :
    HomogeneousSliceRankTwoCertificate (homogenizedClearedAffinePoly A c) H := by
  let h₀ : Fin H := ⟨0, by omega⟩
  refine
    { linear₁ := sliceLinear₁ A c h₀
      linear₂ := sliceLinear₂ A h₀
      cofactor₁ := sliceCofactor₁ A h₀
      cofactor₂ := sliceCofactor₂ A h₀
      polynomial_homogeneous := homogenizedClearedAffinePoly_isHomogeneous A c
      linear₁_homogeneous := ?_
      linear₂_homogeneous := affineHomogenize_isHomogeneous (A.den h₀)
      cofactor₁_homogeneous := (sliceCofactors_homogeneous hH A h₀).1
      cofactor₂_homogeneous := (sliceCofactors_homogeneous hH A h₀).2
      decomposition := homogenizedClearedAffinePoly_eq_two_slices A c h₀ }
  unfold sliceLinear₁
  exact (affineHomogenize_isHomogeneous (A.num h₀)).add
    ((affineHomogenize_isHomogeneous (A.den h₀)).C_mul c)

/-- Strict sign realization on the homogenized Boolean cube. -/
def StrictHomogeneousSignRepresents
    (P : MvPolynomial (Option (Fin n)) ℝ)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, if f x then 0 < eval (homogenizedCubePoint x) P
    else eval (homogenizedCubePoint x) P < 0

/-- Existence of a homogeneous degree-`H` slice-rank-two strict sign
realization. -/
def HomogeneousSliceRankTwoSignRep
    (H : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ P : MvPolynomial (Option (Fin n)) ℝ,
    Nonempty (HomogeneousSliceRankTwoCertificate P H) ∧
      StrictHomogeneousSignRepresents P f

/-- Every `H`-head computation supplies a homogeneous slice-rank-two strict
sign realization. -/
theorem homogeneousSliceRankTwoSignRep_of_computableWithHeadsN
    (hH : 2 ≤ H) (f : (Fin n → Bool) → Bool)
    (hf : computableWithHeadsN n H f) :
    HomogeneousSliceRankTwoSignRep H f := by
  classical
  obtain ⟨phi, c, hstrict⟩ :=
    exists_strict_fracCertificate (fracComputable_of_computable hf)
  let A : AffineFractionFamily n H := FracAtom.affineFamily phi
  let P := homogenizedClearedAffinePoly A c
  refine ⟨P, ⟨sliceRankTwoCertificate hH A c⟩, fun x ↦ ?_⟩
  rw [eval_homogenizedClearedAffinePoly]
  rw [show clearedAffinePoly A c = clearedAtomPoly phi c by rfl,
    clearedAtomPoly_eval]
  have hden : 0 < eval (cubePoint x) (atomDenProduct phi) :=
    atomDenProduct_eval_pos phi x
  cases hfx : f x with
  | false =>
      have hs := hstrict x
      simp only [hfx, Bool.false_eq_true, ↓reduceIte] at hs ⊢
      exact mul_neg_of_pos_of_neg hden hs
  | true =>
      have hs := hstrict x
      simp only [hfx, ↓reduceIte] at hs ⊢
      exact mul_pos hden hs

/-- Failure of every degree-`H` homogeneous slice-rank-two sign realization
forces more than `H` heads. -/
theorem HStar_gt_of_no_homogeneousSliceRankTwoSignRep
    (hH : 2 ≤ H) (f : (Fin n → Bool) → Bool)
    (hobs : ¬ HomogeneousSliceRankTwoSignRep H f) :
    H < HStar n f := by
  by_contra hnot
  have hle : HStar n f ≤ H := Nat.le_of_not_gt hnot
  apply hobs
  exact homogeneousSliceRankTwoSignRep_of_computableWithHeadsN hH f
    (computableWithHeadsN_mono hle (HStar_computable f))

/-- In the constructed certificate, the second generator evaluates positively
on every homogenized Boolean input because it is an actual denominator. -/
theorem sliceRankTwoCertificate_linear₂_pos (hH : 2 ≤ H)
    (A : AffineFractionFamily n H) (c : ℝ) (x : Fin n → Bool) :
    0 < eval (homogenizedCubePoint x)
      (sliceRankTwoCertificate hH A c).linear₂ := by
  let h₀ : Fin H := ⟨0, by omega⟩
  change 0 < eval (homogenizedCubePoint x) (affineHomogenize (A.den h₀))
  rw [eval_affineHomogenize (A.den h₀) (A.den_degree h₀)]
  exact A.den_pos h₀ x

end HeadComplexity
