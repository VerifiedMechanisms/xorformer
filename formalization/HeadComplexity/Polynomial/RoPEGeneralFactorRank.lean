import HeadComplexity.Polynomial.RoPEGeneralDerivative
import HeadComplexity.Polynomial.VanillaBlockDerivatives

/-!
# The denominator-kernel rank bound for arbitrary cleared head families

A first direction annihilating all denominator factors removes every numerator
variable from the first derivative. The second derivative then factors through
the H denominator slopes. Any linear coefficient projection preserves this rank
bound. Applications supply the affine derivative identities explicitly.
-/

noncomputable section

namespace HeadComplexity.RoPEGeneralFactorRank

open MvPolynomial RoPEGeneralDerivative
open scoped BigOperators

variable {σ : Type*} {H : ℕ}

abbrev Poly (σ : Type*) := MvPolynomial σ ℝ

def cleared (N D : Fin H → Poly σ) : Poly σ :=
  ∑ i, N i * ∏ j ∈ Finset.univ.erase i, D j

def derivativeMap {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] (σ → ℝ)) (P : Poly σ) : V →ₗ[ℝ] Poly σ where
  toFun w := directional (L w) P
  map_add' x y := by rw [map_add, directional_add]; rfl
  map_smul' c x := by rw [map_smul, directional_smul]; rfl

def slopeDerivative (n : Fin H → ℝ) (D : Fin H → Poly σ) :
    (Fin H → ℝ) →ₗ[ℝ] Poly σ :=
  ∑ i : Fin H, ∑ j ∈ Finset.univ.erase i,
    (LinearMap.proj j).smulRight
      (C (n i) * ∏ k ∈ (Finset.univ.erase i).erase j, D k)

theorem first_derivative_of_denominator_kernel
    (N D : Fin H → Poly σ) (v : σ → ℝ) (n : Fin H → ℝ)
    (hN : ∀ i, directional v (N i) = C (n i))
    (hD : ∀ i, directional v (D i) = 0) :
    directional v (cleared N D) =
      ∑ i, C (n i) * ∏ j ∈ Finset.univ.erase i, D j := by
  unfold cleared
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, derivation_prod, hD,
    zero_mul, Finset.sum_const_zero, mul_zero, zero_add, hN]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem second_derivative_factors
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (N D : Fin H → Poly σ) (v : σ → ℝ) (n : Fin H → ℝ)
    (L : V →ₗ[ℝ] (σ → ℝ)) (d : V →ₗ[ℝ] (Fin H → ℝ))
    (hN : ∀ i, directional v (N i) = C (n i))
    (hD : ∀ i, directional v (D i) = 0)
    (hL : ∀ w i, directional (L w) (D i) = C (d w i)) :
    derivativeMap L (directional v (cleared N D)) = (slopeDerivative n D).comp d := by
  apply LinearMap.ext
  intro w
  change directional (L w) (directional v (cleared N D)) = slopeDerivative n D (d w)
  rw [first_derivative_of_denominator_kernel N D v n hN hD]
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, directional_C,
    mul_zero, add_zero, derivation_prod, hL, slopeDerivative, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply, smul_eq_C_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem projected_second_rank_le
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (N D : Fin H → Poly σ) (v : σ → ℝ) (n : Fin H → ℝ)
    (L : V →ₗ[ℝ] (σ → ℝ)) (d : V →ₗ[ℝ] (Fin H → ℝ))
    (Φ : Poly σ →ₗ[ℝ] W)
    (hN : ∀ i, directional v (N i) = C (n i))
    (hD : ∀ i, directional v (D i) = 0)
    (hL : ∀ w i, directional (L w) (D i) = C (d w i)) :
    Module.finrank ℝ (Φ.comp (derivativeMap L (directional v (cleared N D)))).range ≤ H := by
  rw [second_derivative_factors N D v n L d hN hD hL]
  let B := Φ.comp (slopeDerivative n D)
  have hsub : (Φ.comp ((slopeDerivative n D).comp d)).range ≤ B.range := by
    rintro y ⟨x, rfl⟩
    exact ⟨d x, rfl⟩
  calc
    _ ≤ Module.finrank ℝ B.range := Submodule.finrank_mono hsub
    _ ≤ H := by simpa using B.finrank_range_le

/-- Denominator slopes evaluated on any linear family of second directions. -/
def dataSlopeMap [Fintype σ] {V : Type*} [AddCommGroup V] [Module ℝ V]
    (a : VanillaGeneralCentered.Data H σ) (L : V →ₗ[ℝ] (σ → ℝ)) :
    V →ₗ[ℝ] (Fin H → ℝ) :=
  LinearMap.pi (fun h ↦ ∑ i : σ,
    (a.denominatorSlope h i) • ((LinearMap.proj i).comp L))

theorem dataSlopeMap_apply [Fintype σ] {V : Type*} [AddCommGroup V] [Module ℝ V]
    (a : VanillaGeneralCentered.Data H σ) (L : V →ₗ[ℝ] (σ → ℝ)) (w : V) (h : Fin H) :
    dataSlopeMap a L w h = ∑ i, a.denominatorSlope h i * L w i := by
  simp [dataSlopeMap]

/-- Actual centered vanilla factors have the required projected rank bound in
any direction annihilating their denominator slopes. -/
theorem data_projected_second_rank_le [Fintype σ]
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (a : VanillaGeneralCentered.Data H σ) (v : σ → ℝ)
    (L : V →ₗ[ℝ] (σ → ℝ)) (Φ : Poly σ →ₗ[ℝ] W)
    (hker : ∀ h, ∑ i, a.denominatorSlope h i * v i = 0) :
    Module.finrank ℝ (Φ.comp (derivativeMap L (directional v a.polynomial))).range ≤ H := by
  apply projected_second_rank_le
    (fun h ↦ RoPECrossBlockCoefficients.affine (a.numeratorConstant h) (a.numeratorSlope h))
    (fun h ↦ RoPECrossBlockCoefficients.affine (a.denominatorConstant h) (a.denominatorSlope h))
    v (fun h ↦ ∑ i, a.numeratorSlope h i * v i) L (dataSlopeMap a L) Φ
  · intro h
    exact VanillaBlockDerivatives.directional_affine v _ _
  · intro h
    rw [VanillaBlockDerivatives.directional_affine, hker h, map_zero]
  · intro w h
    rw [VanillaBlockDerivatives.directional_affine, dataSlopeMap_apply]

theorem data_block_projected_second_rank_le
    {β ι W : Type*} [Fintype β] [Fintype ι] [DecidableEq β]
    [AddCommGroup W] [Module ℝ W]
    (a : VanillaGeneralCentered.Data H (β × ι)) (b₁ b₂ : β) (v : ι → ℝ)
    (Φ : Poly (β × ι) →ₗ[ℝ] W)
    (hker : (VanillaBlockDerivatives.denominatorRows a b₁).mulVec v = 0) :
    Module.finrank ℝ (Φ.comp (derivativeMap
      (VanillaBlockDerivatives.blockDirectionLinear b₂)
      (directional (VanillaBlockDerivatives.blockDirection b₁ v) a.polynomial))).range ≤ H := by
  apply projected_second_rank_le
    (fun h ↦ RoPECrossBlockCoefficients.affine (a.numeratorConstant h) (a.numeratorSlope h))
    (fun h ↦ RoPECrossBlockCoefficients.affine (a.denominatorConstant h) (a.denominatorSlope h))
    (VanillaBlockDerivatives.blockDirection b₁ v)
    ((VanillaBlockDerivatives.numeratorRows a b₁).mulVec v)
    (VanillaBlockDerivatives.blockDirectionLinear b₂)
    (VanillaBlockDerivatives.denominatorRows a b₂).mulVecLin Φ
  · exact VanillaBlockDerivatives.numerator_derivative a b₁ v
  · exact VanillaBlockDerivatives.denominator_derivative_of_kernel a b₁ v hker
  · intro w h
    exact VanillaBlockDerivatives.denominator_derivative a b₂ w h

end HeadComplexity.RoPEGeneralFactorRank
