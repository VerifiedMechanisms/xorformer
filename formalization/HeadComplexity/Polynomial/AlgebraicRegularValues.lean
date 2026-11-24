import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.TensorProduct.Basis

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Algebraically independent values and polynomial differentials

In characteristic zero, algebraically independent field elements have
linearly independent differentials. This provides an algebraic route to
regular values of polynomial maps.
-/

namespace HeadComplexity.PolynomialRootCount

open MvPolynomial KaehlerDifferential
open scoped TensorProduct

/-- Characteristic-zero field extensions are formally smooth, without a
finite-generation assumption. -/
theorem formallySmooth_field_of_charZero (F K : Type*) [Field F] [Field K]
    [CharZero F] [Algebra F K] : Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  let := hs.isAlgebraic_field
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

/-- For a formally smooth last extension, base change of differentials is injective. -/
theorem mapBaseChange_injective_of_formallySmooth
    (F S K : Type*) [CommRing F] [CommRing S] [CommRing K]
    [Algebra F S] [Algebra F K] [Algebra S K] [IsScalarTower F S K]
    [Algebra.FormallySmooth S K] : Function.Injective (mapBaseChange F S K) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange F S K x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

/-- Algebraic independence forces independence of the universal differentials. -/
theorem linearIndependent_differentials {F K ι : Type*} [Field F] [Field K]
    [CharZero F] [Algebra F K] {a : ι → K} (ha : AlgebraicIndependent F a) :
    LinearIndependent K (fun i ↦ D F K (a i)) := by
  let S := MvPolynomial ι F
  let : Algebra S K := (aeval a).toRingHom.toAlgebra
  let : IsScalarTower F S K := IsScalarTower.of_algebraMap_eq' (aeval a).comp_algebraMap.symm
  let : FaithfulSMul S K := (faithfulSMul_iff_algebraMap_injective S K).mpr ha
  let : Algebra (FractionRing S) K := FractionRing.liftAlgebra S K
  let : IsScalarTower S (FractionRing S) K := FractionRing.isScalarTower_liftAlgebra S K
  let : Algebra.FormallySmooth S (FractionRing S) :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors S)
  let : Algebra.FormallySmooth (FractionRing S) K :=
    formallySmooth_field_of_charZero (FractionRing S) K
  let : Algebra.FormallySmooth S K := Algebra.FormallySmooth.comp S (FractionRing S) K
  have h := ((mvPolynomialBasis F ι).baseChange K).linearIndependent.map'
    (mapBaseChange F S K)
    (LinearMap.ker_eq_bot.mpr (mapBaseChange_injective_of_formallySmooth F S K))
  convert h using 1
  funext i
  rw [Function.comp_apply, Module.Basis.baseChange_apply, mvPolynomialBasis_apply]
  change D F K (a i) = mapBaseChange F S K (1 ⊗ₜ[S] D F S (X i))
  rw [mapBaseChange_tmul, one_smul, map_D]
  congr 1
  exact (aeval_X a i).symm

/-- The universal differential of a polynomial evaluation is its formal Jacobian. -/
theorem differential_aeval {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    [Fintype ι] (x : ι → K) (p : MvPolynomial ι F) :
    D F K (aeval x p) = ∑ i, aeval x (pderiv i p) • D F K (x i) := by
  classical
  let S := MvPolynomial ι F
  let : Algebra S K := (aeval x).toRingHom.toAlgebra
  let : IsScalarTower F S K := IsScalarTower.of_algebraMap_eq' (aeval x).comp_algebraMap.symm
  have h := congrArg (KaehlerDifferential.map F F S K)
    ((mvPolynomialBasis F ι).sum_repr (D F S p))
  simp only [S, map_sum, map_smul, mvPolynomialBasis_repr_apply,
    mvPolynomialBasis_apply, map_D] at h
  convert h.symm using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← IsScalarTower.algebraMap_smul K (pderiv i p)]
  congr 1
  change D F K (x i) = D F K (aeval x (X i))
  rw [aeval_X]

/-- Algebraically independent polynomial values force independent Jacobian rows. -/
theorem linearIndependent_jacobian_of_values {F K ι J : Type*}
    [Field F] [Field K] [CharZero F] [Algebra F K] [Finite ι]
    (x : ι → K) (p : J → MvPolynomial ι F)
    (ha : AlgebraicIndependent F (fun j ↦ aeval x (p j))) :
    LinearIndependent K (fun j i ↦ aeval x (pderiv i (p j))) := by
  let := Fintype.ofFinite ι
  apply LinearIndependent.of_comp (Fintype.linearCombination K (fun i ↦ D F K (x i)))
  simpa only [Function.comp_def, Fintype.linearCombination_apply, ← differential_aeval]
    using linearIndependent_differentials ha

end HeadComplexity.PolynomialRootCount
