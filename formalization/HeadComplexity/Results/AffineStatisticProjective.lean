import HeadComplexity.Atoms.AffineStatisticPolynomial
import HeadComplexity.Atoms.PositiveStatisticRawBit
import HeadComplexity.Results.AffineStatisticSignChanges

set_option linter.style.header false

/-! The projective compiler removes the positivity restriction on an affine
statistic's weights. These are upper bounds for this class, not an asymptotic
worst-case head lower bound. -/
namespace HeadComplexity

/-- A polynomial threshold certificate through any affine statistic compiles
with no increase in its degree budget. -/
theorem computableWithHeadsN_of_univariateAffine {n K : ℕ}
    (c : ℝ) (a : Fin n → ℝ) (f : (Fin n → Bool) → Bool)
    (h : UnivariateThresholdDegLE (affineValue c a) f K) :
    computableWithHeadsN n K f := by
  obtain ⟨P, hdeg, hstrict⟩ :=
    exists_strictUnivariateSignRep_of_UnivariateThresholdDegLE h
  apply computableWithHeadsN_affineStatisticPolynomial c a P hdeg f
  · intro x
    cases hx : f x
    · exact ((hstrict x).2 hx).ne
    · exact ((hstrict x).1 hx).ne'
  · exact hstrict.signRepresents

/-- Head complexity is at most any univariate threshold degree through an
arbitrary affine statistic. -/
theorem HStar_le_of_univariateAffine {n K : ℕ}
    (c : ℝ) (a : Fin n → ℝ) (f : (Fin n → Bool) → Bool)
    (h : UnivariateThresholdDegLE (affineValue c a) f K) :
    HStar n f ≤ K :=
  HStar_le_of_computableWithHeadsN
    (computableWithHeadsN_of_univariateAffine c a f h)

namespace AffineStatisticProfile

/-- The number of ordered label changes is a head upper bound even when the
affine statistic has mixed-sign coefficients. -/
theorem computableWithHeadsN_alternations {n : ℕ} {c : ℝ}
    {a : Fin n → ℝ} {f : (Fin n → Bool) → Bool}
    (C : AffineStatisticProfile c a f) :
    computableWithHeadsN n C.alternations f :=
  computableWithHeadsN_of_univariateAffine c a f C.univariateThresholdDegLE

theorem HStar_le_alternations {n : ℕ} {c : ℝ}
    {a : Fin n → ℝ} {f : (Fin n → Bool) → Bool}
    (C : AffineStatisticProfile c a f) :
    HStar n f ≤ C.alternations :=
  HStar_le_of_computableWithHeadsN C.computableWithHeadsN_alternations

end AffineStatisticProfile
end HeadComplexity
