import HeadComplexity.Results.PureGeneralThresholdDegree
import HeadComplexity.Polynomial.VanillaCoefficientLimit
import HeadComplexity.Results.RoPEGeneralBounds

set_option linter.style.header false

/-!
# Remaining algebraic interface for the arbitrary-head separation

All actual classifier, architecture, averaging, and analytic limit steps are
proved. The premise retained here is precisely the finite-dimensional
oriented-factor coefficient-limit obstruction for the actual source.
The complete H=3 separation does not require this premise.
-/

namespace HeadComplexity.PureGeneralReplicatedGrid

open MvPolynomial Filter VanillaGeneralCentered VanillaCoefficientLimit
open RoPEGeneralPhysicalCoordinates
open scoped Topology

/-- Explicit algebraic obstruction, with no Boolean computability premise. -/
def OrientedFactorLimitExcluded (h : ℕ) : Prop :=
  ∀ (a : ℕ → Data (h + 1) (Input h)) (t : ℝ), t ≠ 0 →
    (∀ k i, VanillaThreeCentered.Oriented ((a k).denominatorSlope i)) →
    ¬ TopCoefficientLimit a (C t * physical h)

theorem eventually_not_vanilla_of_factor_obstruction (h : ℕ)
    (hno : OrientedFactorLimitExcluded h) :
    ∀ᶠ m in atTop, ¬ computableWithSharedHeadsN (groupCount (h + 1) * m) (h + 1)
      (classifier (h + 1) m) := by
  have he := eventually_not_vanilla_of_factor_limit_obstruction
    (by omega : 0 < h + 1) (physical h) (scalar_multiple_of_weak_sign_cube h) hno
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with m hm hmpos
  rw [physical_classifier_eq h m hmpos] at hm
  exact hm

/-- Once the explicit algebraic factor-limit obstruction is supplied, the
actual family has the full claimed pure/vanilla separation. -/
theorem eventually_separation_of_factor_obstruction (h : ℕ) (hh : 1 ≤ h)
    (hno : OrientedFactorLimitExcluded h) :
    ∀ᶠ m in atTop,
      PureRoPEHStar (groupCount (h + 1) * m) (classifier (h + 1) m) = h + 1 ∧
      h + 2 ≤ SharedHStar (groupCount (h + 1) * m) (classifier (h + 1) m) ∧
      SharedHStar (groupCount (h + 1) * m) (classifier (h + 1) m) ≤ 2 ^ (h + 1) - 2 ∧
      StandardPureRoPEHStar (groupCount (h + 1) * m) (classifier (h + 1) m) = h + 1 ∧
      FreePureRoPEHStar (groupCount (h + 1) * m) (classifier (h + 1) m) = h + 1 := by
  classical
  filter_upwards [eventually_not_vanilla_of_factor_obstruction h hno,
    eventually_exact_degree_and_pure_minima h] with m hnot hmin
  obtain ⟨_, hp, hs, hf⟩ := hmin
  have hl : ¬ HStar (groupCount (h + 1) * m) (classifier (h + 1) m) ≤ h + 1 := by
    intro hle
    apply hnot
    apply computableWithSharedHeadsN_mono hle
    exact computableWithSharedHeadsN_of_computableWithHeadsN
      (HStar_computable (classifier (h + 1) m))
  have hu := HStar_le_improved_exponential_pureRoPEHStar (classifier (h + 1) m)
    (by omega : 2 ≤ PureRoPEHStar (groupCount (h + 1) * m) (classifier (h + 1) m))
  rw [hp] at hu
  rw [SharedHStar_eq_HStar]
  exact ⟨hp, by omega, hu, hs, hf⟩

end HeadComplexity.PureGeneralReplicatedGrid
