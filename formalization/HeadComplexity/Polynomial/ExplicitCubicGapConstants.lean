import HeadComplexity.Polynomial.ExplicitCubicVandermonde
import HeadComplexity.Polynomial.ExplicitCubicHessianGap
import HeadComplexity.Polynomial.QuantitativeCrossRecovery

set_option linter.style.header false
set_option exponentiation.threshold 3000

/-! # Exact arithmetic for the explicit squarefree exclusion radius -/

namespace HeadComplexity.ExplicitCubicGapConstants
noncomputable section
open ExplicitCubicVandermonde ExplicitCubicQuantitativeBounds
open ExplicitCubicHessianGap QuantitativeCrossRecovery

def squarefreeRadius : ℝ := 1 / 2^2000

theorem squarefreeRadius_pos : 0 < squarefreeRadius := by
  unfold squarefreeRadius
  positivity

theorem squarefreeRadius_le_one : squarefreeRadius ≤ 1 := by
  norm_num [squarefreeRadius]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Exact rational comparison includes the denominator 2^2000.
theorem determinant_perturbation_small :
    4320 * (19 : ℝ)^5 * squarefreeRadius < crossGap / 2 := by
  norm_num [squarefreeRadius, crossGap, vandermondeBound]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Exact rational comparison includes the denominator 2^2000.
theorem first_recovery_small :
    firstErrorFactor (inverseBound crossGap) * squarefreeRadius ≤ 1 := by
  norm_num [firstErrorFactor, inverseBound, squarefreeRadius, crossGap,
    vandermondeBound]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Exact rational comparison includes the denominator 2^2000.
theorem total_recovery_lt_raw_gap :
    10^10 * inverseBound crossGap ^ 3 * squarefreeRadius < rawGapScale / 2352 := by
  norm_num [inverseBound, squarefreeRadius, crossGap, vandermondeBound,
    rawGapScale, FiniteGridPole.explicitDelta, Matrix.cons_val]

end
end HeadComplexity.ExplicitCubicGapConstants
