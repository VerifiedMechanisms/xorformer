"""Generate exact integer data for the norm-gradient dual certificate."""
from fractions import Fraction as Q
import json
from math import lcm, prod
from pathlib import Path

root = Path(__file__).parent
data = json.loads((root / 'integer-zero-fiber-16.json').read_text())
checks = json.loads((root / 'zero-fiber-dual-checks.json').read_text())
w = []
for v, dual in zip(data['sample_indices'], checks['dual']):
    den = [1 + sum(row[i] * ((v >> i) & 1) for i in range(16))
           for row in data['denominator_slopes']]
    w.append(Q(dual) / prod(d * d for d in den))
common = lcm(*(v.denominator for v in w))
values = [int(v * common) for v in w]
assert all(v for v in values)
target = Path('/work/formalization/HeadComplexity/Atoms/CoordinateZeroDualData.lean')
target.write_text('''import HeadComplexity.Atoms.CoordinateZeroFiber

set_option linter.style.header false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

/-! Generated exact data for the numerator-norm dual vector. -/
namespace HeadComplexity.CoordinateZeroFiber
open scoped BigOperators

def dualDenominator : ℤ := ''' + str(common) + '''

def dualNumerator : Fin 96 → ℤ := ![
''' + ',\n'.join('  ' + str(v) for v in values) + ''']

def normGradientNumerator (c : Fin 96) : ℤ :=
  if c.val < 48 then
    2 * numeratorScaledSlopes
      ⟨c.val / 16 % 3, Nat.mod_lt _ (by decide)⟩
      ⟨c.val % 16, Nat.mod_lt _ (by decide)⟩
  else 0

theorem dualDenominator_pos : 0 < dualDenominator := by decide +kernel

theorem dualNumerator_ne_zero : ∀ r, dualNumerator r ≠ 0 := by decide +kernel

theorem cleared_dual_equation : ∀ c,
    (∑ r, clearedJacobian r c * dualNumerator r) =
      dualDenominator * normGradientNumerator c := by
  intro c
  fin_cases c <;> decide +kernel

theorem positive_dual_numerators :
    (∑ r : Fin 96, if 0 < dualNumerator r then 1 else 0 : ℕ) = 44 := by
  decide +kernel

#print axioms cleared_dual_equation
#print axioms dualNumerator_ne_zero

end HeadComplexity.CoordinateZeroFiber
''')
print({'file': str(target), 'denominator_digits': len(str(common)),
       'max_numerator_digits': max(len(str(abs(v))) for v in values)})
