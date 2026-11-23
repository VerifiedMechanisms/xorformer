"""Generate kernel arithmetic checks for the approximate inverse and dual."""
import json
import sys
from pathlib import Path

from verify_unit_minimum_contraction import nearest

root=Path(__file__).parent
sys.set_int_max_str_digits(0)
target=root.parents[1]/'formalization/HeadComplexity/Atoms'
d=json.loads((root/'unit-minimum-certificate/data.json').read_text())
D=int(d['denominator']);z=list(map(int,d['center']));m=108
J=[]
for v in d['active_vertices']:
    bits=[i for i in range(18) if (v>>i)&1]
    aa=[sum(z[3*i+h] for i in bits) for h in range(3)]
    bb=[D+sum(z[54+3*i+h] for i in bits) for h in range(3)]
    row=[0]*108
    for i in bits:
        for h in range(3):
            row[3*i+h]=nearest(D*D,bb[h])
            row[54+3*i+h]=nearest(-aa[h]*D*D,bb[h]*bb[h])
    J.append(row)
vec=lambda a:'!['+', '.join(map(str,a))+']'
def pack(a):
    assert all(-(1 << 255) <= int(x) < (1 << 255) for x in a)
    return sum((int(x)+(1 << 255)) << (256*i) for i,x in enumerate(a))
s='''import HeadComplexity.Atoms.UnitMinimumCenterData

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace HeadComplexity.UnitMinimumCenter
open scoped BigOperators
open IntegerBinaryFiber (bit)

'''
s+='def packedInverseRows : Fin 108 → ℕ := '+vec([pack(row) for row in d['inverse']])+'\n\n'
s+='def packedJacobianColumns : Fin 108 → ℕ := '+vec([pack([J[r][c] for r in range(108)]) for c in range(108)])+'\n\n'
s+='''def packedEntry (a : ℕ) (i : Fin 108) : ℤ :=
  (((a >>> (256 * i.val)) % 2^256 : ℕ) : ℤ) - 2^255

def inverseInteger (r c : Fin 108) : ℤ := packedEntry (packedInverseRows r) c

def roundedJacobian (r c : Fin 108) : ℤ := packedEntry (packedJacobianColumns c) r

'''
s+='def dualInteger : Fin 108 → ℤ := '+vec(d['dual'])+'\n\n'
s+='''def columnHead (c : Fin 108) : Fin 3 := ⟨c.val % 3, Nat.mod_lt _ (by decide)⟩

def columnInput (c : Fin 108) : Fin 18 :=
  ⟨(c.val % 54) / 3, by have := Nat.mod_lt c.val (by decide : 0 < 54); omega⟩

def jacobianNumerator (r c : Fin 108) : ℤ :=
  let x := bit (indices r) (columnInput c).val
  if c.val < 54 then x * scale else -x * num (columnHead c) (indices r) * scale

def jacobianDenominator (r c : Fin 108) : ℤ :=
  if c.val < 54 then den (columnHead c) (indices r) else den (columnHead c) (indices r)^2

def gradientInteger (c : Fin 108) : ℤ :=
  if c.val < 54 then u (columnHead c) (columnInput c) else 0

theorem rounded_jacobian_error : ∀ r c : Fin 108,
    0 < jacobianDenominator r c ∧
    2 * |scale * jacobianNumerator r c - roundedJacobian r c * jacobianDenominator r c| ≤
      jacobianDenominator r c := by
  intro r
  fin_cases r <;> decide +kernel

theorem inverse_row_bound : ∀ r : Fin 108,
    (∑ c, |inverseInteger r c|) < 100000 * scale := by
  intro r
  fin_cases r <;> decide +kernel

theorem dual_bounds : ∀ r : Fin 108,
    3 * scale < 1000 * dualInteger r ∧ dualInteger r < 1000000 * scale := by
  decide +kernel

def inverseErrorRow (r : Fin 108) : ℤ :=
  ∑ c : Fin 108, |(if r = c then scale^2 else 0) -
    ∑ k : Fin 108, inverseInteger r k * roundedJacobian k c|

'''
s+='''
theorem dual_residual : ∀ c : Fin 108,
    10^55 * |(∑ r : Fin 108, roundedJacobian r c * labels r * dualInteger r) -
      scale * gradientInteger c| < scale^2 := by
  intro c
  fin_cases c <;> decide +kernel

#print axioms rounded_jacobian_error
#print axioms dual_residual

end HeadComplexity.UnitMinimumCenter
'''
(target/'UnitMinimumJacobianData.lean').write_text(s)
previous='UnitMinimumJacobianData'
for block in range(18):
    name=f'UnitMinimumJacobianBlock{block:02}'
    s=f'''import HeadComplexity.Atoms.{previous}

set_option linter.style.header false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace HeadComplexity.UnitMinimumCenter

'''
    for r in range(6*block,6*block+6):
        s+=f'''theorem inverse_error_{r} : 10^55 * inverseErrorRow {r} < scale^2 := by
  decide +kernel

'''
    s+='end HeadComplexity.UnitMinimumCenter\n'
    (target/(name+'.lean')).write_text(s)
    previous=name
s=f'''import HeadComplexity.Atoms.{previous}

set_option linter.style.header false

namespace HeadComplexity.UnitMinimumCenter

theorem inverse_error_rows (r : Fin 108) : 10^55 * inverseErrorRow r < scale^2 := by
  fin_cases r
'''
for r in range(108):s+=f'  · exact inverse_error_{r}\n'
s+='''
#print axioms rounded_jacobian_error
#print axioms inverse_error_rows
#print axioms dual_residual

end HeadComplexity.UnitMinimumCenter
'''
(target/'UnitMinimumCenterJacobian.lean').write_text(s)
print('Generated packed exact matrix checks in 18 sequentially imported blocks.')
