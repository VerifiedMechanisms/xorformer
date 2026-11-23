"""Generate exact kernel checks for the rational center's entire cube table."""
import json
import sys
from pathlib import Path

sys.set_int_max_str_digits(0)
root = Path(__file__).parent
target = root.parents[1]/'formalization/HeadComplexity/Atoms'
d = json.loads((root/'unit-minimum-certificate/data.json').read_text())
D = int(d['denominator']); z = list(map(int,d['center']))
u = [[z[3*i+h] for i in range(18)] for h in range(3)]
b = [[z[54+3*i+h] for i in range(18)] for h in range(3)]
vec = lambda a: '!['+', '.join(map(str,a))+']'
s = '''import HeadComplexity.Atoms.IntegerUnitCubeSplit

set_option linter.style.header false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace HeadComplexity.UnitMinimumCenter
open scoped BigOperators
open IntegerBinaryFiber (bit dot lowDot highDot dot_split)

'''
s += f'def scale : ℤ := {D}\n\n'
s += 'def u : Fin 3 → Fin 18 → ℤ := '+vec([vec(a) for a in u])+'\n\n'
s += 'def b : Fin 3 → Fin 18 → ℤ := '+vec([vec(a) for a in b])+'\n\n'
s += 'def indices : Fin 108 → ℕ := '+vec(d['active_vertices'])+'\n\n'
s += 'def labels : Fin 108 → ℤ := '+vec(d['active_labels'])+'\n\n'
s += 'def activeList : List ℕ := ['+', '.join(map(str,d['active_vertices']))+']\n\n'
s += '''def den (h : Fin 3) (v : ℕ) : ℤ := scale + dot (b h) v

def num (h : Fin 3) (v : ℕ) : ℤ := dot (u h) v

theorem indices_injective : Function.Injective indices := by decide +kernel

theorem indices_mem : ∀ r, indices r ∈ activeList := by decide +kernel

theorem activeList_mem_iff (v : ℕ) : v ∈ activeList ↔ ∃ r, indices r = v := by
  simp only [activeList, List.mem_cons, List.mem_singleton, indices, Fin.exists_fin_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
  simp [eq_comm]

theorem numerator_bounds : ∀ h i, 2 * |u h i| < scale := by decide +kernel

theorem slope_bounds : ∀ h i, b h i < 0 ∧ 1000 * b h i < -scale := by decide +kernel

theorem denominator_endpoint_bounds : ∀ h, scale < 100 * den h 262143 := by decide +kernel

end HeadComplexity.UnitMinimumCenter

'''
(target/'UnitMinimumCenterData.lean').write_text(s)
packed=[]
for a,offset in [(b,0),(b,9),(u,0),(u,9)]:
    row=[]
    for head in a:
        values=[sum(head[offset+i]*((v>>i)&1) for i in range(9)) for v in range(512)]
        assert all(-(1 << 255) <= v < (1 << 255) for v in values)
        row.append(sum((v+(1 << 255)) << (256*j) for j,v in enumerate(values)))
    packed.append(row)
s = '''import HeadComplexity.Atoms.UnitMinimumCenterData

set_option linter.style.header false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace HeadComplexity.UnitMinimumCenter
open IntegerBinaryFiber (lowDot highDot dot_split)

'''
s += 'def packedHalves : Fin 4 → Fin 3 → ℕ := '+vec([vec(row) for row in packed])+'\n\n'
s += '''def halfAt (g : Fin 4) (h : Fin 3) (j : Fin 512) : ℤ :=
  (((packedHalves g h >>> (256 * j.val)) % 2^256 : ℕ) : ℤ) - 2^255

'''
for g,name,dot,arr in [(0,'low_den','lowDot','b'),(1,'high_den','highDot','b'),(2,'low_num','lowDot','u'),(3,'high_num','highDot','u')]:
    s+=f'''theorem half_{name} : ∀ h j, halfAt {g} h j = {dot} ({arr} h) j.val := by
  intro h
  fin_cases h <;> decide +kernel

'''
s+='''def cachedDen (h : Fin 3) (k j : Fin 512) : ℤ :=
  scale + halfAt 0 h j + halfAt 1 h k

def cachedNum (h : Fin 3) (k j : Fin 512) : ℤ :=
  halfAt 2 h j + halfAt 3 h k

theorem cachedDen_eq (h : Fin 3) (k j : Fin 512) :
    cachedDen h k j = den h (512 * k.val + j.val) := by
  simp only [cachedDen, den, dot_split, half_low_den, half_high_den]
  ring

theorem cachedNum_eq (h : Fin 3) (k j : Fin 512) :
    cachedNum h k j = num h (512 * k.val + j.val) := by
  simp only [cachedNum, num, dot_split, half_low_num, half_high_num]

def cachedP (k j : Fin 512) : ℤ :=
  cachedNum 0 k j * cachedDen 1 k j * cachedDen 2 k j +
  cachedNum 1 k j * cachedDen 0 k j * cachedDen 2 k j +
  cachedNum 2 k j * cachedDen 0 k j * cachedDen 1 k j

def cachedQ (k j : Fin 512) : ℤ :=
  cachedDen 0 k j * cachedDen 1 k j * cachedDen 2 k j

def gapOrSelected (k j : Fin 512) : Prop :=
  cachedQ k j ≤ 100000000 * cachedP k j ∨
  100000000 * (500000000000000000000000 * cachedP k j +
    9493430546062124 * cachedQ k j) ≤ -500000000000000000000000 * cachedQ k j ∨
  512 * k.val + j.val = 0 ∨ 512 * k.val + j.val ∈ activeList

instance (k j : Fin 512) : Decidable (gapOrSelected k j) := by
  unfold gapOrSelected
  infer_instance

'''
# Do not silently substitute an incorrect rational gamma into the source.
from fractions import Fraction
gamma=Fraction(d['gamma'])
s=s.replace('500000000000000000000000',str(gamma.denominator)).replace('9493430546062124',str(gamma.numerator))
for k in range(512):
    s+=f'''private theorem gap_block_{k} : ∀ j : Fin 512, gapOrSelected {k} j := by
  decide +kernel

'''
s+='''theorem cached_gap (k j : Fin 512) : gapOrSelected k j := by
  fin_cases k
'''
for k in range(512):s+=f'  · exact gap_block_{k} j\n'
s+='''
#print axioms cached_gap

end HeadComplexity.UnitMinimumCenter
'''
(target/'UnitMinimumCenterCube.lean').write_text(s)
print('Generated rational-center data and full-cube gap checks.')
