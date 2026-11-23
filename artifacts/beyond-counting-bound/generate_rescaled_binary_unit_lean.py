"""Generate kernel-checkable packed enumeration and a row-replacement certificate."""
import json
from pathlib import Path
root=Path(__file__).parent
lean=root.parents[1]/'formalization/HeadComplexity/Atoms'
d=json.loads((root/'integer-binary-fiber-18.json').read_text())
r=json.loads((root/'rescaled-binary-unit-checks.json').read_text())
split=(lean/'CoordinateZeroCubeSplit.lean').read_text().replace('CoordinateZeroFinite','IntegerBinaryFinite').replace('CoordinateZeroFiber','IntegerBinaryFiber').replace('256','512').replace('8','9').replace('16','18')
(lean/'IntegerUnitCubeSplit.lean').write_text(split)
arrays=[]
for kind,offset in [('denominator_slopes',0),('denominator_slopes',9),('numerator_scaled_slopes',0),('numerator_scaled_slopes',9)]:
    rows=[]
    for h in range(3):
        a=d[kind][h]
        values=[sum(a[offset+i]*((v>>i)&1) for i in range(9)) for v in range(512)]
        assert all(-256<=v<256 for v in values)
        rows.append(sum((v+256)<<(9*j) for j,v in enumerate(values)))
    arrays.append(rows)
s='''import HeadComplexity.Atoms.IntegerUnitCubeSplit

set_option linter.style.header false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

/-! Kernel enumeration of the exact gap below the level one. -/
namespace HeadComplexity.IntegerBinaryFiber
namespace UnitCube

def packedHalves : Fin 4 → Fin 3 → ℕ := ![
'''
s+=',\n'.join('  !['+', '.join(map(str,row))+']' for row in arrays)+']\n\n'
s+='''def halfAt (g : Fin 4) (h : Fin 3) (j : Fin 512) : ℤ :=
  (((packedHalves g h >>> (9 * j.val)) % 512 : ℕ) : ℤ) - 256

'''
for g,name,dot,arr in [(0,'low_den','lowDot','denominatorSlopes'),(1,'high_den','highDot','denominatorSlopes'),(2,'low_num','lowDot','numeratorScaledSlopes'),(3,'high_num','highDot','numeratorScaledSlopes')]:
 s+=f'''theorem half_{name} : ∀ h j, halfAt {g} h j = {dot} ({arr} h) j.val := by
  intro h
  fin_cases h <;> decide +kernel

'''
s+='''def cachedDen (h : Fin 3) (k j : Fin 512) : ℤ :=
  1 + halfAt 0 h j + halfAt 1 h k

def cachedNum (h : Fin 3) (k j : Fin 512) : ℤ :=
  halfAt 2 h j + halfAt 3 h k

theorem cachedDen_eq (h : Fin 3) (k j : Fin 512) :
    cachedDen h k j = den h (512 * k.val + j.val) := by
  rw [den_split]
  simp only [cachedDen, half_low_den, half_high_den]

theorem cachedNum_eq (h : Fin 3) (k j : Fin 512) :
    cachedNum h k j = num h (512 * k.val + j.val) := by
  rw [num_split]
  simp only [cachedNum, half_low_num, half_high_num]

def cachedP (k j : Fin 512) : ℤ :=
  cachedNum 0 k j * cachedDen 1 k j * cachedDen 2 k j +
  cachedNum 1 k j * cachedDen 0 k j * cachedDen 2 k j +
  cachedNum 2 k j * cachedDen 0 k j * cachedDen 1 k j

def cachedD (k j : Fin 512) : ℤ :=
  3 * cachedDen 0 k j * cachedDen 1 k j * cachedDen 2 k j

'''
for k in range(512):
 s+=f'''private theorem gap_block_{k} : ∀ j : Fin 512,
    0 ≤ cachedP {k} j ∨ 34650 * cachedP {k} j ≤ -cachedD {k} j := by
  decide +kernel

'''
s+='''theorem cached_gap (k j : Fin 512) :
    0 ≤ cachedP k j ∨ 34650 * cachedP k j ≤ -cachedD k j := by
  fin_cases k
'''
for k in range(512):s+=f'  · exact gap_block_{k} j\n'
s+='''
end UnitCube
end HeadComplexity.IntegerBinaryFiber
'''
(lean/'IntegerUnitCube.lean').write_text(s)
print('Generated',lean/'IntegerUnitCube.lean')
