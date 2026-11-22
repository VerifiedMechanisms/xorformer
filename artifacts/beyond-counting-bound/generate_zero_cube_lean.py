"""Generate a batched kernel check of the complete sixteen-bit zero set."""
import json
from pathlib import Path

root = Path(__file__).parent
data = json.loads((root / 'fullcube-active-minimum-checks.json').read_text())
base = json.loads((root / 'integer-zero-fiber-16.json').read_text())
zeros = data['zero_vertices']
extra = [v['vertex'] for v in data['extra_zero_derivatives']]
packed = []
for kind in range(4):
    source = base['denominator_slopes'] if kind < 2 else base['numerator_scaled_slopes']
    offset = 8 * (kind % 2)
    packed.append([])
    for h in range(3):
        values = [128 + sum(source[h][offset+i] * ((j >> i) & 1)
                            for i in range(8)) for j in range(256)]
        assert all(0 <= v < 256 for v in values)
        packed[-1].append(sum(v << (8*j) for j, v in enumerate(values)))
pieces = ['''import HeadComplexity.Atoms.CoordinateZeroCubeSplit

set_option linter.style.header false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

/-! Complete kernel enumeration of the zero set at the sixteen-bit base point.
This certifies finite data, not an asymptotic head-complexity theorem. -/
namespace HeadComplexity.CoordinateZeroFiber

def packedHalves : Fin 4 → Fin 3 → ℕ := ![
''' + ',\n'.join('  ![' + ', '.join(map(str, row)) + ']' for row in packed) + ''']

def halfAt (g : Fin 4) (h : Fin 3) (j : Fin 256) : ℤ :=
  (((packedHalves g h >>> (8 * j.val)) % 256 : ℕ) : ℤ) - 128

theorem half_low_den : ∀ h j,
    halfAt 0 h j = lowDot (denominatorSlopes h) j.val := by
  intro h
  fin_cases h <;> decide +kernel

theorem half_high_den : ∀ h j,
    halfAt 1 h j = highDot (denominatorSlopes h) j.val := by
  intro h
  fin_cases h <;> decide +kernel

theorem half_low_num : ∀ h j,
    halfAt 2 h j = lowDot (numeratorScaledSlopes h) j.val := by
  intro h
  fin_cases h <;> decide +kernel

theorem half_high_num : ∀ h j,
    halfAt 3 h j = highDot (numeratorScaledSlopes h) j.val := by
  intro h
  fin_cases h <;> decide +kernel

def cachedDen (h : Fin 3) (k j : Fin 256) : ℤ :=
  1 + halfAt 0 h j + halfAt 1 h k

def cachedNum (h : Fin 3) (k j : Fin 256) : ℤ :=
  halfAt 2 h j + halfAt 3 h k

theorem cachedDen_eq (h : Fin 3) (k j : Fin 256) :
    cachedDen h k j = den h (256 * k.val + j.val) := by
  rw [den_split]
  simp only [cachedDen, half_low_den, half_high_den]

theorem cachedNum_eq (h : Fin 3) (k j : Fin 256) :
    cachedNum h k j = num h (256 * k.val + j.val) := by
  rw [num_split]
  simp only [cachedNum, half_low_num, half_high_num]

def cachedScore (k j : Fin 256) : ℤ :=
  3 * cachedDen 0 k j * cachedDen 1 k j * cachedDen 2 k j +
    cachedNum 0 k j * cachedDen 1 k j * cachedDen 2 k j +
    cachedNum 1 k j * cachedDen 0 k j * cachedDen 2 k j +
    cachedNum 2 k j * cachedDen 0 k j * cachedDen 1 k j

theorem cachedScore_eq (k j : Fin 256) :
    cachedScore k j = clearedScore (256 * k.val + j.val) := by
  simp only [cachedScore, clearedScore, cachedDen_eq, cachedNum_eq]

def zeroVertexList : List ℕ := [
''' + ', '.join(map(str, zeros)) + ''']

def extraZeroVertices : Finset ℕ := {
''' + ', '.join(map(str, extra)) + '''}

theorem zeroVertexList_length : zeroVertexList.length = 106 := by decide +kernel
theorem zeroVertexList_nodup : zeroVertexList.Nodup := by decide +kernel

theorem zeroVertexList_decomposition :
    zeroVertexList.toFinset = Finset.univ.image indices ∪ extraZeroVertices := by
  decide +kernel

''']
for k in range(256):
    pieces.append(f'''private theorem zero_block_{k} : ∀ j : Fin 256,
    (cachedScore {k} j = 0 ↔
      (256 * {k} + j.val) ∈ zeroVertexList) := by
  decide +kernel

''')
pieces.append('''theorem zero_blocks_correct (k j : Fin 256) :
    (clearedScore (256 * k.val + j.val) = 0 ↔
      (256 * k.val + j.val) ∈ zeroVertexList) := by
  rw [← cachedScore_eq]
  fin_cases k
''')
for k in range(256):
    pieces.append(f'  · exact zero_block_{k} j\n')
pieces.append('''
theorem all_base_zeros (v : Fin 65536) :
    clearedScore v.val = 0 ↔ v.val ∈ zeroVertexList := by
  let k : Fin 256 := ⟨v.val / 256, by omega⟩
  let j : Fin 256 := ⟨v.val % 256, Nat.mod_lt _ (by decide)⟩
  have h := zero_blocks_correct k j
  have he : 256 * k.val + j.val = v.val := by dsimp [k, j]; omega
  simpa only [he] using h

#print axioms all_base_zeros
#print axioms zeroVertexList_decomposition

end HeadComplexity.CoordinateZeroFiber
''')
target = Path('/work/formalization/HeadComplexity/Atoms/CoordinateZeroCube.lean')
target.write_text(''.join(pieces))
print({'file': str(target), 'vertices': 65536, 'blocks': 256})
