"""Generate kernel-checkable finite data for the regular coordinate zero.

The generated Lean proofs use `decide`, never `native_decide`.  Generation
does not certify anything; Lean must separately check the matrix identities.
"""
import json
from math import prod
from pathlib import Path


def vec(values):
    return '![' + ', '.join(map(str, values)) + ']'


def mat(rows):
    return '![\n  ' + ',\n  '.join(vec(row) for row in rows) + '\n]'


def inverse(matrix, p):
    n = len(matrix)
    a = [row[:] + [int(i == j) for j in range(n)] for i, row in enumerate(matrix)]
    for k in range(n):
        pivot = next(i for i in range(k, n) if a[i][k])
        a[k], a[pivot] = a[pivot], a[k]
        inv = pow(a[k][k], -1, p)
        a[k] = [v * inv % p for v in a[k]]
        for i in range(n):
            if i != k:
                q = a[i][k]
                a[i] = [(v - q * w) % p for v, w in zip(a[i], a[k])]
    return [row[n:] for row in a]


def main():
    root = Path(__file__).resolve().parents[2]
    cert = json.loads((Path(__file__).parent / 'integer-zero-fiber-16.json').read_text())
    n, h, p = 16, 3, 101
    b, u, vertices = cert['denominator_slopes'], cert['numerator_scaled_slopes'], cert['sample_indices']
    matrix = []
    for v in vertices:
        x = [(v >> i) & 1 for i in range(n)]
        d = [1 + sum(a * z for a, z in zip(row, x)) for row in b]
        a = [sum(t * z for t, z in zip(row, x)) for row in u]
        row = [3 * x[i] * d[j] * prod(d[k] ** 2 for k in range(h) if k != j)
               for j in range(h) for i in range(n)]
        row += [-a[j] * x[i] * prod(d[k] ** 2 for k in range(h) if k != j)
                for j in range(h) for i in range(n)]
        matrix.append([t % p for t in row])
    inv = inverse(matrix, p)
    target = root / 'formalization/HeadComplexity/Atoms/CoordinateZeroData.lean'
    text = '''import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

set_option linter.style.header false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Generated finite data. The checking theorems are in CoordinateZeroFiber. -/
namespace HeadComplexity.CoordinateZeroFiber
open scoped BigOperators

'''
    text += 'def indices : Fin 96 → ℕ := ' + vec(vertices) + '\n\n'
    text += 'def denominatorSlopes : Fin 3 → Fin 16 → ℤ := ' + mat(b) + '\n\n'
    text += 'def numeratorScaledSlopes : Fin 3 → Fin 16 → ℤ := ' + mat(u) + '\n\n'
    text += '''def decodeEntry (row : ℕ) (i : ℕ) : ℕ :=
  row / 128^i % 128

'''
    for name, rows in [('jacobianMod', matrix), ('inverseMod', inv)]:
        encoded = [str(sum(v * 128**i for i, v in enumerate(row))) for row in rows]
        text += 'def ' + name + 'Data : Fin 96 → ℕ := ![\n  '
        text += ',\n  '.join(encoded) + '\n]\n\n'
        text += ('def ' + name + ' : Matrix (Fin 96) (Fin 96) (ZMod 101) :=\n'
                 '  fun r c ↦ (decodeEntry (' + name + 'Data r) c.val : ZMod 101)\n\n')
    text += 'end HeadComplexity.CoordinateZeroFiber\n'
    target.write_text(text)
    print(target)


if __name__ == '__main__':
    main()
