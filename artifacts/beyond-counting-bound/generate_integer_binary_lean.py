"""Generate exact finite Lean data; generation itself proves nothing."""
import json
from pathlib import Path


def vec(xs):
    return '!['+', '.join(map(str,xs))+']'


def mat(xs):
    return '![\n  '+',\n  '.join(vec(x) for x in xs)+']'


def main():
    root=Path(__file__).resolve().parents[2]
    a=Path(__file__).parent
    c=json.loads((a/'integer-binary-fiber-18.json').read_text())
    data=json.loads((a/'integer-binary-fiber-matrices.json').read_text())
    out=root/'formalization/HeadComplexity/Atoms'
    s='''import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

set_option linter.style.header false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Generated data for an eighteen-bit mixed binary evaluation fiber.
The checking theorems are in IntegerBinaryFinite and IntegerBinaryFiber. -/
namespace HeadComplexity.IntegerBinaryFiber
open scoped BigOperators

'''
    s+='def indices : Fin 108 → ℕ := '+vec(c['sample_indices'])+'\n\n'
    s+='def labels : Fin 108 → ℤ := '+vec(c['labels'])+'\n\n'
    s+='def denominatorSlopes : Fin 3 → Fin 18 → ℤ := '+mat(c['denominator_slopes'])+'\n\n'
    s+='def numeratorScaledSlopes : Fin 3 → Fin 18 → ℤ := '+mat(c['numerator_scaled_slopes'])+'\n\n'
    s+='def decodeEntry (row i : ℕ) : ℕ := row / 128^i % 128\n\n'
    for name,rows in [('jacobianMod',data['cleared_jacobian']),('inverseMod',data['inverse_mod_101'])]:
        encoded=[sum((v%101)*128**i for i,v in enumerate(row)) for row in rows]
        s+='def '+name+'Data : Fin 108 → ℕ := '+vec(encoded)+'\n\n'
        s+='def '+name+' : Matrix (Fin 108) (Fin 108) (ZMod 101) :=\n'
        s+='  fun r c ↦ (decodeEntry ('+name+'Data r) c.val : ZMod 101)\n\n'
    s+='end HeadComplexity.IntegerBinaryFiber\n'
    (out/'IntegerBinaryData.lean').write_text(s)
    s=(out/'CoordinateZeroFinite.lean').read_text()
    for x,y in [('CoordinateZeroData','IntegerBinaryData'),('CoordinateZeroFiber','IntegerBinaryFiber'),
                ('sixteen-bit, three-head regular zero','eighteen-bit, three-head mixed binary fiber'),
                ('Fin 96','Fin 108'),('Fin 16','Fin 18'),('2^16','2^18'),('% 16','% 18'),('/ 16','/ 18'),('< 48','< 54')]:
        s=s.replace(x,y)
    start=s.index('theorem cleared_sample_scores_zero')
    end=s.index('/-- Each rational Jacobian row',start)
    s=s[:start]+'''theorem labels_sign : ∀ r, labels r = 1 ∨ labels r = -1 := by decide +kernel

theorem labels_mixed : labels 0 = 1 ∧ labels 53 = -1 := by decide +kernel

theorem labels_exact : ∀ r, labels r = if r.val = 53 then -1 else 1 := by decide +kernel

theorem cleared_sample_scores : ∀ r, clearedScore (indices r) =
    labels r * (3 * den 0 (indices r) * den 1 (indices r) * den 2 (indices r)) := by
  decide +kernel

theorem sample_scores : ∀ r, score (indices r) = labels r := by
  intro r
  have hd : ∀ h : Fin 3, (den h (indices r) : ℚ) ≠ 0 := by
    intro h
    exact_mod_cast ne_of_gt (sample_denominators_positive r h)
  have hz := congrArg (fun z : ℤ => (z : ℚ)) (cleared_sample_scores r)
  simp only [clearedScore, Int.cast_add, Int.cast_mul, Int.cast_ofNat] at hz
  simp only [score, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change 1 + ((num 0 (indices r) : ℚ) / (3 * den 0 (indices r)) +
    ((num 1 (indices r) : ℚ) / (3 * den 1 (indices r)) +
      (num 2 (indices r) : ℚ) / (3 * den 2 (indices r)))) = labels r
  field_simp [hd 0, hd 1, hd 2]
  linear_combination hz


'''+s[end:]
    (out/'IntegerBinaryFinite.lean').write_text(s)
    s=(out/'CoordinateZeroFiber.lean').read_text()
    for x,y in [('CoordinateZeroFinite','IntegerBinaryFinite'),('CoordinateZeroFiber','IntegerBinaryFiber'),
                ('regular coordinate-zero certificate','mixed binary-coordinate certificate'),
                ('Fin 96','Fin 108'),('Fin 16','Fin 18'),('% 16','% 18'),('/ 16','/ 18'),('< 48','< 54')]:
        s=s.replace(x,y)
    start=s.index('def cloneRows')
    end=s.index('theorem clone_samples_have_one',start)
    s=s[:start]+'''def cloneRows : Fin 6 → Fin 108 := '''+vec(data['clone_rows'])+'''
def cloneColumns : Fin 6 → Fin 108 := '''+vec(data['clone_columns'])+'''
def clearedClone : Matrix (Fin 6) (Fin 6) ℤ :=
  clearedJacobian.submatrix cloneRows cloneColumns

def cloneInverseMod : Matrix (Fin 6) (Fin 6) (ZMod 101) := '''+mat(data['clone_inverse_mod_101'])+'\n\n'+s[end:]
    (out/'IntegerBinaryFiber.lean').write_text(s)
    print('Generated IntegerBinaryData, IntegerBinaryFinite, IntegerBinaryFiber. Lean checking required.')


if __name__=='__main__':
    main()
