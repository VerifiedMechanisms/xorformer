"""Generate the positive-residue six-test certificate with integer arithmetic."""
from fractions import Fraction
import json
import math
from pathlib import Path

root=Path(__file__).resolve().parent
source=root/'separable-mobius/n3-m6-positive-fiber-exact.json'
record=json.loads(source.read_text())
assert record['patterns']==record['total_patterns']==64
rows=[row for key in ['poles','residuals'] for row in record[key]]
rows += [record['thresholds']]
rows += list(record['witnesses'].values())
scale=math.lcm(*(Fraction(x).denominator for row in rows for x in row))
def integer(x):
    value=Fraction(x)*scale
    assert value.denominator==1
    return str(value.numerator)
def vector(row):return '!['+', '.join(map(integer,row))+']'
def matrix(rows):return '!['+',\n    '.join(map(vector,rows))+']'
template=Path('formalization/HeadComplexity/Atoms/MobiusThreeParameterShattering.lean').read_text()
tail=template[template.index('def labels ('):]
tail=tail.replace('MobiusThreeParameterShattering','PositiveMobiusFiberShattering')
tail=tail.replace('six_tests_shattered','six_positive_tests_shattered')
tail=tail.replace('theorem witnesses_positive',
                  'theorem residues_positive : ∀ q h, 0 < residues q h := by\n  decide +kernel\n\ntheorem witnesses_positive')
tail=tail.replace('Six fixed separable reciprocal tests','Six fixed separable reciprocal tests with strictly positive residues')
text='''import Mathlib.Tactic

set_option linter.style.header false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-! Generated exact rational witnesses from a positive Cauchy permutation fiber.
The theorem concerns a separable reciprocal relaxation, not the head lower bound.
All finite arithmetic is checked by the kernel. -/
namespace HeadComplexity.PositiveMobiusFiberShattering

'''
text+=f'def scale : ℤ := {scale}\n\n'
text+='def poles : Fin 6 → Fin 3 → ℤ :=\n  '+matrix(record['poles'])+'\n\n'
text+='def residues : Fin 6 → Fin 3 → ℤ :=\n  '+matrix(record['residuals'])+'\n\n'
text+='def thresholds : Fin 6 → ℤ := '+vector(record['thresholds'])+'\n\n'
text+='def witness : Fin 64 → Fin 3 → ℤ :=\n  '+matrix([record['witnesses'][str(i)] for i in range(64)])+'\n\n'
text+=tail
target=Path('formalization/HeadComplexity/Atoms/PositiveMobiusFiberShattering.lean')
target.write_text(text)
print(json.dumps({'file':str(target),'scale_digits':len(str(scale)),'bytes':target.stat().st_size}))
