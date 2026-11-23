#!/usr/bin/env python3
from fractions import Fraction as F
from pathlib import Path
from math import lcm,gcd
from functools import reduce
import sympy as s,json,hashlib
BASE=Path(__file__).resolve().parent
points=[]
for t in range(4,11):
 d=1+t+t*t;points.append((F(t*t-1,d)+2,F(-t*(t+2),d)+2))
inputs=[(0,0),(1,0),(0,1),(1,1)]
labels=[(x,j) for x in range(4) for j in range(4)]
rows=[[(a*inputs[x][0]+b*inputs[x][1])**j for a,b in points] for x,j in labels]
M=s.Matrix(rows);ns=M.nullspace();assert len(ns)==1
c=list(ns[0]);den=lcm(*[int(v.q) for v in c]);c=[int(v*den) for v in c];g=reduce(gcd,c);c=[v//g for v in c]
assert all(c) and len(set(c))==7
assert all(a>0 and b>0 and (a-2)**2+(a-2)*(b-2)+(b-2)**2==1 for a,b in points)
assert all(len({a*x+b*y for a,b in points})==7 for x,y in inputs[1:])
selected6=list(M[:,:6].T.rref()[1]);assert len(selected6)==6
minor6=M[selected6,:6];inv6=minor6.inv();assert inv6*minor6==s.eye(6)
labels5=[(x,j) for x in range(4) for j in range(5)]
rows5=[[(a*inputs[x][0]+b*inputs[x][1])**j for a,b in points] for x,j in labels5]
M5=s.Matrix(rows5);selected7=list(M5.T.rref()[1]);assert len(selected7)==7
minor7=M5[selected7,:];inv7=minor7.inv();assert inv7*minor7==s.eye(7)
fourth=[sum(v*(a*x+b*y)**4 for (a,b),v in zip(points,c)) for x,y in inputs]
assert fourth==[0,F(90613464360,1405678729),F(15464511960,1405678729),F(-106077976320,1405678729)]
result={'status':'PASS','velocities':[[str(v) for v in p] for p in points],'residues':c,
        'rows6':[labels[i] for i in selected6],'inverse6':[[str(x) for x in inv6.row(i)] for i in range(6)],
        'rows7':[labels5[i] for i in selected7],'inverse7':[[str(x) for x in inv7.row(i)] for i in range(7)],
        'fourth_moments':[str(x) for x in fourth],'moment_rank_three':6,'moment_rank_four':7,
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope':'Exact finite certificate. General harmonic theorem is a written proof. No Boolean lower bound.',
        'main_target_proved':False}
(BASE/'ellipse-moment-circuits-rational-audit.json').write_text(json.dumps(result,indent=2)+'\n')

def rat(v):
 v=s.Rational(v)
 return str(v.p) if v.q==1 else '('+str(v.p)+' / '+str(v.q)+')'
def vec(xs):return '!['+', '.join(xs)+']'
def mat(a):return vec([vec([rat(x) for x in a.row(i)]) for i in range(a.rows)])
source='''import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Exact seven-point ellipse certificate. The general harmonic and existence
arguments remain complete written proofs, not declarations in this file. -/
namespace HeadComplexity.EllipseMomentCircuits

'''
source+='def velocity : Fin 7 → Fin 2 → ℚ := '+vec([vec([rat(x) for x in p]) for p in points])+'\n'
source+='def residue : Fin 7 → ℚ := '+vec([str(v) for v in c])+'\n'
source+='def input : Fin 4 → Fin 2 → ℚ := '+vec([vec([str(v) for v in p]) for p in inputs])+'\n'
source+='def projection (h : Fin 7) (x : Fin 4) : ℚ := ∑ i, velocity h i * input x i\n'
source+='def moment (x : Fin 4) (j : ℕ) : ℚ := ∑ h, residue h * projection h x ^ j\n'
source+='def rows6 : Fin 6 → Fin 4 × Fin 4 := '+vec(['('+str(labels[i][0])+', '+str(labels[i][1])+')' for i in selected6])+'\n'
source+='def minor6 : Matrix (Fin 6) (Fin 6) ℚ := fun i j => projection j.castSucc (rows6 i).1 ^ (rows6 i).2.val\n'
source+='def inverse6 : Matrix (Fin 6) (Fin 6) ℚ := '+mat(inv6)+'\n'
source+='def rows7 : Fin 7 → Fin 4 × Fin 5 := '+vec(['('+str(labels5[i][0])+', '+str(labels5[i][1])+')' for i in selected7])+'\n'
source+='def minor7 : Matrix (Fin 7) (Fin 7) ℚ := fun i j => projection j (rows7 i).1 ^ (rows7 i).2.val\n'
source+='def inverse7 : Matrix (Fin 7) (Fin 7) ℚ := '+mat(inv7)+'\n\n'
source+='theorem velocities_positive : ∀ h i, 0 < velocity h i := by decide +kernel\n'
source+='theorem on_ellipse : ∀ h, (velocity h 0 - 2)^2 + (velocity h 0 - 2)*(velocity h 1 - 2) + (velocity h 1 - 2)^2 = 1 := by decide +kernel\n'
source+='theorem residues_nonzero : ∀ h, residue h ≠ 0 := by decide +kernel\n'
source+='theorem residues_distinct : Function.Injective residue := by decide +kernel\n'
source+='theorem projections_distinct : ∀ x, x ≠ 0 → Function.Injective (fun h => projection h x) := by decide +kernel\n'
source+='theorem moments_zero : ∀ x (j : Fin 4), moment x j.val = 0 := by decide +kernel\n'
source+='theorem fourth_moments : (fun x => moment x 4) = '+vec([rat(x) for x in fourth])+' := by decide +kernel\n'
source+='theorem inverse6_mul : inverse6 * minor6 = 1 := by decide +kernel\n'
source+='theorem inverse7_mul : inverse7 * minor7 = 1 := by decide +kernel\n'
source+='''
theorem coherent_slopes_positive (ε : ℝ) (hε : 0 ≤ ε) (h : Fin 7) (i : Fin 2) :
    0 < 1 + ε * (velocity h i : ℝ) := by
  have hv : 0 < (velocity h i : ℝ) := by exact_mod_cast velocities_positive h i
  positivity

end HeadComplexity.EllipseMomentCircuits
'''
Path('formalization/HeadComplexity/Atoms/EllipseMomentCircuits.lean').write_text(source)
print(json.dumps({k:result[k] for k in ['status','rows6','rows7','fourth_moments','moment_rank_three','moment_rank_four']},indent=2))
