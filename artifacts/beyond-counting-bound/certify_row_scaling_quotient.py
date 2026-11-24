#!/usr/bin/env python3
"""Construct an exact three-head quotient-tangent rank certificate."""
from pathlib import Path
from itertools import product
import json
import hashlib
import sympy as sp
import numpy as np

BASE = Path(__file__).resolve().parent
p, n, H, N, r = 101, 4, 3, 16, 13

def inv(M):
    M = [list(map(lambda v:int(v)%p, row)) for row in M]
    d = len(M)
    B = [row+[int(i==j) for j in range(d)] for i,row in enumerate(M)]
    for j in range(d):
        k = next((i for i in range(j,d) if B[i][j]), None)
        if k is None: raise ValueError('singular')
        B[j], B[k] = B[k], B[j]
        z = pow(B[j][j], -1, p)
        B[j] = [(v*z)%p for v in B[j]]
        for i in range(d):
            if i != j:
                z = B[i][j]
                B[i] = [(v-z*w)%p for v,w in zip(B[i],B[j])]
    return [row[d:] for row in B]

def pivots(M):
    B = [[int(v)%p for v in row] for row in M]
    d, m, row = len(B), len(B[0]), 0
    out = []
    for j in range(m):
        k = next((i for i in range(row,d) if B[i][j]), None)
        if k is None: continue
        B[row], B[k] = B[k], B[row]
        z = pow(B[row][j], -1, p)
        B[row] = [(v*z)%p for v in B[row]]
        for i in range(d):
            if i != row:
                z = B[i][j]
                B[i] = [(v-z*w)%p for v,w in zip(B[i],B[row])]
        out.append(j); row += 1
        if row == d: break
    return out

def red(v):
    v = sp.Rational(v)
    return int(v.p)%p * pow(int(v.q)%p, -1, p)%p

rng = np.random.default_rng(749002)
X = [[(x >> j)&1 for j in range(n)] for x in range(N)]
for trial in range(100):
    bs = rng.integers(1,21,size=(H,n)).tolist()
    D = [[1+sum(a*b for a,b in zip(x,bh)) for bh in bs] for x in X]
    A = sp.Matrix([[1]+[sp.Rational(x[i],D[xx][h]) for h in range(H) for i in range(n)]
                   for xx,x in enumerate(X)])
    Am = np.array(A.applyfunc(red)).astype(np.int64)
    B = pivots(Am.T.tolist())
    if len(B)!=r: continue
    E = [x for x in range(N) if x not in B]
    T = sp.zeros(N-r,N)
    TB = -A[E,:]*A[B,:].inv()
    for i,e in enumerate(E):
        T[i,e]=1
        for j,b in enumerate(B): T[i,b]=TB[i,j]
    assert T*A==sp.zeros(N-r,r)
    Tm = np.array(T.applyfunc(red)).astype(np.int64)
    cs = []
    for x in range(N-1):
        cs.append(T[:,x]*A[x,:])
    for h in range(H):
        for j in range(n):
            dA=sp.zeros(N,r)
            for x in range(N):
                for i in range(n):
                    dA[x,1+h*n+i]=-sp.Rational(X[x][i]*X[x][j],D[x][h]**2)
            cs.append(T*dA)
    C=sp.Matrix.hstack(*[sp.Matrix(list(m)) for m in cs])
    Cm=np.array(C.applyfunc(red)).astype(np.int64)
    rows=pivots(Cm.T.tolist())
    if len(rows)!=N-1+n*H: continue
    M=Cm[rows,:]
    MI=inv(M.tolist())
    assert np.array_equal(np.array(MI)@M%p,np.eye(len(rows),dtype=np.int64))
    break
else: raise RuntimeError('No certificate')

def vec(v): return '!['+', '.join(map(str,v))+']'
def mat(m): return vec([vec(row) for row in m])

source='''import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

/-! Finite certificate for independent denominator directions modulo row scaling.
The rational lift and differential interpretation are in the companion note. -/
set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace HeadComplexity.RowScalingQuotient
instance : Fact (Nat.Prime 101) := ⟨by decide⟩
local instance : DecidableEq (ZMod 101) := ZMod.decidableEq 101
'''
source+=f'def slopes : Fin 3 → Fin 4 → ℕ := {mat(bs)}\n'
source+='def bit (x : Fin 16) (i : ℕ) : ℕ := if x.val.testBit i then 1 else 0\n'
source+='def denNat (x : Fin 16) (h : Fin 3) : ℕ := 1 + ∑ i : Fin 4, slopes h i * bit x i.val\n'
source+='def den (x : Fin 16) (h : Fin 3) : ZMod 101 := denNat x h\n'
source+=f'def denInverse : Matrix (Fin 16) (Fin 3) (ZMod 101) := {mat([[pow(v,-1,p) for v in row] for row in D])}\n'
source+=f'def evaluation : Matrix (Fin 16) (Fin 13) (ZMod 101) := {mat(Am.tolist())}\n'
source+=f'def baseRows : Fin 13 → Fin 16 := {vec(B)}\n'
source+=f'def extraRows : Fin 3 → Fin 16 := {vec(E)}\n'
source+=f'def baseInverse : Matrix (Fin 13) (Fin 13) (ZMod 101) := {mat(inv(Am[B,:].tolist()))}\n'
source+=f'def normal : Matrix (Fin 3) (Fin 16) (ZMod 101) := {mat(Tm.tolist())}\n'
source+=f'def selectedRows : Fin 27 → Fin 39 := {vec(rows)}\n'
source+=f'def selected : Matrix (Fin 27) (Fin 27) (ZMod 101) := {mat(M.tolist())}\n'
source+=f'def selectedInverse : Matrix (Fin 27) (Fin 27) (ZMod 101) := {mat(MI)}\n'
source+='''
def headColumn (h : Fin 3) (i : Fin 4) : Fin 13 := ⟨1+4*h.val+i.val, by omega⟩
def derivative (h : Fin 3) (j : Fin 4) (x : Fin 16) (c : Fin 13) : ZMod 101 :=
  - ∑ i : Fin 4, if c = headColumn h i then
      (bit x i.val : ZMod 101) * bit x j.val * denInverse x h ^ 2 else 0

def coefficient (a : Fin 39) (q : Fin 27) : ZMod 101 :=
  let l : Fin 3 := ⟨a.val / 13, by omega⟩
  let c : Fin 13 := ⟨a.val % 13, Nat.mod_lt _ (by decide)⟩
  if hq : q.val < 15 then
    let x : Fin 16 := ⟨q.val, by omega⟩
    normal l x * evaluation x c
  else
    let h : Fin 3 := ⟨(q.val-15)/4, by omega⟩
    let j : Fin 4 := ⟨(q.val-15)%4, Nat.mod_lt _ (by decide)⟩
    ∑ x : Fin 16, normal l x * derivative h j x c

theorem denominators_positive : ∀ x h, 0 < denNat x h ∧ denNat x h < 101 := by decide +kernel
local instance : DecidableRel (fun x h => denInverse x h = (den x h)⁻¹) :=
  fun x h => ZMod.decidableEq 101 (denInverse x h) ((den x h)⁻¹)
theorem denominator_inverse : ∀ x h, denInverse x h = (den x h)⁻¹ := by decide +kernel
theorem evaluation_origin : ∀ x, evaluation x 0 = 1 := by decide +kernel
theorem evaluation_heads : ∀ x h i,
    evaluation x (headColumn h i) = (bit x i.val : ZMod 101) / den x h := by decide +kernel
theorem base_inverse_mul : baseInverse * evaluation.submatrix baseRows id = 1 := by decide +kernel
theorem normal_annihilates : normal * evaluation = 0 := by decide +kernel
theorem normal_extra_identity : normal.submatrix id extraRows = 1 := by decide +kernel
local instance : DecidableRel (fun a q : Fin 27 => selected a q = coefficient (selectedRows a) q) :=
  fun a q => ZMod.decidableEq 101 (selected a q) (coefficient (selectedRows a) q)
theorem selected_formula : ∀ a q, selected a q = coefficient (selectedRows a) q := by
  decide +kernel
theorem selected_inverse_mul : selectedInverse * selected = 1 := by decide +kernel

end HeadComplexity.RowScalingQuotient
'''
lean=Path('/work/formalization/HeadComplexity/Atoms/RowScalingQuotient.lean')
lean.write_text(source)
audit='import HeadComplexity.Atoms.RowScalingQuotient\n\n'
names=['denominators_positive','denominator_inverse','evaluation_origin','evaluation_heads','base_inverse_mul',
       'normal_annihilates','normal_extra_identity','selected_formula','selected_inverse_mul']
audit+='\n'.join('#print axioms HeadComplexity.RowScalingQuotient.'+s for s in names)+'\n'
(BASE/'AuditRowScalingQuotient.lean').write_text(audit)
data={'status':'PASS','field':p,'slopes':bs,'base_rows':B,'extra_rows':E,
      'selected_rows':rows,'normal_mod':Tm.tolist(),'selected_mod':M.tolist(),
      'selected_inverse_mod':MI,'quotient_dimension':n*H,
      'scope':'Exact rational formulas reduced mod 101. Nonzero minors certify full denominator variation modulo all row scalings. No head lower bound.',
      'source_sha256':hashlib.sha256(lean.read_bytes()).hexdigest(),
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'main_target_proved':False}
(BASE/'row-scaling-quotient-certificate.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({'status':'PASS','slopes':bs,'selected_minor':len(rows),'quotient_dimension':n*H}))
