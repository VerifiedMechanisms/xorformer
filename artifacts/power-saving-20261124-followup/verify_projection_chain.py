"""Exact finite checks only; the arbitrary-n proof is in the accompanying note."""
from itertools import product
import json
import sympy as s

out=[]
for n in range(1,9):
    points=[(0,)+(0,)*n,(0,)+(1,)*n]
    coeffs=[-1,1]
    for i in range(n):
        u=[1]+[int(j<i) for j in range(n)]
        v=u.copy(); v[i+1]-=1
        points += [tuple(u),tuple(v)]
        coeffs += [-1,1]
    incidence=[]
    reciprocal=[]
    for x in product((0,1),repeat=n):
        vals=[p[0]+sum(a*b for a,b in zip(p[1:],x)) for p in points]
        incidence += [[int(a==t) for a in vals] for t in sorted(set(vals))]
        base=2+sum((2+j)*a for j,a in enumerate(x))
        reciprocal.append([s.Rational(1,base+t) for t in vals])
    M=s.Matrix(incidence)
    R=s.Matrix(reciprocal)
    assert M*s.Matrix(coeffs)==s.zeros(M.rows,1)
    assert R*s.Matrix(coeffs)==s.zeros(R.rows,1)
    affine_rank=s.Matrix([[1,*p] for p in points]).rank()-1
    assert len(set(points))==2*n+2
    assert M.rank()==2*n+1
    assert affine_rank==n+1
    out.append(dict(n=n,support=len(points),projection_rank=M.rank(),
                    affine_rank=affine_rank,reciprocal_rank=R.rank()))
print(json.dumps(out,indent=2))
