#!/usr/bin/env python3
"""Exact rational replays of the general projection and pencil identities."""
from itertools import combinations
from pathlib import Path
import hashlib
import json
import sympy as sp

BASE = Path(__file__).resolve().parent
N, r = 6, 3
A = sp.Matrix([[1,t,t*t] for t in range(1,N+1)])
G = (A.T*A).inv()
P = A*G*A.T
K = sp.eye(N)-P
assert P*P == P and P.T == P
L = sp.diag(*[P[i,i] for i in range(N)])-P.multiply_elementwise(P)
assert L*sp.ones(N,1)==sp.zeros(N,1)
bases = list(combinations(range(N),r))
weights = [A[list(B),:].det()**2 for B in bases]
assert min(weights)>0
probs = [w/sum(weights) for w in weights]
ind = [sp.Matrix([int(i in B) for i in range(N)]) for B in bases]
mean = sum((p*v for p,v in zip(probs,ind)),sp.zeros(N,1))
assert mean == sp.Matrix([P[i,i] for i in range(N)])
cov = sum((p*(v-mean)*(v-mean).T for p,v in zip(probs,ind)),sp.zeros(N,N))
assert cov == L

def normsq(M): return sum(v*v for v in M)

cases=[]
for seed in range(12):
    dA=sp.Matrix(N,r,lambda i,j: ((seed+2)*(i+1)**2+(j+1)*(i+3)+seed*j*j)%17-8)
    X=K*dA*G*A.T+A*G*dA.T*K
    assert X.T==X and P*X+X*P==X and P*X*P==sp.zeros(N,N)
    d=sp.Matrix([X[i,i] for i in range(N)])
    t=sp.Matrix(list(-L[:N-1,:N-1].inv()*d[:N-1,:])+[0])
    assert L*t == -d
    Dt=sp.diag(*t)
    R=(Dt*P+P*Dt)/2-P*Dt*P
    Y=X+R
    assert all(Y[i,i]==0 for i in range(N))
    assert normsq(R)==(t.T*L*t)[0]/2
    assert normsq(Y)==normsq(X)-(t.T*L*t)[0]/2
    for i in range(N):
        Di=sp.diag(*[int(j==i) for j in range(N)])
        Ri=(Di*P+P*Di)/2-P*Di*P
        assert sum(a*b for a,b in zip(Y,Ri))==0
    xi=[2*sp.trace(A[list(B),:].inv()*dA[list(B),:]) for B in bases]
    ex=sum(p*z for p,z in zip(probs,xi))
    residual=[z-ex+((v-mean).T*t)[0] for z,v in zip(xi,ind)]
    var=sum(p*(z-ex)**2 for p,z in zip(probs,xi))
    fi=sum(p*z*z for p,z in zip(probs,residual))
    assert var == 2*normsq(X)
    assert fi == 2*normsq(Y) == var-(t.T*L*t)[0]
    assert sum((p*(v-mean)*z for p,v,z in zip(probs,ind,residual)),sp.zeros(N,1))==sp.zeros(N,1)
    cases.append({'seed':seed,'initial_information':str(var),'quotient_information':str(fi),
                  'removed_information':str((t.T*L*t)[0])})

n,H=4,3
X=[[int((x>>i)&1) for i in range(n)] for x in range(1<<n)]
E=[1+sum(a*b for a,b in zip(x,[1,2,3,4])) for x in X]
F=[2+sum(a*b for a,b in zip(x,[3,1,4,2])) for x in X]
pole_lists=[[-sp.Rational(1,10),1,2],[0,3,5]]
cleared=[]
for ts in pole_lists:
    D=[[e+t*f for t in ts] for e,f in zip(E,F)]
    assert all(d>0 for row in D for d in row)
    C=sp.Matrix([[sp.prod(ds)]+[sp.Rational(x[i],ds[h])*sp.prod(ds)
                              for h in range(H) for i in range(n)] for x,ds in zip(X,D)])
    cleared.append(C)
Kp=sp.Matrix([[a*e**(H-1-j)*f**j for j in range(H) for a in [1]+x]
              for x,e,f in zip(X,E,F)])
rank=Kp.rank()
assert sp.Matrix.hstack(Kp,*cleared).rank()==rank
assert all(C.rank()==rank for C in cleared)

out={'status':'PASS','projection_information_cases':cases,
     'basis_count':len(bases),'pencil_input_bits':n,'pencil_head_count':H,
     'pencil_space_rank':rank,'pole_lists':[[str(t) for t in ts] for ts in pole_lists],
     'scope':'Exact finite replays of written general differential and pencil identities.',
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'main_target_proved':False}
(BASE/'row-scaling-geometry-rational-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','information_cases':len(cases),'pencil_space_rank':rank}))
