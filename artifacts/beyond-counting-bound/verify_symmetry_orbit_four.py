#!/usr/bin/env python3
"""Independent exact verifier, with no floating-point optimization or tolerances."""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import hashlib,json,sys
sys.set_int_max_str_digits(0)
from verify_full_table_critical_points import determinant,dot

BASE=Path(__file__).parent
source=BASE/'symmetry-orbit-four-certificate.json'
c=json.loads(source.read_text())
n,k=c['n'],c['group_size'];assert (n,k)==(7,4)
a,b=list(map(F,c['a'])),list(map(F,c['b']))
d0=F(c['denominator_constant']);assert d0>0 and min(b)>0
X=[[(v>>i)&1 for i in range(n)] for v in range(2**n)]
Y=[[F(1)]+list(map(F,x)) for x in X]
D=[d0+dot(b,x) for x in X]
T=[dot(a,y)/d for y,d in zip(Y,D)]
z=list(map(F,c['orbit_mu']))
mu=[z[(v&15).bit_count()+5*(v>>4)] for v in range(128)]
p=2*n+1
J=[[q/d for q in y]+[-t*F(q)/d for q in x] for x,y,d,t in zip(X,Y,D,T)]
assert all(sum((m-t)*row[i] for m,t,row in zip(mu,T,J))==0 for i in range(p))
H=[[F(0) for _ in range(p)] for _ in range(p)]
for x,y,d,t,m,row in zip(X,Y,D,T,mu,J):
    # Half the Hessian of the squared residual, computed by the chain rule.
    for i in range(p):
        for j in range(p):
            if i<n+1 and j<n+1:second=F(0)
            elif i<n+1:second=-y[i]*x[j-n-1]/d**2
            elif j<n+1:second=-x[i-n-1]*y[j]/d**2
            else:second=2*t*x[i-n-1]*x[j-n-1]/d**2
            H[i][j]+=row[i]*row[j]+(t-m)*second
assert H==[[F(v) for v in row] for row in c['half_hessian']]
L=[[F(v) for v in row] for row in c['lower_factor']]
K=[[F(v) for v in row] for row in c['lower_inverse']]
P=list(map(F,c['positive_pivots']))
assert min(P)>0
assert all(sum(K[i][r]*L[r][j] for r in range(p))==int(i==j) for i in range(p) for j in range(p))
assert all(sum(L[i][r]*P[r]*L[j][r] for r in range(p))==H[i][j] for i in range(p) for j in range(p))
tables=[];labels=[];actions=[]
for perm in permutations(range(4)):
    action=[(v&~15)+sum(((v>>perm[i])&1)<<i for i in range(4)) for v in range(128)]
    assert sorted(action)==list(range(128))
    assert [mu[v] for v in action]==mu
    t=[T[v] for v in action]
    assert dot(t,t)==dot(T,T)==dot(mu,t)
    tables.append(tuple(t));labels.append(tuple(v>0 for v in t));actions.append(action)
assert len(set(tables))==24
assert len(set(labels))==4
R=[]
for i,j in c['reconstruction_pairs']:
    v=T[(1<<i)+(1<<j)];row=[F(0)]*n
    row[i]=v-T[1<<i];row[j]=v-T[1<<j];R.append(row)
det=determinant(R)
assert det==F(c['reconstruction_determinant']) and det!=0
assert all(m+100>0 and t+100>0 for m,t in zip(mu,T))
assert sum(t==0 for t in T)==1
report=dict(status='PASS',samples=128,parameters=15,orbit_size=24,
    distinct_positive_supports_before_translation=4,untranslated_has_zero=True,
    positive_translation=100,
    stationarity='exact rational',hessian='exact positive LDL and exact inverse',
    reconstruction_determinant=str(det),squared_table_norm=str(dot(T,T)),
    source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    scope='Finite exact identities only; smooth local-maximum deduction is written separately.',
    main_target_proved=False)
(BASE/'symmetry-orbit-four-rational-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
