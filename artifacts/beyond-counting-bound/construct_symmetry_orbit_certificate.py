#!/usr/bin/env python3
import sys,json
from fractions import Fraction as F
from itertools import permutations,combinations
from pathlib import Path
import numpy as np
from scipy.linalg import qr
from certify_common_normal_maxima import rref,ldl
from verify_full_table_critical_points import inverse,mv,transpose,dot,determinant

def data(n,k,a,b,d0):
    X=[[(x>>i)&1 for i in range(n)] for x in range(2**n)]
    Y=[[1]+x for x in X]
    D=[d0+dot(b,x) for x in X];T=[dot(a,y)/dd for y,dd in zip(Y,D)]
    J=[[F(v)/dd for v in y]+[-tt*F(v)/dd for v in x] for x,y,dd,tt in zip(X,Y,D,T)]
    keys=[(code&((1<<k)-1)).bit_count()+(k+1)*(code>>k) for code in range(2**n)]
    O=[[F(key==other) for other in range((k+1)*2**(n-k))] for key in keys]
    return X,Y,D,T,J,O

def hessian(X,Y,D,T,mu,n):
    p=2*n+1;H=[[F(0) for _ in range(p)] for _ in range(p)]
    for x,y,dd,tt,mm in zip(X,Y,D,T,mu):
        for i in range(n+1):
            for j in range(n+1): H[i][j]+=F(y[i]*y[j])/dd**2
            for j in range(n):
                cc=(mm-2*tt)*y[i]*x[j]/dd**2
                H[i][n+1+j]+=cc;H[n+1+j][i]+=cc
        for i in range(n):
            for j in range(n): H[n+1+i][n+1+j]+=(3*tt**2-2*mm*tt)*x[i]*x[j]/dd**2
    return H

src=Path(sys.argv[1]);dest=Path(sys.argv[2]);c=json.loads(src.read_text().splitlines()[0]);n=c['n'];k=c['group_size'];p=2*n+1
for scale in [1,2,4,8,16,32,100,1000]:
    d0=F(scale); b=[F(round(v*scale)) for v in c['b']]
    if min(b)<=0:continue
    a=[F(round(v*100*scale)) for v in c['a']]
    X,Y,D,T,J,O=data(n,k,a,b,d0)
    eq=[[sum(J[x][i]*O[x][j] for x in range(len(X))) for j in range(len(O[0]))] for i in range(p)]
    rhs=[sum(J[x][i]*T[x] for x in range(len(X))) for i in range(p)]
    eqf=np.array(eq,float);rhsf=np.array(rhs,float)
    zf=np.array(c['orbit_mu'])*100
    rowscale=np.linalg.norm(eqf,axis=1)
    es=eqf/rowscale[:,None];rs=rhsf/rowscale
    zf+=np.linalg.lstsq(es,rs-es@zf,rcond=1e-14)[0]
    muf=np.array(O,float)@zf
    Hf=np.array(hessian(X,Y,D,T,list(map(F,muf)),n),float)
    Z=np.linalg.svd(np.array(J,float),full_matrices=False)
    W=Z[2].T/Z[1][None,:]
    eig=np.linalg.eigvalsh(W.T@Hf@W)
    print('scale',scale,'min whitened eigenvalue',eig[0],flush=True)
    if eig[0]<.005:continue
    _,_,order=qr(es,pivoting=True,mode='economic')
    piv=list(map(int,order[:p]));free=[j for j in range(len(zf)) if j not in piv]
    z=[F(round(float(v)*10**8),10**8) for v in zf]
    mat=[[row[j] for j in piv] for row in eq]
    sol=mv(inverse(mat),[r-sum(row[j]*z[j] for j in free) for row,r in zip(eq,rhs)])
    for j,v in zip(piv,sol):z[j]=v
    assert all(dot(row,z)==r for row,r in zip(eq,rhs))
    mu=mv(O,z);H=hessian(X,Y,D,T,mu,n)
    lo,pp=ldl(H)
    G=[[sum(row[i]*row[j] for row in J) for j in range(p)] for i in range(p)]
    _,gp=ldl(G)
    tables=[];signs=[]
    for perm in permutations(range(k)):
        aa=a[:];bb=b[:]
        for i in range(k):aa[1+i]=a[1+perm[i]];bb[i]=b[perm[i]]
        _,_,_,tt,jj,_=data(n,k,aa,bb,d0)
        assert all(sum((mu[x]-tt[x])*jj[x][i] for x in range(len(X)))==0 for i in range(p))
        assert dot(tt,tt)==dot(T,T)==dot(mu,tt)
        tables.append(tuple(tt));signs.append(tuple(v>0 for v in tt))
    assert len(set(tables))==len(tables)
    # Full table local inverse, fixing the denominator constant d0.
    pairs=list(combinations(range(n),2));pm=[]
    for i,j in pairs:
        vv=T[(1<<i)+(1<<j)]
        row=[F(0)]*n;row[i]=vv-T[1<<i];row[j]=vv-T[1<<j];pm.append(row)
    _,selected=rref(transpose(pm));assert len(selected)==n
    rd=determinant([pm[j] for j in selected]);assert rd
    report=dict(status='EXACT RATIONAL VERIFICATION PASS',n=n,group_size=k,
        denominator_constant=str(d0),a=list(map(str,a)),b=list(map(str,b)),orbit_mu=list(map(str,z)),
        half_hessian=[[str(v) for v in row] for row in H],lower_factor=[[str(v) for v in row] for row in lo],
        lower_inverse=[[str(v) for v in row] for row in inverse(lo)],positive_pivots=list(map(str,pp)),
        gram_positive_pivots=list(map(str,gp)),reconstruction_pairs=[pairs[j] for j in selected],
        reconstruction_determinant=str(rd),distinct_table_count=len(set(tables)),distinct_label_count=len(set(signs)),
        squared_norm=str(dot(T,T)),source=str(src),source_trial=c['trial'],main_target_proved=False)
    dest.write_text(json.dumps(report,indent=2)+'\n')
    print('wrote',dest,'bytes',dest.stat().st_size,flush=True)
    break
else:raise RuntimeError('No exact positive Hessian certificate')
